import Holonics.HNN.Keys

/-!
# The diagonal board's survivors are the fibre of its fundamental cycles

`Holonics/HNN/Keys` proves that over a traversal-ordered edge list the Bombe's diagonal board `propagate` returns
`some f` exactly when `f` is an injective, edge-consistent assignment on the component's ports
(`propagation_eq_edge_fibre`), and that a survivor closes every walk of the menu (`survivor_closes_walks`). Its `[open]`
paragraph leaves the converse: that the survivors are exactly the fibre of the component's fundamental-cycle menu. This
file proves it. Sources: the record of October 5 on located keys
(`research/records/2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md`, §8 item 1) and #410's box
"Survivors are the cycle fibre"; atlas `hnn.propagation-edge-fibre`.

[proved-derived; formal-checked] What is proved.

1. **The traversal tree** (`treeChain`, `treeChain_seed`, `treeChain_chain`, `treeChain_isSome_iff`,
   `treeChain_prefix`): reading the edge list in its order and keeping, for each port, the first walk that reached it
   gives a spanning tree of the component. Each port's tree walk is a chain of menu edges from the seed to it, a port
   has one exactly when it is visited (the list traversal ordered), and the tree is closed under prefixes: an edge on a
   tree walk joins its source's tree walk to its target's (`IsTreeEdge`).
2. **A survivor is the tree's reading** (`survivor_eq_treeReading`): a consistent assignment sends each port to the
   seed image carried along the port's tree walk, `f q = T_(tree q)(s₀)`; so a survivor's image does not depend on the
   walk that reads it (`survivor_path_independent`).
3. **The survivors are the cycle fibre** (`propagate_eq_some_iff`, `survives_iff_cycles_close`,
   `survives_iff_fundamental`): propagation from `(k, s₀)` survives exactly when every edge's cycle closes,
   `W_e(T_(tree src)(s₀)) = T_(tree dst)(s₀)`, and the tree's readings are injective; the survivor is then the tree's
   reading. An edge on the tree closes its own cycle at every candidate (`treeEdge_cycleCloses`), so only the
   fundamental cycles, those of the edges off the tree, decide.
4. **As loops of the Bombe** (`cycleLoop`, `cycleMenu`, `cycleLoop_closes_iff`, `holds_iff_tree_and_cycles`,
   `holds_iff_tree_and_fundamental`, `plugboard_survives_iff`, `survivors_eq_cycle_fibre`): each edge's fundamental
   cycle is a `Compression/Core/Keys` loop at the seed, out along the source's tree walk, across the edge, back along
   the target's tree walk inverted. A full plugboard satisfies every edge exactly when it satisfies the tree's edges and
   closes every fundamental loop; when it fits the tree, propagation from its seed image survives exactly when it closes
   every loop. Over a truth that fits every edge, the candidates that survive propagation are the loop-closure fibre of
   the fundamental-cycle menu cut by the tree's injectivity, the diagonal board's plugboard condition.

The computational object is the helical pair interaction read on a menu of pair contacts: each edge is a contact
whose stage is the ring's transport at the key, and a cycle closes when the transport around it fixes the image. Of
the winding guide's six general objects this touches the pair (the edges), faces and placement (the images the board
assigns) and the cell holonomy (a cycle's closure is its holonomy at the key); the helix, the tube and the tower
thread stay attached.

Consumers: the atlas row `hnn.propagation-edge-fibre` and `HNN/Keys`' `[open]` paragraph, which this answers.

What stands beside it: the turn menu's fibre (`HNN/TurnMenuFibre`), whose cycles are these loops with the rotor's turn
as their stage; the cycle space of a graph has the fundamental cycles of any spanning tree as a basis, which is
why closing them suffices; the board's injectivity is a separate condition the cycles do not see, and stays a
hypothesis of its own (`TreeInjective`); key location for continuous keys stays with #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.SurvivorsCycleFibre

open Holonics.HNN.Keys
open Holonics.Compression.Core.Keys

section Walks

variable {Key α : Type*}

/-- [definition] **A walk's transport at a key**: its stage word, last edge first, as one permutation (the word
`walk_transports` and `survivor_closes_walks` carry an image by). -/
def transport (k : Key) (ws : List (MenuEdge Key α)) : Equiv.Perm α :=
  (ws.map fun e : MenuEdge Key α => e.stage k).reverse.prod

/-- [proved-derived; formal-checked] The empty walk transports by the identity. -/
@[simp] theorem transport_nil (k : Key) : transport k ([] : List (MenuEdge Key α)) = 1 := rfl

/-- [proved-derived; formal-checked] One more edge composes its stage after the walk's transport. -/
theorem transport_append_one (k : Key) (ws : List (MenuEdge Key α)) (e : MenuEdge Key α) :
    transport k (ws ++ [e]) = e.stage k * transport k ws := by
  simp [transport]

/-- [proved-derived; formal-checked] The walk read backwards, each stage inverted, transports by the inverse. -/
theorem prod_map_inv_eq_inv_transport (k : Key) (ws : List (MenuEdge Key α)) :
    (ws.map fun e : MenuEdge Key α => (e.stage k)⁻¹).prod = (transport k ws)⁻¹ := by
  rw [transport, List.prod_inv_reverse, List.map_reverse, List.reverse_reverse, List.map_map]
  rfl

/-- [proved-derived; formal-checked] A chain with one more edge: the shorter chain ends at the edge's source. -/
theorem chain_append_one {p q : α} {ws : List (MenuEdge Key α)} {e : MenuEdge Key α} :
    Chain p (ws ++ [e]) q ↔ Chain p ws e.src ∧ e.dst = q := by
  induction ws generalizing p with
  | nil =>
      simp only [List.nil_append, Chain]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2⟩
  | cons e' ws ih => simp only [List.cons_append, Chain, ih, and_assoc]

end Walks

section Tree

variable {Key α : Type*} [DecidableEq α]

/-- [definition] **One step of the traversal tree**: an edge whose target has no tree walk gives it the source's tree
walk followed by the edge (none, when the source has none either); a reached target keeps its walk. -/
def treeStep (t : α → Option (List (MenuEdge Key α))) (e : MenuEdge Key α) :
    α → Option (List (MenuEdge Key α)) :=
  match t e.dst with
  | some _ => t
  | none => Function.update t e.dst ((t e.src).map fun ws => ws ++ [e])

/-- [definition] **The traversal tree**: each port's first walk from the seed, read along the edge list. -/
def treeChain (p₀ : α) (es : List (MenuEdge Key α)) : α → Option (List (MenuEdge Key α)) :=
  es.foldl treeStep (Function.update (fun _ => none) p₀ (some []))

/-- [definition] **A tree edge**: one that lies on some port's tree walk. -/
def IsTreeEdge (p₀ : α) (es : List (MenuEdge Key α)) (e : MenuEdge Key α) : Prop :=
  ∃ q ws, treeChain p₀ es q = some ws ∧ e ∈ ws

/-- [proved-derived; formal-checked] A reached target keeps its tree walk. -/
theorem treeStep_of_some {t : α → Option (List (MenuEdge Key α))} {e : MenuEdge Key α} {ws}
    (h : t e.dst = some ws) : treeStep t e = t := by
  simp [treeStep, h]

/-- [proved-derived; formal-checked] An unreached target takes the source's tree walk followed by the edge. -/
theorem treeStep_of_none {t : α → Option (List (MenuEdge Key α))} {e : MenuEdge Key α}
    (h : t e.dst = none) :
    treeStep t e = Function.update t e.dst ((t e.src).map fun ws => ws ++ [e]) := by
  simp [treeStep, h]

/-- [proved-derived; formal-checked] A tree walk once read is kept by a step. -/
theorem treeStep_persist {t : α → Option (List (MenuEdge Key α))} {e : MenuEdge Key α} {q : α} {ws}
    (h : t q = some ws) : treeStep t e q = some ws := by
  cases hd : t e.dst with
  | some w => rw [treeStep_of_some hd]; exact h
  | none =>
      rw [treeStep_of_none hd]
      have hq : q ≠ e.dst := by rintro rfl; rw [h] at hd; cases hd
      rw [Function.update_of_ne hq]; exact h

/-- [proved-derived; formal-checked] A tree walk once read is kept by every later step. -/
theorem foldl_treeStep_persist {q : α} {ws} :
    ∀ (es : List (MenuEdge Key α)) (t : α → Option (List (MenuEdge Key α))), t q = some ws →
      es.foldl treeStep t q = some ws
  | [], _, h => h
  | _ :: es, _, h => foldl_treeStep_persist es _ (treeStep_persist h)

/-- [proved-derived; formal-checked] One more edge is one more step of the tree. -/
theorem treeChain_append_one (p₀ : α) (es : List (MenuEdge Key α)) (e : MenuEdge Key α) :
    treeChain p₀ (es ++ [e]) = treeStep (treeChain p₀ es) e := by
  simp [treeChain, List.foldl_append]

/-- [proved-derived; formal-checked] A tree walk read from a prefix of the list stands on the whole list. -/
theorem treeChain_persist {p₀ q : α} {es : List (MenuEdge Key α)} {ws} (es' : List (MenuEdge Key α))
    (h : treeChain p₀ es q = some ws) : treeChain p₀ (es ++ es') q = some ws := by
  rw [treeChain, List.foldl_append]
  exact foldl_treeStep_persist es' _ h

/-- [proved-derived; formal-checked] The seed's tree walk is empty. -/
theorem treeChain_seed (p₀ : α) (es : List (MenuEdge Key α)) : treeChain p₀ es p₀ = some [] :=
  foldl_treeStep_persist es _ (by simp)

/-- [proved-derived; formal-checked] **A tree walk is a walk of the menu**: a chain of the list's edges from the seed
to its port. -/
theorem treeChain_chain (p₀ : α) :
    ∀ (es : List (MenuEdge Key α)) {q : α} {ws}, treeChain p₀ es q = some ws →
      Chain p₀ ws q ∧ ∀ e ∈ ws, e ∈ es := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
      intro q ws h
      by_cases hq : q = p₀
      · subst hq
        simp only [treeChain, List.foldl_nil, Function.update_self, Option.some.injEq] at h
        subst h
        exact ⟨rfl, by simp⟩
      · simp [treeChain, Function.update_of_ne hq] at h
  | append_singleton es e ih =>
      intro q ws h
      rw [treeChain_append_one] at h
      have hsub : ∀ e' ∈ es, e' ∈ es ++ [e] := fun e' he' => List.mem_append_left _ he'
      cases hd : treeChain p₀ es e.dst with
      | some w =>
          rw [treeStep_of_some hd] at h
          obtain ⟨hc, hm⟩ := ih h
          exact ⟨hc, fun e' he' => hsub e' (hm e' he')⟩
      | none =>
          rw [treeStep_of_none hd] at h
          by_cases hq : q = e.dst
          · subst hq
            rw [Function.update_self] at h
            obtain ⟨ws₀, hs, rfl⟩ := Option.map_eq_some_iff.mp h
            obtain ⟨hc, hm⟩ := ih hs
            refine ⟨chain_append_one.mpr ⟨hc, rfl⟩, fun e' he' => ?_⟩
            rcases List.mem_append.mp he' with he' | he'
            · exact hsub e' (hm e' he')
            · rw [List.mem_singleton.mp he']; exact List.mem_append_right _ (List.mem_singleton_self e)
          · rw [Function.update_of_ne hq] at h
            obtain ⟨hc, hm⟩ := ih h
            exact ⟨hc, fun e' he' => hsub e' (hm e' he')⟩

/-- [proved-derived; formal-checked] **The tree spans the component**: over a traversal-ordered list a port has a tree
walk exactly when the seed or an edge visits it. -/
theorem treeChain_isSome_iff (p₀ : α) :
    ∀ (es : List (MenuEdge Key α)), TraversalOrdered p₀ es → ∀ q,
      (treeChain p₀ es q).isSome ↔ InPorts p₀ es q := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
      intro _ q
      by_cases hq : q = p₀
      · subst hq; simp [treeChain, InPorts]
      · simp [treeChain, InPorts, hq]
  | append_singleton es e ih =>
      intro hord q
      obtain ⟨hord', hsrc⟩ := hord.of_append
      have ih' := ih hord'
      rw [treeChain_append_one, inPorts_append_one]
      cases hd : treeChain p₀ es e.dst with
      | some w =>
          rw [treeStep_of_some hd, ih' q]
          constructor
          · exact Or.inl
          · rintro (h | rfl | rfl)
            · exact h
            · exact hsrc
            · exact (ih' _).mp (by rw [hd]; rfl)
      | none =>
          rw [treeStep_of_none hd]
          by_cases hq : q = e.dst
          · subst hq
            rw [Function.update_self]
            obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((ih' e.src).mpr hsrc)
            simp [hw]
          · rw [Function.update_of_ne hq, ih' q]
            constructor
            · exact Or.inl
            · rintro (h | rfl | h)
              · exact h
              · exact hsrc
              · exact absurd h hq

/-- [proved-derived; formal-checked] **The tree is closed under prefixes**: an edge on a tree walk joins its source's
tree walk to its target's, the target's walk being the source's followed by the edge. -/
theorem treeChain_prefix (p₀ : α) :
    ∀ (es : List (MenuEdge Key α)) {q : α} {ws pre suf} {e : MenuEdge Key α},
      treeChain p₀ es q = some ws → ws = pre ++ e :: suf →
        treeChain p₀ es e.src = some pre ∧ treeChain p₀ es e.dst = some (pre ++ [e]) := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
      intro q ws pre suf e h hws
      by_cases hq : q = p₀
      · subst hq
        simp only [treeChain, List.foldl_nil, Function.update_self, Option.some.injEq] at h
        subst h
        exact absurd hws.symm (by simp)
      · simp [treeChain, Function.update_of_ne hq] at h
  | append_singleton es e₀ ih =>
      intro q ws pre suf e h hws
      have hp : ∀ {r : α} {w}, treeChain p₀ es r = some w → treeChain p₀ (es ++ [e₀]) r = some w :=
        fun hr => treeChain_persist [e₀] hr
      rw [treeChain_append_one] at h
      cases hd : treeChain p₀ es e₀.dst with
      | some w =>
          rw [treeStep_of_some hd] at h
          obtain ⟨h1, h2⟩ := ih h hws
          exact ⟨hp h1, hp h2⟩
      | none =>
          rw [treeStep_of_none hd] at h
          by_cases hq : q = e₀.dst
          · subst hq
            rw [Function.update_self] at h
            obtain ⟨ws₀, hs, rfl⟩ := Option.map_eq_some_iff.mp h
            rcases List.eq_nil_or_concat' suf with rfl | ⟨suf', x, rfl⟩
            · obtain ⟨rfl, he⟩ := List.append_inj' hws rfl
              obtain rfl : e₀ = e := by simpa using he
              refine ⟨hp hs, ?_⟩
              rw [treeChain_append_one, treeStep_of_none hd, Function.update_self, hs]
              rfl
            · have hws' : ws₀ ++ [e₀] = (pre ++ e :: suf') ++ [x] := by rw [hws]; simp
              obtain ⟨hws₀, -⟩ := List.append_inj' hws' rfl
              obtain ⟨h1, h2⟩ := ih hs hws₀
              exact ⟨hp h1, hp h2⟩
          · rw [Function.update_of_ne hq] at h
            obtain ⟨h1, h2⟩ := ih h hws
            exact ⟨hp h1, hp h2⟩

/-- [definition] **The tree's reading** at `(k, s₀)`: each port's image, the seed image carried along its tree walk. -/
def treeReading (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α)) (q : α) : Option α :=
  (treeChain p₀ es q).map fun ws => transport k ws s₀

/-- [definition] **An edge's cycle closes** at `(k, s₀)`: the stage carries the tree's reading at its source to the
tree's reading at its target (vacuous where an endpoint has no tree walk). -/
def CycleCloses (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α)) (e : MenuEdge Key α) : Prop :=
  ∀ ws₁ ws₂, treeChain p₀ es e.src = some ws₁ → treeChain p₀ es e.dst = some ws₂ →
    e.stage k (transport k ws₁ s₀) = transport k ws₂ s₀

/-- [definition] **The tree's readings are injective** at `(k, s₀)`: two ports read one image only if they are one
port (the board's plugboard condition). -/
def TreeInjective (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α)) : Prop :=
  ∀ p q x, treeReading k p₀ s₀ es p = some x → treeReading k p₀ s₀ es q = some x → p = q

/-- [proved-derived; formal-checked] **A tree edge closes its own cycle** at every key and seed image. -/
theorem treeEdge_cycleCloses {p₀ : α} {es : List (MenuEdge Key α)} {e : MenuEdge Key α}
    (h : IsTreeEdge p₀ es e) (k : Key) (s₀ : α) : CycleCloses k p₀ s₀ es e := by
  obtain ⟨q, ws, hq, hmem⟩ := h
  obtain ⟨pre, suf, hsplit⟩ := List.append_of_mem hmem
  obtain ⟨h1, h2⟩ := treeChain_prefix p₀ es hq hsplit
  intro ws₁ ws₂ hw₁ hw₂
  rw [h1, Option.some.injEq] at hw₁
  rw [h2, Option.some.injEq] at hw₂
  subst hw₁ hw₂
  rw [transport_append_one, Equiv.Perm.mul_apply]

/-- [proved-derived; formal-checked] **Only the fundamental cycles decide**: every edge's cycle closes exactly when
every cycle of an edge off the tree does. -/
theorem cycles_close_iff_fundamental (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α)) :
    (∀ e ∈ es, CycleCloses k p₀ s₀ es e) ↔ ∀ e ∈ es, ¬ IsTreeEdge p₀ es e → CycleCloses k p₀ s₀ es e := by
  refine ⟨fun h e he _ => h e he, fun h e he => ?_⟩
  by_cases ht : IsTreeEdge p₀ es e
  · exact treeEdge_cycleCloses ht k s₀
  · exact h e he ht

/-- [definition] **An edge's fundamental cycle as a loop of the Bombe** (`Compression/Core/Keys.Loop`), at the seed:
out along the source's tree walk, across the edge, back along the target's tree walk with each stage inverted (the
empty word where an endpoint has no tree walk). -/
def cycleLoop (p₀ : α) (es : List (MenuEdge Key α)) (e : MenuEdge Key α) : Loop Key α where
  port := p₀
  stages k :=
    match treeChain p₀ es e.src, treeChain p₀ es e.dst with
    | some ws₁, some ws₂ =>
        (ws₂.map fun e' : MenuEdge Key α => (e'.stage k)⁻¹) ++ e.stage k ::
          (ws₁.map fun e' : MenuEdge Key α => e'.stage k).reverse
    | _, _ => []

/-- [definition] **The fundamental-cycle menu**: one loop per edge of the list. -/
def cycleMenu (p₀ : α) (es : List (MenuEdge Key α)) : List (Loop Key α) :=
  es.map (cycleLoop p₀ es)

/-- [proved-derived; formal-checked] **A fundamental loop closes exactly when its cycle closes** at the candidate's
seed image. -/
theorem cycleLoop_closes_iff (p₀ : α) (es : List (MenuEdge Key α)) (e : MenuEdge Key α) (k : Key)
    (S : Equiv.Perm α) : (cycleLoop p₀ es e).Closes (k, S) ↔ CycleCloses k p₀ (S p₀) es e := by
  rw [Loop.closes_iff]
  cases h1 : treeChain p₀ es e.src with
  | none =>
      simp only [cycleLoop, h1, List.prod_nil, Equiv.Perm.coe_one, id_eq, true_iff]
      intro ws₁ ws₂ hw₁; rw [h1] at hw₁; cases hw₁
  | some ws₁ =>
      cases h2 : treeChain p₀ es e.dst with
      | none =>
          simp only [cycleLoop, h1, h2, List.prod_nil, Equiv.Perm.coe_one, id_eq, true_iff]
          intro ws₁' ws₂ _ hw₂; rw [h2] at hw₂; cases hw₂
      | some ws₂ =>
          simp only [cycleLoop, h1, h2, List.prod_append, List.prod_cons, prod_map_inv_eq_inv_transport]
          change ((transport k ws₂)⁻¹ * (e.stage k * transport k ws₁)) (S p₀) = S p₀ ↔ _
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
          constructor
          · intro h ws₁' ws₂' hw₁ hw₂
            rw [h1, Option.some.injEq] at hw₁
            rw [h2, Option.some.injEq] at hw₂
            subst hw₁ hw₂
            exact h
          · intro h
            exact h ws₁ ws₂ h1 h2

/-- [proved-derived; formal-checked] Along a tree walk whose edges hold at a plugboard, the transport of the seed's
image is the port's image. -/
theorem transport_tree_eq {p₀ q : α} {es : List (MenuEdge Key α)} {ws} {k : Key} {S : Equiv.Perm α}
    (hq : treeChain p₀ es q = some ws) (hholds : ∀ e ∈ ws, e.Holds (k, S)) : transport k ws (S p₀) = S q :=
  walk_transports (k, S) ws (treeChain_chain p₀ es hq).1 hholds

/-- [proved-derived; formal-checked] **A plugboard fits every edge exactly when it fits the tree and closes every
fundamental loop.** -/
theorem holds_iff_tree_and_cycles {p₀ : α} {es : List (MenuEdge Key α)} (hord : TraversalOrdered p₀ es)
    (k : Key) (S : Equiv.Perm α) :
    (∀ e ∈ es, e.Holds (k, S)) ↔
      (∀ e ∈ es, IsTreeEdge p₀ es e → e.Holds (k, S)) ∧ ∀ L ∈ cycleMenu p₀ es, L.Closes (k, S) := by
  constructor
  · intro h
    refine ⟨fun e he _ => h e he, fun L hL => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hL
    rw [cycleLoop_closes_iff]
    intro ws₁ ws₂ hw₁ hw₂
    rw [transport_tree_eq hw₁ fun e' he' => h e' ((treeChain_chain p₀ es hw₁).2 e' he'),
      transport_tree_eq hw₂ fun e' he' => h e' ((treeChain_chain p₀ es hw₂).2 e' he')]
    exact (h e he).symm
  · rintro ⟨htree, hcyc⟩ e he
    obtain ⟨ws₁, hw₁⟩ := Option.isSome_iff_exists.mp
      ((treeChain_isSome_iff p₀ es hord e.src).mpr (Or.inr ⟨e, he, Or.inl rfl⟩))
    obtain ⟨ws₂, hw₂⟩ := Option.isSome_iff_exists.mp
      ((treeChain_isSome_iff p₀ es hord e.dst).mpr (Or.inr ⟨e, he, Or.inr rfl⟩))
    have hclose := (cycleLoop_closes_iff p₀ es e k S).mp
      (hcyc _ (List.mem_map.mpr ⟨e, he, rfl⟩)) ws₁ ws₂ hw₁ hw₂
    rw [transport_tree_eq hw₁ fun e' he' => htree e' ((treeChain_chain p₀ es hw₁).2 e' he')
        ⟨e.src, ws₁, hw₁, he'⟩,
      transport_tree_eq hw₂ fun e' he' => htree e' ((treeChain_chain p₀ es hw₂).2 e' he')
        ⟨e.dst, ws₂, hw₂, he'⟩] at hclose
    exact hclose.symm

/-- [proved-derived; formal-checked] **The fundamental loops suffice**: a plugboard fits every edge exactly when it
fits the tree and closes the loop of every edge off the tree. -/
theorem holds_iff_tree_and_fundamental {p₀ : α} {es : List (MenuEdge Key α)} (hord : TraversalOrdered p₀ es)
    (k : Key) (S : Equiv.Perm α) :
    (∀ e ∈ es, e.Holds (k, S)) ↔
      (∀ e ∈ es, IsTreeEdge p₀ es e → e.Holds (k, S)) ∧
        ∀ e ∈ es, ¬ IsTreeEdge p₀ es e → (cycleLoop p₀ es e).Closes (k, S) := by
  rw [holds_iff_tree_and_cycles hord]
  refine and_congr_right fun _ => ?_
  simp only [cycleMenu, List.forall_mem_map, cycleLoop_closes_iff]
  exact cycles_close_iff_fundamental k p₀ (S p₀) es

end Tree

section Survivors

variable {Key α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
/-- [proved-derived; formal-checked] **A survivor is the tree's reading**: a consistent assignment over a
traversal-ordered list sends each port to the seed image carried along the port's tree walk. -/
theorem survivor_eq_treeReading {k : Key} {p₀ s₀ : α} {es : List (MenuEdge Key α)}
    (hord : TraversalOrdered p₀ es) {f : α → Option α} (hf : Consistent k p₀ s₀ es f) :
    f = treeReading k p₀ s₀ es := by
  funext q
  cases h : treeChain p₀ es q with
  | none =>
      have hq : ¬ InPorts p₀ es q := fun hin => by
        have := (treeChain_isSome_iff p₀ es hord q).mpr hin
        rw [h] at this; cases this
      have : (f q).isSome = false := by
        cases hfq : (f q).isSome
        · rfl
        · exact absurd ((hf.dom q).mp hfq) hq
      simp only [treeReading, h, Option.map_none]
      exact Option.not_isSome_iff_eq_none.mp (by simp [this])
  | some ws =>
      obtain ⟨hc, hm⟩ := treeChain_chain p₀ es h
      simp only [treeReading, h, Option.map_some]
      exact survivor_closes_walks hf ws hm hc s₀ hf.seed

/-- [proved-derived; formal-checked] **The survivors are the cycle fibre.** Over a traversal-ordered list, propagation
from `(k, s₀)` returns `f` exactly when every edge's cycle closes, the tree's readings are injective, and `f` is the
tree's reading. -/
theorem propagate_eq_some_iff (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α))
    (hord : TraversalOrdered p₀ es) (f : α → Option α) :
    propagate k p₀ s₀ es = some f ↔
      (∀ e ∈ es, CycleCloses k p₀ s₀ es e) ∧ TreeInjective k p₀ s₀ es ∧ f = treeReading k p₀ s₀ es := by
  rw [propagation_eq_edge_fibre k p₀ s₀ es hord]
  constructor
  · intro hf
    have hfeq := survivor_eq_treeReading hord hf
    refine ⟨fun e he ws₁ ws₂ hw₁ hw₂ => ?_, fun p q x hp hq => hf.inj p q x (hfeq ▸ hp) (hfeq ▸ hq), hfeq⟩
    obtain ⟨x, hx₁, hx₂⟩ := hf.edges e he
    rw [hfeq] at hx₁ hx₂
    simp only [treeReading, hw₁, hw₂, Option.map_some, Option.some.injEq] at hx₁ hx₂
    rw [hx₁, hx₂]
  · rintro ⟨hcyc, hinj, rfl⟩
    refine ⟨fun q => ?_, ?_, fun e he => ?_, hinj⟩
    · rw [treeReading, Option.isSome_map]
      exact treeChain_isSome_iff p₀ es hord q
    · simp [treeReading, treeChain_seed]
    · obtain ⟨ws₁, hw₁⟩ := Option.isSome_iff_exists.mp
        ((treeChain_isSome_iff p₀ es hord e.src).mpr (Or.inr ⟨e, he, Or.inl rfl⟩))
      obtain ⟨ws₂, hw₂⟩ := Option.isSome_iff_exists.mp
        ((treeChain_isSome_iff p₀ es hord e.dst).mpr (Or.inr ⟨e, he, Or.inr rfl⟩))
      refine ⟨transport k ws₁ s₀, by simp [treeReading, hw₁], ?_⟩
      simp only [treeReading, hw₂, Option.map_some, Option.some.injEq]
      exact (hcyc e he ws₁ ws₂ hw₁ hw₂).symm

/-- [proved-derived; formal-checked] **Propagation survives exactly on the cycle fibre**: every edge's cycle closes at
`(k, s₀)` and the tree's readings are injective. -/
theorem survives_iff_cycles_close (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α))
    (hord : TraversalOrdered p₀ es) :
    (∃ f, propagate k p₀ s₀ es = some f) ↔ (∀ e ∈ es, CycleCloses k p₀ s₀ es e) ∧ TreeInjective k p₀ s₀ es := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨h1, h2, -⟩ := (propagate_eq_some_iff k p₀ s₀ es hord f).mp hf
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, (propagate_eq_some_iff k p₀ s₀ es hord _).mpr ⟨h1, h2, rfl⟩⟩

/-- [proved-derived; formal-checked] **The fundamental cycles decide survival**: propagation survives exactly when the
cycle of every edge off the tree closes and the tree's readings are injective. -/
theorem survives_iff_fundamental (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α))
    (hord : TraversalOrdered p₀ es) :
    (∃ f, propagate k p₀ s₀ es = some f) ↔
      (∀ e ∈ es, ¬ IsTreeEdge p₀ es e → CycleCloses k p₀ s₀ es e) ∧ TreeInjective k p₀ s₀ es := by
  rw [survives_iff_cycles_close k p₀ s₀ es hord, cycles_close_iff_fundamental]

/-- [proved-derived; formal-checked] **A survivor's image does not depend on the walk that reads it**: any two walks of
the menu from the seed to one port carry the seed image to the same image. -/
theorem survivor_path_independent {k : Key} {p₀ s₀ : α} {es : List (MenuEdge Key α)} {f : α → Option α}
    (hord : TraversalOrdered p₀ es) (hf : propagate k p₀ s₀ es = some f) {q : α} {ws ws' : List (MenuEdge Key α)}
    (hws : ∀ e ∈ ws, e ∈ es) (hws' : ∀ e ∈ ws', e ∈ es) (hc : Chain p₀ ws q) (hc' : Chain p₀ ws' q) :
    transport k ws s₀ = transport k ws' s₀ := by
  have hcons := (propagation_eq_edge_fibre k p₀ s₀ es hord f).mp hf
  have h1 := survivor_closes_walks hcons ws hws hc s₀ hcons.seed
  have h2 := survivor_closes_walks hcons ws' hws' hc' s₀ hcons.seed
  rw [h1] at h2
  exact Option.some.inj h2

/-- [proved-derived; formal-checked] **A plugboard that fits the tree survives exactly when it closes every
fundamental loop**, and then it fits every edge (`holds_iff_tree_and_cycles`). -/
theorem plugboard_survives_iff {p₀ : α} {es : List (MenuEdge Key α)} (hord : TraversalOrdered p₀ es)
    (k : Key) (S : Equiv.Perm α) (htree : ∀ e ∈ es, IsTreeEdge p₀ es e → e.Holds (k, S)) :
    (∃ f, propagate k p₀ (S p₀) es = some f) ↔ ∀ L ∈ cycleMenu p₀ es, L.Closes (k, S) := by
  rw [survives_iff_cycles_close k p₀ (S p₀) es hord]
  simp only [cycleMenu, List.forall_mem_map, cycleLoop_closes_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, fun p q x hp hq => ?_⟩⟩
  have hread : ∀ r y, treeReading k p₀ (S p₀) es r = some y → S r = y := by
    intro r y hr
    obtain ⟨ws, hw, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact (transport_tree_eq hw fun e' he' => htree e' ((treeChain_chain p₀ es hw).2 e' he')
      ⟨r, ws, hw, he'⟩).symm
  exact S.injective ((hread p x hp).trans (hread q x hq).symm)

/-- [proved-derived; formal-checked] **The survivors are the loop-closure fibre of the fundamental-cycle menu**, cut by
the board's plugboard condition. Over a truth that fits every edge, the candidates `(k, S)` whose seed image survives
propagation are the fibre of `cycleMenu` (`Compression/Core/Keys.fibre`) whose tree readings are injective. -/
theorem survivors_eq_cycle_fibre {p₀ : α} {es : List (MenuEdge Key α)} (hord : TraversalOrdered p₀ es)
    (truth : Key × Equiv.Perm α) (htruth : ∀ e ∈ es, e.Holds truth) :
    {c : Key × Equiv.Perm α | ∃ f, propagate c.1 p₀ (c.2 p₀) es = some f} =
      fibre (cycleMenu p₀ es) truth ∩ {c | TreeInjective c.1 p₀ (c.2 p₀) es} := by
  have hobs : Observed (cycleMenu p₀ es) truth :=
    ((holds_iff_tree_and_cycles hord truth.1 truth.2).mp htruth).2
  rw [fibre_eq_bombe hobs]
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, survives_iff_cycles_close c.1 p₀ (c.2 p₀) es hord]
  refine and_congr_left fun _ => ?_
  simp only [cycleMenu, List.forall_mem_map]
  refine forall₂_congr fun e _ => ?_
  rw [← Loop.closes_iff, cycleLoop_closes_iff]

end Survivors

end Holonics.HNN.SurvivorsCycleFibre
