import Holonics.Compression.Landmark.Context.Capacity
import Holonics.Aeon.Clock.Epoch

/-!
# Compression.Landmark.Context.Epoch: a node's arrivals are the epochs of its section

[definition; agent-inferred] The unity audit of September 27 (`research/records/2026-09-27_THE_
HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_
PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md`, §2). A node of the receiving tree is a receiver:
its section is reached at the cells whose address opens it, and its ticks cut the passage into
**epochs** (`Aeon/Clock/Epoch`). This owner joins the tree's arrivals to that clock. The
computational object is the helical pair interaction's receiving tree; of the winding guide's six
general objects it touches the **helix** (the node's count register winds on its own clock and
carries at its capacity) and the **tower thread** (a node's section is its context depth's
restriction of the address); the rest stay attached.

```text
aeon       micro-states 0, …, n  (micro-state t + 1 follows cell t of a passage of n cells)
section    ticks_s = {t + 1 : the address of cell t opens s}  ⊆ (0, n + 1)
epoch      epochOf ticks_s k = #{tick ≤ k} = |routed (obs.take k) s|
register   σ_s(k) = run (routed (obs.take k) s) ;  capped: Σ_c σ_s(k)(c) ≤ epochOf ticks_s k
```

[proved-derived; formal-checked] What is proved.

1. **The node's section is certified** (`nodeTicks`, `nodeSection`, `nodeTicks_snoc`,
   `node_epochs_attained`): its ticks lie strictly inside the aeon, so they cut it into
   `#ticks + 1` nonempty epochs (`Aeon/Clock/Epoch.epochs_attained`).
2. **A node's arrivals are its epochs** (`arrivals_are_epochs`, `node_arrivals_card`): after the
   first `k` cells, the number of arrivals that reached the node is the epoch index of micro-state
   `k` at its section, `epochOf ticks_s k`; over the whole passage it is the number of ticks.
3. **The register is read on the node's epochs** (`observations_drop`, `node_register_on_epochs`):
   under any node law, after the passage's first `k` cells the node's register and own weight are
   the law's run and mass of the classes that arrived at its ticks up to `k` (its epoch history),
   whose length is the epoch index.
4. **The capped register is a function of its epoch history** (`capped_register_on_epochs`): the
   capacity's register at micro-state `k` is `capLaw`'s run of the node's epoch history, and its
   total never passes the epoch index, so the carry acts on the node's own clock.

The Rust consumer is `crates/holonics/src/compression/landmark/context.rs`
(`compression::landmark::context`, `Capacity` and the deposit's count register).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.Epoch

open Finset
open Holonics.Aeon.Clock.Epoch (epochOf CertifiedSection epochs_attained)
open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.Capacity (capLaw cap_run_total_le)

universe u v

/-! ## 1. The node's section -/

section Section

variable {Ltr : Type u} [DecidableEq Ltr] {A : Type v}

/-- [definition] **A node's section** in a passage of observations (oldest first): the micro-states
`t + 1` after each cell `t` whose address opens the node `s`, strictly inside the aeon of
`obs.length + 1` micro-states (micro-state `0` precedes the first cell). -/
def nodeTicks (obs : List (List Ltr × A)) (s : List Ltr) : Finset ℕ :=
  (Ioo 0 (obs.length + 1)).filter fun k =>
    (obs[k - 1]?).map (fun o => decide (o.1.take s.length = s)) = some true

/-- [definition] **The node's section is certified**: its ticks lie strictly inside the aeon. -/
def nodeSection (obs : List (List Ltr × A)) (s : List Ltr) : CertifiedSection (obs.length + 1) :=
  ⟨nodeTicks obs s, filter_subset _ _⟩

theorem nodeTicks_nil (s : List Ltr) :
    nodeTicks ([] : List (List Ltr × A)) s = ∅ := by
  simp [nodeTicks]

/-- A cell appended to the passage ticks the node's section at the new micro-state exactly when
its address opens the node. -/
theorem nodeTicks_snoc (obs : List (List Ltr × A)) (o : List Ltr × A) (s : List Ltr) :
    nodeTicks (obs ++ [o]) s =
      if o.1.take s.length = s then insert (obs.length + 1) (nodeTicks obs s)
      else nodeTicks obs s := by
  have hold : ∀ k, k ≠ obs.length + 1 →
      (k ∈ nodeTicks (obs ++ [o]) s ↔ k ∈ nodeTicks obs s) := by
    intro k hk
    simp only [nodeTicks, mem_filter, mem_Ioo, List.length_append, List.length_singleton]
    constructor
    · rintro ⟨⟨h0, h1⟩, hg⟩
      have hk' : k - 1 < obs.length := by omega
      rw [List.getElem?_append_left hk'] at hg
      exact ⟨⟨h0, by omega⟩, hg⟩
    · rintro ⟨⟨h0, h1⟩, hg⟩
      have hk' : k - 1 < obs.length := by omega
      rw [List.getElem?_append_left hk']
      exact ⟨⟨h0, by omega⟩, hg⟩
  have hnew : obs.length + 1 ∈ nodeTicks (obs ++ [o]) s ↔ o.1.take s.length = s := by
    simp [nodeTicks]
  have hout : obs.length + 1 ∉ nodeTicks obs s := by simp [nodeTicks]
  ext k
  split_ifs with ho
  · rw [mem_insert]
    by_cases hk : k = obs.length + 1
    · subst hk
      exact iff_of_true (hnew.2 ho) (Or.inl rfl)
    · rw [hold k hk]
      exact ⟨Or.inr, fun h => h.resolve_left hk⟩
  · by_cases hk : k = obs.length + 1
    · subst hk
      exact iff_of_false (fun h => ho (hnew.1 h)) hout
    · exact hold k hk

/-- [proved-derived; formal-checked] **`node_epochs_attained`: the node's section cuts the aeon into
`#ticks + 1` nonempty epochs** (`Aeon/Clock/Epoch.epochs_attained` at the certified section). -/
theorem node_epochs_attained (obs : List (List Ltr × A)) (s : List Ltr) :
    (range (obs.length + 1)).image (epochOf (nodeTicks obs s)) =
      range (#(nodeTicks obs s) + 1) :=
  epochs_attained (nodeSection obs s) (Nat.succ_pos _)

/-- [proved-derived; formal-checked] **`arrivals_are_epochs`: a node's arrivals are the epochs of its
section.** After the passage's first `k` cells, the number of arrivals routed to the node `s` is the
epoch index of micro-state `k` at the node's section. -/
theorem arrivals_are_epochs (obs : List (List Ltr × A)) (s : List Ltr) :
    ∀ k, (routed (obs.take k) s).length = epochOf (nodeTicks obs s) k := by
  induction obs using List.reverseRecOn with
  | nil => intro k; simp [routed, nodeTicks_nil, epochOf]
  | append_singleton obs o ih =>
    obtain ⟨a, c⟩ := o
    intro k
    have hout : obs.length + 1 ∉ nodeTicks obs s := by simp [nodeTicks]
    by_cases hk : k ≤ obs.length
    · rw [List.take_append_of_le_length hk, ih k, nodeTicks_snoc]
      split_ifs
      · unfold epochOf
        rw [filter_insert, if_neg (by omega)]
      · rfl
    · have hk' : obs.length + 1 ≤ k := by omega
      have htake : (obs ++ [(a, c)]).take k = obs ++ [(a, c)] :=
        List.take_of_length_le (by simp; omega)
      have hih := ih k
      rw [List.take_of_length_le (by omega)] at hih
      rw [htake, routed_snoc, List.length_append, hih, nodeTicks_snoc]
      split_ifs with ho
      · unfold epochOf
        rw [filter_insert, if_pos hk', card_insert_of_notMem fun h => hout (mem_filter.1 h).1,
          List.length_singleton]
      · rw [List.length_nil, Nat.add_zero]

/-- [proved-derived; formal-checked] **`node_arrivals_card`: over the whole passage a node's
arrivals number its ticks.** -/
theorem node_arrivals_card (obs : List (List Ltr × A)) (s : List Ltr) :
    (routed obs s).length = #(nodeTicks obs s) := by
  have h := arrivals_are_epochs obs s obs.length
  rw [List.take_of_length_le le_rfl] at h
  rw [h, epochOf, filter_true_of_mem]
  intro t ht
  have := (mem_Ioo.1 ((nodeSection obs s).inside ht)).2
  omega

end Section

/-! ## 2. The register is read on the node's epochs -/

section Register

variable {Ltr : Type u} [DecidableEq Ltr] {A : Type v}

omit [DecidableEq Ltr] in
/-- A passage's observations number its cells. -/
theorem observations_length (ctx : List A → List Ltr) :
    ∀ h : List A, (observations ctx h).length = h.length
  | [] => rfl
  | c :: h => by simp [observations, observations_length ctx h]

omit [DecidableEq Ltr] in
/-- The observations of the passage's first cells are the first observations. -/
theorem observations_drop (ctx : List A → List Ltr) :
    ∀ (h : List A) (k : ℕ),
      observations ctx (h.drop k) = (observations ctx h).take (h.length - k)
  | [], k => by simp [observations]
  | c :: h, 0 => by
    rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le (observations_length ctx _).le]
  | c :: h, k + 1 => by
    rw [List.drop_succ_cons, observations_drop ctx h k, observations,
      List.length_cons, Nat.add_sub_add_right, List.take_append_of_le_length]
    rw [observations_length]
    omega

/-- [proved-derived; formal-checked] **`node_register_on_epochs`: the register is read on the node's
epochs.** Under any node law, after the passage's first `k` cells (the history `h.drop (|h| − k)`),
the node's arrivals number the epoch index of micro-state `k` at its section, and its register and
own weight are the law's run and mass of its epoch history (the classes that arrived at its ticks up
to `k`). -/
theorem node_register_on_epochs [Fintype A] (L : NodeLaw A) (ctx : List A → List Ltr) (h : List A)
    (s : List Ltr) {k : ℕ} (hk : k ≤ h.length) :
    (routed ((observations ctx h).take k) s).length = epochOf (nodeTicks (observations ctx h) s) k ∧
      lawState L (lawStandingOf L ctx (h.drop (h.length - k))) s =
        L.run (routed ((observations ctx h).take k) s) ∧
      lawOwn L (lawStandingOf L ctx (h.drop (h.length - k))) s =
        L.mass (routed ((observations ctx h).take k) s) := by
  have hobs : observations ctx (h.drop (h.length - k)) = (observations ctx h).take k := by
    rw [observations_drop, Nat.sub_sub_self hk]
  obtain ⟨hs, ho⟩ := law_state_own_routed L ctx (h.drop (h.length - k)) s
  rw [hobs] at hs ho
  exact ⟨arrivals_are_epochs _ s k, hs, ho⟩

/-- [proved-derived; formal-checked] **`capped_register_on_epochs`: the capped register is a function
of the node's epoch history.** After the passage's first `k` cells the capacity's register at the
node is `capLaw`'s run of the classes that arrived at its ticks up to `k`, and its total never passes
the epoch index of micro-state `k`: the carry acts on the node's own clock. -/
theorem capped_register_on_epochs [Fintype A] [DecidableEq A] [Nonempty A] (cap : Option ℕ) (ctx : List A → List Ltr)
    (h : List A) (s : List Ltr) {k : ℕ} (hk : k ≤ h.length) :
    lawState (capLaw A cap) (lawStandingOf (capLaw A cap) ctx (h.drop (h.length - k))) s =
        (capLaw A cap).run (routed ((observations ctx h).take k) s) ∧
      ∑ c, lawState (capLaw A cap) (lawStandingOf (capLaw A cap) ctx (h.drop (h.length - k))) s c ≤
        epochOf (nodeTicks (observations ctx h) s) k := by
  obtain ⟨hn, hs, -⟩ := node_register_on_epochs (capLaw A cap) ctx h s hk
  refine ⟨hs, ?_⟩
  rw [hs, ← hn]
  exact cap_run_total_le cap _

end Register

section Audit

#print axioms nodeTicks_nil
#print axioms nodeTicks_snoc
#print axioms node_epochs_attained
#print axioms arrivals_are_epochs
#print axioms node_arrivals_card
#print axioms observations_length
#print axioms observations_drop
#print axioms node_register_on_epochs
#print axioms capped_register_on_epochs

end Audit

end Holonics.Compression.Landmark.Context.Epoch
