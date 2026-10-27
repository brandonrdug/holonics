import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# The loops of a region: gluing a region's returns gives the passage `k − 1` cycles

The record `research/records/2026-10-26_A_REFERENT_IS_DENSE_BY_THE_LOOPS_THAT_CLOSE_THROUGH_IT_AND_SEVEN_IN_TEN_RUN_THROUGH_A_PRONOUN.md`
(§3.1, atlas `receiver.referent-laps`) reads a passage's mentions in order as a path of `N` vertices,
`N − 1` edges and one component, and identifies the `k` mentions that return to one region. #410
owes the count: the glued passage has `N − k + 1` vertices and the same edges, so its cycle rank is
`β₁ = E − V + C = k − 1`, and over regions `β₁ = Σ_r (k_r − 1)`. This file proves it.

A gluing is any surjection `g` from the mentions `Fin N`, `N = n + 1`, onto the glued vertices; the
returns of a vertex are its fibre. Mention `i` meets mention `i + 1`: the passage keeps its `n` edges,
and two adjacent returns to one region make a loop edge, which still counts.

[proved-derived; formal-checked] What is proved.

1. **The returns count the mentions** (`sum_returns`): `Σ_v k_v = N`, so the glued vertices number
   `N − Σ_v (k_v − 1)` (`card_glued`).
2. **One component** (`reachable_first`, `gluedGraph_connected`, `components_eq_one`): every glued
   vertex is reached from the first mention's along the passage, so the glued passage is connected
   and has exactly one connected component.
3. **The cycle rank** (`cycleRank_eq_sum`): `β₁ = E − V + C = Σ_v (k_v − 1)` over the glued vertices,
   a mention left alone counting `0`; for one region of `k` returns, `β₁ = k − 1` and the vertices
   number `N − k + 1` (`cycleRank_one_region`, `card_one_region`); with no returns the passage is a
   path and `β₁ = 0` (`cycleRank_no_return`).

The computational object is the helical pair interaction's contact graph read over a passage: a
return that agrees closes a loop through its region. Of the winding guide's six general objects this
touches the cell holonomy (the loops round which a passage's turn is read); the helix, the pair,
faces and placement, the tube and the tower thread stay attached.

Consumers: the atlas row `receiver.referent-laps` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.RegionLoops

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The returns -/

/-- [definition] The returns of glued vertex `v`: the mentions the gluing sends to it. -/
def returns {n : ℕ} (g : Fin (n + 1) → V) (v : V) : ℕ := (univ.filter fun i => g i = v).card

/-- [proved-derived; formal-checked] **The returns count the mentions**: `Σ_v k_v = N`. -/
theorem sum_returns {n : ℕ} (g : Fin (n + 1) → V) : ∑ v, returns g v = n + 1 := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin (n + 1))))
    (t := (univ : Finset V)) (f := g) (fun i _ => mem_coe.2 (mem_univ (g i)))
  simp only [card_univ, Fintype.card_fin] at h
  exact h.symm

/-- [proved-derived; formal-checked] The glued vertices number `N − Σ_v (k_v − 1)`. -/
theorem card_glued {n : ℕ} (g : Fin (n + 1) → V) :
    (Fintype.card V : ℤ) = (n + 1 : ℤ) - ∑ v, ((returns g v : ℤ) - 1) := by
  have hs : (∑ v, (returns g v : ℤ)) = n + 1 := by exact_mod_cast sum_returns g
  rw [Finset.sum_sub_distrib, hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-! ## 2. One component -/

/-- [definition] The glued passage: mention `i` meets mention `i + 1`, read on the glued vertices. A
loop edge (two adjacent returns to one region) adds no adjacency, while the edge count keeps it. -/
def gluedGraph {n : ℕ} (g : Fin (n + 1) → V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ i : Fin n, e = s(g i.castSucc, g i.succ)}

/-- [proved-derived; formal-checked] Every mention's vertex is reached from the first mention's along
the passage. -/
theorem reachable_first {n : ℕ} (g : Fin (n + 1) → V) (i : Fin (n + 1)) :
    (gluedGraph g).Reachable (g 0) (g i) := by
  induction i using Fin.induction with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ i ih =>
    refine ih.trans ?_
    by_cases h : g i.castSucc = g i.succ
    · simp only [h]
      exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).2 ⟨⟨i, rfl⟩, h⟩)

/-- [proved-derived; formal-checked] **The glued passage is connected.** -/
theorem gluedGraph_connected {n : ℕ} {g : Fin (n + 1) → V} (hg : Function.Surjective g) :
    (gluedGraph g).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨g 0, fun v => ?_⟩
  obtain ⟨i, rfl⟩ := hg v
  exact reachable_first g i

/-- [proved-derived; formal-checked] **One component**: `C = 1`. -/
theorem components_eq_one {n : ℕ} {g : Fin (n + 1) → V} (hg : Function.Surjective g) :
    Nat.card (gluedGraph g).ConnectedComponent = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨(gluedGraph_connected hg).preconnected.subsingleton_connectedComponent,
    ⟨(gluedGraph g).connectedComponentMk (g 0)⟩⟩

/-! ## 3. The cycle rank -/

/-- [definition] The cycle rank of the glued passage, `β₁ = E − V + C`: its `n` edges (a loop edge
counts), its glued vertices and its components. -/
noncomputable def cycleRank {n : ℕ} (g : Fin (n + 1) → V) : ℤ :=
  Fintype.card (Fin n) - Fintype.card V + Nat.card (gluedGraph g).ConnectedComponent

/-- [proved-derived; formal-checked] **The loops of the regions**: `β₁ = Σ_v (k_v − 1)`, each glued
vertex adding one loop for each return past its first. -/
theorem cycleRank_eq_sum {n : ℕ} {g : Fin (n + 1) → V} (hg : Function.Surjective g) :
    cycleRank g = ∑ v, ((returns g v : ℤ) - 1) := by
  rw [cycleRank, components_eq_one hg, Fintype.card_fin, card_glued g]
  push_cast
  ring

/-- [proved-derived; formal-checked] **One region**: when one glued vertex `v₀` takes the region's
`k` returns and every other vertex one mention, `β₁ = k − 1`. -/
theorem cycleRank_one_region {n : ℕ} {g : Fin (n + 1) → V} (hg : Function.Surjective g) (v₀ : V)
    (hrest : ∀ v, v ≠ v₀ → returns g v = 1) :
    cycleRank g = (returns g v₀ : ℤ) - 1 := by
  rw [cycleRank_eq_sum hg, Finset.sum_eq_single v₀ (fun v _ hv => by rw [hrest v hv]; simp)
    (fun h => absurd (mem_univ v₀) h)]

/-- [proved-derived; formal-checked] One region leaves `N − k + 1` vertices. -/
theorem card_one_region {n : ℕ} {g : Fin (n + 1) → V} (hg : Function.Surjective g) (v₀ : V)
    (hrest : ∀ v, v ≠ v₀ → returns g v = 1) :
    (Fintype.card V : ℤ) = (n + 1 : ℤ) - returns g v₀ + 1 := by
  have h1 := cycleRank_one_region hg v₀ hrest
  rw [cycleRank, components_eq_one hg, Fintype.card_fin] at h1
  push_cast at h1
  linarith

/-- [proved-derived; formal-checked] With no returns the passage is a path: `β₁ = 0`. -/
theorem cycleRank_no_return {n : ℕ} {g : Fin (n + 1) → V} (hg : Function.Surjective g)
    (h1 : ∀ v, returns g v = 1) : cycleRank g = 0 := by
  rw [cycleRank_eq_sum hg]
  simp [h1]

end Holonics.HNN.RegionLoops
