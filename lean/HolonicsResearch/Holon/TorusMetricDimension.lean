import HolonicsResearch.Holon.LoopCurvature

/-!
# The tori `C₄ □ C₄` and `C₅ □ C₅`: four landmarks and three, read through the torus's translations

[proved-derived] The source is #410's box "Loop curvature" (first Betti numbers, the zero-reduced-cost lemma and the
small metric-dimension cases, checked only in `research/notebook/motion/loop_curvature_checks.py`), part done in
#1003 by `HolonicsResearch/Holon/LoopCurvature`, which left the two tori of the notebook's last loop: their refusals
run over every triple of 16 vertices or every pair of 25, past that file's budget.

What is proved.

1. **A translation carries a resolving set to a resolving set** (`resolves_image_add`): on an additive group whose
   distance is invariant under translation, `S` resolves exactly when `S + g` does, so the refusal of every set of
   three (or two) landmarks is read on the sets that hold `0` (`not_resolves_triple`, `not_resolves_pair`). The
   torus `ℤ/k × ℤ/k` with the box distance of two rings is invariant under its translations for `k = 4, 5`
   (`torus4_translate`, `torus5_translate`, decided on the rings).
2. **Fewer than four lie in a triple** (`subset_triple_of_card_lt_four`), and metric dimension four follows from a
   resolving set of four and the refusal of every triple (`isMetricDimension_four`), as `LoopCurvature`'s
   `isMetricDimension_three` does for three.
3. **`C₄ □ C₄` needs four** (`torus44_metricDimension`): the box distance satisfies the torus's Bellman equation (so
   it is the graph distance, `LoopCurvature.bellman_unique`), `{(0,0), (0,1), (0,2), (1,0)}` resolves, and no three
   vertices do. The kernel reads 256 triples through `0`, about 17 s.
4. **`C₅ □ C₅` needs three** (`torus55_metricDimension`): `{(0,0), (0,1), (2,0)}` resolves and no two vertices do,
   read on the 25 pairs through `0`.

So with the notebook's `C₃ □ C₄` (three, in `LoopCurvature`), a torus of two even rings needs four landmarks and one
with an odd ring three, the values the notebook printed (`metric dimension of C4 x C4 = 4`, `of C5 x C5 = 3`).

Limits. Two tori, each by a finite check: the general law for `C_m □ C_n` (three when a ring is odd, four when both
are even) is not proved here. The translation lemma is general; the invariance of the box distance is decided for
`k = 4` and `k = 5` only. The distance tables are certified by their Bellman equation, as in `LoopCurvature`.

The computational object is the helical pair interaction: each ring of the torus is a helix's turn, a landmark is a
receiver whose distances are the faces it reads, and a resolving set is a set of receivers whose faces together
separate every place, the torus's translations carrying one such set to another. Of the winding guide's six general
objects this touches the helix (the two rings), the faces and placement (the landmarks' readings) and the cell
holonomy (the torus's two loops, `LoopCurvature.torus_betti1`); the pair, the tube and the tower thread stay
attached.

Consumers: the atlas row of the loop-curvature checks and `LoopCurvature`'s metric-dimension section.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Holon.TorusMetricDimension

open Holonics.Holon.LoopCurvature

section Translate

variable {G : Type*} [AddGroup G]

/-- [proved-derived; formal-checked] **A translation carries a resolving set to a resolving set**: if the distance
is invariant under translation, `S + g` resolves whenever `S` does. -/
theorem resolves_image_add [DecidableEq G] {d : G → G → ℕ} (hd : ∀ g s u, d (s + g) (u + g) = d s u)
    {S : Finset G} (hS : Resolves d S) (g : G) : Resolves d (S.image (· + g)) := by
  intro u v h
  have key : u - g = v - g := by
    refine hS (u - g) (v - g) fun s hs => ?_
    have hsg := h (s + g) (Finset.mem_image_of_mem _ hs)
    rw [← hd g s (u - g), ← hd g s (v - g), sub_add_cancel, sub_add_cancel]
    exact hsg
  simpa using congrArg (· + g) key

/-- [proved-derived; formal-checked] **The refusal of every triple is read through `0`**: if no triple holding `0`
resolves, no triple does. -/
theorem not_resolves_triple [DecidableEq G] {d : G → G → ℕ} (hd : ∀ g s u, d (s + g) (u + g) = d s u)
    (h0 : ∀ b c : G, ¬ Resolves d {0, b, c}) (a b c : G) : ¬ Resolves d {a, b, c} := by
  intro h
  have ht := resolves_image_add hd h (-a)
  rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton, add_neg_cancel] at ht
  exact h0 (b + -a) (c + -a) ht

/-- [proved-derived; formal-checked] **The refusal of every pair is read through `0`.** -/
theorem not_resolves_pair [DecidableEq G] {d : G → G → ℕ} (hd : ∀ g s u, d (s + g) (u + g) = d s u)
    (h0 : ∀ b : G, ¬ Resolves d {0, b}) (a b : G) : ¬ Resolves d {a, b} := by
  intro h
  have ht := resolves_image_add hd h (-a)
  rw [Finset.image_insert, Finset.image_singleton, add_neg_cancel] at ht
  exact h0 (b + -a) ht

end Translate

section Four

variable {α : Type*} [DecidableEq α]

/-- [proved-derived; formal-checked] Every set of fewer than four vertices lies in a triple. -/
theorem subset_triple_of_card_lt_four [Nonempty α] (T : Finset α) (hT : T.card < 4) :
    ∃ a b c, T ⊆ {a, b, c} := by
  obtain ⟨a₀⟩ := ‹Nonempty α›
  interval_cases h : T.card
  · rw [Finset.card_eq_zero] at h
    exact ⟨a₀, a₀, a₀, by simp [h]⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, a, a, by simp⟩
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, a, b, by simp⟩
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := Finset.card_eq_three.mp h
    exact ⟨a, b, c, le_rfl⟩

/-- [proved-derived; formal-checked] Metric dimension four from a resolving set of four and the refusal of every
triple. -/
theorem isMetricDimension_four [Nonempty α] (d : α → α → ℕ) (S : Finset α) (hS : S.card = 4)
    (hres : Resolves d S) (hthree : ∀ a b c, ¬ Resolves d {a, b, c}) : IsMetricDimension d 4 := by
  refine ⟨⟨S, hS, hres⟩, fun T hT hTres => ?_⟩
  obtain ⟨a, b, c, habc⟩ := subset_triple_of_card_lt_four T hT
  exact hthree a b c (hTres.mono habc)

end Four

/-! ## The two tori -/

/-- [proved-derived; formal-checked] The ring `C₄`'s distance is invariant under its turns. -/
theorem cycle4_translate : ∀ g i j : Fin 4, cycleDist (i + g) (j + g) = cycleDist i j := by
  decide +kernel

/-- [proved-derived; formal-checked] The ring `C₅`'s distance is invariant under its turns. -/
theorem cycle5_translate : ∀ g i j : Fin 5, cycleDist (i + g) (j + g) = cycleDist i j := by
  decide +kernel

/-- [proved-derived; formal-checked] The torus `C₄ □ C₄`'s distance is invariant under its translations. -/
theorem torus4_translate (g s u : Fin 4 × Fin 4) :
    boxDist cycleDist cycleDist (s + g) (u + g) = boxDist (cycleDist (k := 4)) cycleDist s u := by
  simp only [boxDist, Prod.fst_add, Prod.snd_add, cycle4_translate]

/-- [proved-derived; formal-checked] The torus `C₅ □ C₅`'s distance is invariant under its translations. -/
theorem torus5_translate (g s u : Fin 5 × Fin 5) :
    boxDist cycleDist cycleDist (s + g) (u + g) = boxDist (cycleDist (k := 5)) cycleDist s u := by
  simp only [boxDist, Prod.fst_add, Prod.snd_add, cycle5_translate]

set_option maxRecDepth 200000 in
/-- [proved-derived; formal-checked] No three vertices through `(0, 0)` resolve `C₄ □ C₄` (256 triples, decided). -/
theorem torus44_no_triple_through_zero : ∀ b c : Fin 4 × Fin 4,
    ¬ Resolves (boxDist (cycleDist (k := 4)) (cycleDist (k := 4))) {0, b, c} := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- [proved-derived; formal-checked] **The torus `C₄ □ C₄` needs four**, both its rings being even: its box distance
is the graph distance (Bellman), `{(0,0), (0,1), (0,2), (1,0)}` resolves, and no three vertices do. -/
theorem torus44_metricDimension :
    IsBellmanDistance (boxAdj (cycleAdj (k := 4)) (cycleAdj (k := 4))) (boxDist cycleDist cycleDist) ∧
      IsMetricDimension (boxDist (cycleDist (k := 4)) (cycleDist (k := 4))) 4 :=
  ⟨by decide +kernel,
    isMetricDimension_four _ {(0, 0), (0, 1), (0, 2), (1, 0)} rfl (by decide +kernel)
      (not_resolves_triple torus4_translate torus44_no_triple_through_zero)⟩

set_option maxRecDepth 200000 in
/-- [proved-derived; formal-checked] No two vertices through `(0, 0)` resolve `C₅ □ C₅` (25 pairs, decided). -/
theorem torus55_no_pair_through_zero : ∀ b : Fin 5 × Fin 5,
    ¬ Resolves (boxDist (cycleDist (k := 5)) (cycleDist (k := 5))) {0, b} := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- [proved-derived; formal-checked] **The torus `C₅ □ C₅` needs three**, a ring being odd: its box distance is the
graph distance (Bellman), `{(0,0), (0,1), (2,0)}` resolves, and no two vertices do. -/
theorem torus55_metricDimension :
    IsBellmanDistance (boxAdj (cycleAdj (k := 5)) (cycleAdj (k := 5))) (boxDist cycleDist cycleDist) ∧
      IsMetricDimension (boxDist (cycleDist (k := 5)) (cycleDist (k := 5))) 3 :=
  ⟨by decide +kernel,
    isMetricDimension_three _ {(0, 0), (0, 1), (2, 0)} rfl (by decide +kernel)
      (not_resolves_pair torus5_translate torus55_no_pair_through_zero)⟩

end Holonics.Holon.TorusMetricDimension
