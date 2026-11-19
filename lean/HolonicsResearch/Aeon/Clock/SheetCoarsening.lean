import Holonics.Aeon.Clock.Epoch
import Mathlib.Tactic

/-!
# Sheets do not coarsen: the oriented coarsening of epochs is refused, and holds on an aeon that never crosses back

`Aeon/Clock/Epoch` proves that epochs coarsen: when a sub-section's ticks are among a section's ticks, the coarse epoch
is a function of the fine epoch, composing along a tower (`epochOf_coarse`, `coarsen_tower`). The retired Rust owner
`EpochTower` ([`crates/holonics/src/aeon/epoch.rs` at
`d5ed4adc1`](https://github.com/brandonrdug/holonics/blob/d5ed4adc1/crates/holonics/src/aeon/epoch.rs)) also carried the
**sheet** of a micro-state, the flux up to it, and left its coarsening open: its test
`the_sheets_of_a_sub_cut_crossed_back_do_not_coarsen` found one fine sheet meeting two coarse sheets. This module states
that refusal beside the unoriented law, and the law that holds where the refusal's cause is absent.

[proved-derived; formal-checked] What is proved, on words of steps `(edge, forward?)` read by cut cochains.

1. **The sheet is the reading of the prefix** (`sheet`, `sheet_eq_crossings`): the forward crossings less the backward
   crossings of the first `j` steps, `Epoch.wordReading_eq_crossings` on the prefix.
2. **Epochs coarsen under every sub-cut** (`crossingTicks_subset_of_subCut`, `epochs_coarsen`): a sub-cut's crossing
   ticks are the cut's, so `Epoch.epochOf_coarse` applies to every word.
3. **Sheets coarsen exactly when a coarse sheet is a function of the fine sheet** (`SheetsCoarsen`,
   `sheetsCoarsen_iff_exists`).
4. **The refusal** (`sheets_do_not_coarsen`): on two edges, the cut of both and the sub-cut of the second, the word
   "the first edge forward, the second back" returns to its first fine sheet while the coarse sheet has moved to `−1`;
   its epochs coarsen by the Rust's map `0 ↦ 0, 1 ↦ 0, 2 ↦ 1`. So no oriented coarsening law holds for every word.
5. **The law where nothing crosses back** (`sheetsCoarsen_of_forward`): if no step crosses the fine cut against its
   orientation, the sheets coarsen under every sub-cut. On such a word the sheet is the epoch, and a fine sheet held
   between two micro-states holds the coarse one.

The computational object is the helical pair interaction's clock: a section of a navigator's helix read as a cut, its
flux the whole windings, the sheet the sheet of the section's cover a micro-state lies on. Of the winding guide's six
general objects this touches the helix (the sheets of the cover) and the tower thread (the coarsening along sub-sections);
the pair, faces and placement, the cell holonomy and the tube stay attached.

What stands beside it: the Rust's tower validation and its refusals of mismatched grains, and the arrival form of the
non-coarsening (`Epoch.nontransversal_subsection_does_not_coarsen`), which is a different cause: a section the motion
lingers on.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Aeon.Clock.SheetCoarsening

open Finset Holonics.Aeon.Clock.Epoch Holonics.Aeon.Clock.Reading

variable {E : Type*}

/-! ## 1. Sheets and sub-cuts -/

/-- [definition] **The sheet of micro-state `j`**: the flux of the first `j` steps across the section. -/
def sheet (ω : E → ℤ) (w : List (E × Bool)) (j : ℕ) : ℤ := wordReading ω (w.take j)

/-- The sheet is the forward crossings less the backward crossings up to the micro-state. -/
theorem sheet_eq_crossings {ω : E → ℤ} (hω : IsCut ω) (w : List (E × Bool)) (j : ℕ) :
    sheet ω w j = (forwardCrossings ω (w.take j) : ℤ) - backwardCrossings ω (w.take j) :=
  wordReading_eq_crossings hω _

/-- [definition] **A sub-cut**: every edge it cuts, the cut cuts too. -/
def SubCut (ω' ω : E → ℤ) : Prop := ∀ e, ω' e = 1 → ω e = 1

/-- A sub-cut's crossing ticks are among the cut's. -/
theorem crossingTicks_subset_of_subCut {ω ω' : E → ℤ} (hω' : IsCut ω') (h : SubCut ω' ω) :
    ∀ w : List (E × Bool), crossingTicks ω' w ⊆ crossingTicks ω w
  | [] => by simp [crossingTicks]
  | s :: w => by
      intro t ht
      simp only [crossingTicks, mem_union, mem_map] at ht ⊢
      rcases ht with ht | ⟨t', ht', he⟩
      · left
        split_ifs at ht with h0
        · simp at ht
        · have h1 : ω s.1 ≠ 0 := by
            rcases hω' s.1 with h' | h'
            · exact absurd h' h0
            · rw [h s.1 h']; norm_num
          simpa [h1] using ht
      · exact Or.inr ⟨t', crossingTicks_subset_of_subCut hω' h w ht', he⟩

/-- **Epochs coarsen under every sub-cut**, on every word. -/
theorem epochs_coarsen {ω ω' : E → ℤ} (hω' : IsCut ω') (h : SubCut ω' ω) (w : List (E × Bool)) (j : ℕ) :
    epochOf (crossingTicks ω' w) j = coarsen (crossingTicks ω w) (crossingTicks ω' w) (epochOf (crossingTicks ω w) j) :=
  epochOf_coarse (crossingTicks_subset_of_subCut hω' h w) j

/-! ## 2. When sheets coarsen -/

/-- [definition] **Sheets coarsen along a word**: micro-states on one fine sheet lie on one coarse sheet. -/
def SheetsCoarsen (ω ω' : E → ℤ) (w : List (E × Bool)) : Prop :=
  ∀ i j, i ≤ w.length → j ≤ w.length → sheet ω w i = sheet ω w j → sheet ω' w i = sheet ω' w j

/-- Sheets coarsen exactly when the coarse sheet is a function of the fine sheet. -/
theorem sheetsCoarsen_iff_exists (ω ω' : E → ℤ) (w : List (E × Bool)) :
    SheetsCoarsen ω ω' w ↔ ∃ f : ℤ → ℤ, ∀ j ≤ w.length, sheet ω' w j = f (sheet ω w j) := by
  classical
  constructor
  · intro h
    refine ⟨fun s => if hs : ∃ j, j ≤ w.length ∧ sheet ω w j = s then sheet ω' w hs.choose else 0, ?_⟩
    intro j hj
    have hs : ∃ i, i ≤ w.length ∧ sheet ω w i = sheet ω w j := ⟨j, hj, rfl⟩
    simp only [hs, dite_true]
    exact h _ _ hj hs.choose_spec.1 hs.choose_spec.2.symm
  · rintro ⟨f, hf⟩ i j hi hj he
    rw [hf i hi, hf j hj, he]

/-- [counterexample; formal-checked] **The refusal: sheets do not coarsen.** Two edges, the cut of both and the sub-cut
of the second; the word crosses the first forward and the second back. Micro-states `0` and `2` share the fine sheet
`0` while their coarse sheets are `0` and `−1`; the epochs still coarsen, by `0 ↦ 0, 1 ↦ 0, 2 ↦ 1`. -/
theorem sheets_do_not_coarsen :
    let ω : Fin 2 → ℤ := fun _ => 1
    let ω' : Fin 2 → ℤ := fun e => if e = 1 then 1 else 0
    let w : List (Fin 2 × Bool) := [(0, true), (1, false)]
    IsCut ω ∧ IsCut ω' ∧ SubCut ω' ω ∧
      sheet ω w 0 = 0 ∧ sheet ω w 2 = 0 ∧ sheet ω' w 0 = 0 ∧ sheet ω' w 2 = -1 ∧
      ¬ SheetsCoarsen ω ω' w ∧
      (coarsen (crossingTicks ω w) (crossingTicks ω' w) 0 = 0 ∧
        coarsen (crossingTicks ω w) (crossingTicks ω' w) 1 = 0 ∧
        coarsen (crossingTicks ω w) (crossingTicks ω' w) 2 = 1) := by
  intro ω ω' w
  have h0 : sheet ω w 0 = 0 := by simp [sheet, ω, w]
  have h2 : sheet ω w 2 = 0 := by simp [sheet, wordReading, stepReading, ω, w]
  have h0' : sheet ω' w 0 = 0 := by simp [sheet, ω', w]
  have h2' : sheet ω' w 2 = -1 := by simp [sheet, wordReading, stepReading, ω', w]
  refine ⟨fun _ => Or.inr rfl, fun e => ?_, fun e _ => rfl, h0, h2, h0', h2', ?_, ?_⟩
  · by_cases he : e = 1 <;> simp [ω', he]
  · intro h
    have := h 0 2 (by simp [w]) (by simp [w]) (by rw [h0, h2])
    rw [h0', h2'] at this
    norm_num at this
  · simp [coarsen, crossingTicks, epochOf, ω, ω', w]
    decide

/-- On a word that never crosses the cut back, each step adds `0` or `1` to the sheet. -/
private theorem wordReading_nonneg {ω : E → ℤ} (hω : IsCut ω) :
    ∀ m : List (E × Bool), (∀ s ∈ m, s.2 = false → ω s.1 = 0) → 0 ≤ wordReading ω m
  | [] => fun _ => by simp
  | s :: m => fun hm => by
      rw [wordReading_cons]
      have hs : 0 ≤ stepReading ω s := by
        rcases s with ⟨e, b⟩
        cases b
        · simp [stepReading, hm (e, false) (by simp) rfl]
        · rcases hω e with h | h <;> simp [stepReading, h]
      exact add_nonneg hs (wordReading_nonneg hω m fun t ht => hm t (List.mem_cons_of_mem _ ht))

/-- A stretch that never crosses the cut back and leaves the fine sheet where it was crosses no sub-cut. -/
private theorem subCut_reading_zero {ω ω' : E → ℤ} (hω : IsCut ω) (hω' : IsCut ω') (h : SubCut ω' ω) :
    ∀ m : List (E × Bool), (∀ s ∈ m, s.2 = false → ω s.1 = 0) → wordReading ω m = 0 → wordReading ω' m = 0
  | [] => fun _ _ => by simp
  | s :: m => fun hm hz => by
      rw [wordReading_cons] at hz ⊢
      have hrest := wordReading_nonneg hω m fun t ht => hm t (List.mem_cons_of_mem _ ht)
      rcases s with ⟨e, b⟩
      have hωe : ω e = 0 := by
        cases b
        · exact hm (e, false) (by simp) rfl
        · rcases hω e with h0 | h1
          · exact h0
          · simp [stepReading, h1] at hz; omega
      have hω'e : ω' e = 0 := by
        rcases hω' e with h0 | h1
        · exact h0
        · rw [h e h1] at hωe; norm_num at hωe
      have hstep : stepReading ω (e, b) = 0 := by cases b <;> simp [stepReading, hωe]
      rw [hstep, zero_add] at hz
      have hstep' : stepReading ω' (e, b) = 0 := by cases b <;> simp [stepReading, hω'e]
      rw [hstep', zero_add]
      exact subCut_reading_zero hω hω' h m (fun t ht => hm t (List.mem_cons_of_mem _ ht)) hz

/-- The sheet at `j ≥ i` is the sheet at `i` plus the reading of the steps between. -/
private theorem sheet_split (ω : E → ℤ) (w : List (E × Bool)) {i j : ℕ} (hij : i ≤ j) :
    sheet ω w j = sheet ω w i + wordReading ω ((w.take j).drop i) := by
  unfold sheet
  conv_lhs => rw [← List.take_append_drop i (w.take j)]
  rw [wordReading_append, List.take_take, min_eq_left hij]

/-- **Sheets coarsen where nothing crosses back**: if no step crosses the fine cut against its orientation, every
sub-cut's sheet is a function of the fine sheet. -/
theorem sheetsCoarsen_of_forward {ω ω' : E → ℤ} (hω : IsCut ω) (hω' : IsCut ω') (h : SubCut ω' ω)
    (w : List (E × Bool)) (hw : ∀ s ∈ w, s.2 = false → ω s.1 = 0) : SheetsCoarsen ω ω' w := by
  have key : ∀ i j, i ≤ j → sheet ω w i = sheet ω w j → sheet ω' w i = sheet ω' w j := by
    intro i j hij he
    have hm : ∀ s ∈ (w.take j).drop i, s.2 = false → ω s.1 = 0 :=
      fun s hs => hw s (List.mem_of_mem_take (List.mem_of_mem_drop hs))
    rw [sheet_split ω w hij] at he
    rw [sheet_split ω' w hij, subCut_reading_zero hω hω' h _ hm (by linarith), add_zero]
  intro i j _ _ he
  rcases le_total i j with hij | hji
  · exact key i j hij he
  · exact (key j i hji he.symm).symm

end Holonics.Aeon.Clock.SheetCoarsening
