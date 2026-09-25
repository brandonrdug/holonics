import Holonics.Aeon.Clock.Winding
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Epochs: an aeon divided at a receiver's section, and the refinement tower

[definition] `docs/ELEMENTARY_OBJECTS.md` §12 and the aeon record ("epoch"). A receiver ticks when
the motion arrives on its section `Σ_R`; the ticks cut an aeon of `N` micro-steps into
**epochs**. Here an aeon's micro-steps are `0, …, N − 1`, the ticks are arrival micro-states, and
the epoch of a micro-step is the number of ticks at or before it (`epochOf`); epoch `k` is its
fibre (`epoch`). A **certified section** has its ticks strictly inside the aeon
(`CertifiedSection`). A section read from the motion by a Boolean mark ticks at the arrivals
(`arrivals`); it is **transversal** when the motion never lingers on it (`Transversal`), as the
parametron ring's section is for `d ≥ 2`.

[proved-derived; formal-checked] What is proved.

1. **Epochs partition the aeon.** Every micro-step lies in its epoch, distinct epochs are disjoint,
   and each epoch is an interval (`epoch_exhaustive`, `epoch_disjoint`, `epoch_contiguous`); the
   epoch advances by one exactly at a tick (`epochOf_succ`). Under a certified section the aeon has
   exactly `#ticks + 1` nonempty epochs (`epochs_attained`, `epoch_count`).
2. **Coarsening by a sub-section, and the tower.** When the coarse ticks are among the fine ones
   (as a transversal section's sub-section's are: `arrivals_subset_of_subsection`), the coarse
   epoch is a function `coarsen` of the fine epoch (`epochOf_coarse`); coarsening composes along a
   tower `Σ'' ⊆ Σ' ⊆ Σ` (`coarsen_tower`); refining a coarse epoch into the fine epochs it contains
   and merging them returns it (`coarse_epoch_is_union_of_fine`); and the fine epochs are
   distributed over the coarse ones (`fine_epochs_distribute_over_coarse`). Kac's mean first-return
   ratio for these towers belongs to `Aeon/Production`.
3. **Count is flux.** On the parametron ring of a clock passage `n/d`, the arrivals on the section
   over an aeon of `n·k` micro-steps from residue `r < d` number `targetTicks r k`, which for
   `d ≥ 2` are the owner's crossing records and equal the whole windings of the reading counted
   from the last crossing (`ring_count_is_flux`, over `Objects/Parametron.ownerCrossings_eq_targetTicks`).
   A crossing population read without its section is not the object: in
   `Geometry/WindingLedger.theApertureMovesThePopulationAndNotTheNet` the population moves with
   the aperture while the net winding stays; a transversal section on a monotone ring fixes the
   count to the windings.
4. **The Odometer is a tower of epochs.** With ticks at the multiples of `n`, the epoch of a
   micro-step is its `PhaseCarry.winding` (`epochOf_digitTicks`), the Odometer's upper digit counts
   epochs (`odometer_counts_epochs`), and coarsening to the multiples of `n·m` is the carry
   `winding m` (`odometer_tower`).

5. **Epochs of an aeon, and count as oriented flux.** A receiver's section on the parametric
   complex is a **cut clock**: a closed `0/1` cochain (`CutClock`), a `Clock K ℤ` reading `+1` on
   each edge that crosses the section. Along an aeon its reading is the **oriented** crossing
   count, forward crossings minus backward crossings (`reading_eq_crossings`), so crossing counts
   are readings and add under concatenation (`crossings_concat`, `Reading.reading_concat`), are
   homotopy invariant and reverse sign under reversal. The aeon's crossing steps are its ticks
   (`crossingTicks`), a certified section of its occurrence sequence (`aeonSection`), cutting it
   into `#crossings + 1` epochs (`aeon_epochs_attained`). On the lift of the clock torus the
   section `{x | d ∣ x i}` of navigator `i` is the exact clock of the winding potential
   `x ↦ ⌊x i / d⌋` (`sectionForm_eq_exactForm`, `sectionClock`), so **the signed crossing count
   is the change of whole windings** (`signed_count_is_flux`), for any `±1` walk; a monotone aeon
   has no backward crossing and its tick count is that change (`monotone_count_is_flux`), of which
   the parametron ring's count above is the owner's instance.

[counterexample; formal-checked] The hypotheses are load-bearing.
- **An uncertified declared tick list does not partition.** Declared ticks `[3, 1]` on an aeon of
  four micro-steps give intervals `[0, 3)` and `[1, 4)` that overlap; the certified tick set
  `{1, 3}` gives the partition `{0}, {1, 2}, {3}` (`declared_ticks_do_not_partition`).
- **A tick outside the aeon leaves an empty epoch** (`tick_outside_leaves_an_empty_epoch`).
- **A non-transversal section is not a flux counter.** At `d = 1` every ring state is on the
  section: the ring has no crossing, while the reading completes `r + N` whole windings
  (`nontransversal_count_is_not_flux`).
- **Unsigned arrivals are not the flux of a walk that turns back.** On the one-navigator lift with
  `d = 2`, the aeon `0 → 1 → 2 → 1 → 2` crosses the section forward twice and backward once: it
  has three crossing ticks while its signed reading, the change of whole windings, is `1`
  (`unsigned_count_is_not_flux`).
- **A non-transversal section does not coarsen.** When the motion lingers on `Σ` for two
  micro-states, a sub-section's arrival is not an arrival on `Σ`, and two micro-steps of one fine
  epoch lie in different coarse epochs (`nontransversal_subsection_does_not_coarsen`).

No `axiom`, no `sorry`, no `native_decide`.
-/

set_option linter.dupNamespace false

namespace Holonics.Aeon.Clock.Epoch

open Finset
open Holonics.Geometry
open Holonics.Geometry.HolonicClockedPantographicSwing

/-! ## 1. Ticks partition an aeon into epochs -/

/-- [definition] **The epoch of micro-step `j`** at a receiver whose section is reached at the
micro-states `ticks`: the number of ticks at or before `j`. -/
def epochOf (ticks : Finset ℕ) (j : ℕ) : ℕ := #(ticks.filter (· ≤ j))

/-- [definition] **Epoch `k`** of an aeon of `N` micro-steps: the micro-steps whose epoch is `k`. -/
def epoch (ticks : Finset ℕ) (N k : ℕ) : Finset ℕ := (range N).filter (fun j => epochOf ticks j = k)

theorem mem_epoch {ticks : Finset ℕ} {N k j : ℕ} :
    j ∈ epoch ticks N k ↔ j < N ∧ epochOf ticks j = k := by
  simp [epoch]

/-- [proved-derived; formal-checked] Every micro-step of the aeon lies in its epoch. -/
theorem epoch_exhaustive (ticks : Finset ℕ) {N j : ℕ} (hj : j < N) :
    j ∈ epoch ticks N (epochOf ticks j) :=
  mem_epoch.mpr ⟨hj, rfl⟩

/-- [proved-derived; formal-checked] Distinct epochs are disjoint. -/
theorem epoch_disjoint (ticks : Finset ℕ) (N : ℕ) {k k' : ℕ} (hk : k ≠ k') :
    Disjoint (epoch ticks N k) (epoch ticks N k') := by
  rw [epoch, epoch, disjoint_filter]
  intro j _ h1 h2
  exact hk (h1.symm.trans h2)

theorem epochOf_mono (ticks : Finset ℕ) {i j : ℕ} (h : i ≤ j) : epochOf ticks i ≤ epochOf ticks j :=
  card_le_card (monotone_filter_right _ (fun _ _ hx => le_trans hx h))

/-- [proved-derived; formal-checked] Each epoch is an interval of micro-steps. -/
theorem epoch_contiguous (ticks : Finset ℕ) {N k i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l)
    (hi : i ∈ epoch ticks N k) (hl : l ∈ epoch ticks N k) : j ∈ epoch ticks N k := by
  rw [mem_epoch] at hi hl ⊢
  have h1 := epochOf_mono ticks hij
  have h2 := epochOf_mono ticks hjl
  exact ⟨lt_of_le_of_lt hjl hl.1, by omega⟩

/-- [proved-derived; formal-checked] **The epoch advances by one exactly at a tick.** -/
theorem epochOf_succ (ticks : Finset ℕ) (j : ℕ) :
    epochOf ticks (j + 1) = epochOf ticks j + if j + 1 ∈ ticks then 1 else 0 := by
  unfold epochOf
  have hsplit : ticks.filter (· ≤ j + 1) = ticks.filter (· ≤ j) ∪ ticks.filter (· = j + 1) := by
    ext x
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hx, h⟩
      rcases Nat.lt_or_ge j x with hlt | hge
      · exact Or.inr ⟨hx, by omega⟩
      · exact Or.inl ⟨hx, hge⟩
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · exact ⟨hx, by omega⟩
      · exact ⟨hx, by omega⟩
  have hdisj : Disjoint (ticks.filter (· ≤ j)) (ticks.filter (· = j + 1)) := by
    rw [disjoint_filter]
    intro x _ h1 h2
    omega
  rw [hsplit, card_union_of_disjoint hdisj, filter_eq']
  split_ifs <;> simp

/-- [proved-derived; formal-checked] A tick strictly after `j` has a strictly later epoch. -/
theorem epochOf_lt_of_mem {ticks : Finset ℕ} {j t : ℕ} (ht : t ∈ ticks) (hjt : j < t) :
    epochOf ticks j < epochOf ticks t := by
  refine card_lt_card ⟨monotone_filter_right _ (fun _ _ hx => le_trans hx hjt.le), fun h => ?_⟩
  have : t ∈ ticks.filter (· ≤ j) := h (mem_filter.mpr ⟨ht, le_rfl⟩)
  have := (mem_filter.mp this).2
  omega

/-- [definition] **A certified section** along an aeon of `N` micro-steps: its ticks lie strictly
inside the aeon. -/
structure CertifiedSection (N : ℕ) where
  ticks : Finset ℕ
  inside : ticks ⊆ Ioo 0 N

/-- A discrete intermediate value law: a count starting at `0` that advances by at most one per
step attains every value up to its last. -/
private theorem attains_every_value (f : ℕ → ℕ) (h0 : f 0 = 0) (hstep : ∀ j, f (j + 1) ≤ f j + 1) :
    ∀ m k, k ≤ f m → ∃ j ≤ m, f j = k := by
  intro m
  induction m with
  | zero => intro k hk; exact ⟨0, le_rfl, by omega⟩
  | succ m ih =>
    intro k hk
    by_cases hkm : k ≤ f m
    · obtain ⟨j, hj, hfj⟩ := ih k hkm
      exact ⟨j, by omega, hfj⟩
    · have := hstep m
      exact ⟨m + 1, le_rfl, by omega⟩

/-- [proved-derived; formal-checked] **A certified section cuts the aeon into `#ticks + 1`
nonempty epochs**: the epochs attained by the micro-steps are exactly `0, …, #ticks`. -/
theorem epochs_attained {N : ℕ} (S : CertifiedSection N) (hN : 0 < N) :
    (range N).image (epochOf S.ticks) = range (#S.ticks + 1) := by
  ext k
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨j, _, rfl⟩
    exact Nat.lt_succ_of_le (card_filter_le _ _)
  · intro hk
    have h0 : epochOf S.ticks 0 = 0 := by
      rw [epochOf, card_eq_zero, filter_eq_empty_iff]
      intro t ht htle
      have := mem_Ioo.mp (S.inside ht)
      omega
    have hstep : ∀ j, epochOf S.ticks (j + 1) ≤ epochOf S.ticks j + 1 := by
      intro j
      rw [epochOf_succ]
      split_ifs <;> omega
    have hlast : epochOf S.ticks (N - 1) = #S.ticks := by
      rw [epochOf, filter_true_of_mem]
      intro t ht
      have := mem_Ioo.mp (S.inside ht)
      omega
    obtain ⟨j, hj, hfj⟩ := attains_every_value _ h0 hstep (N - 1) k (by omega)
    exact ⟨j, by omega, hfj⟩

/-- [proved-derived; formal-checked] The number of epochs of a certified section is its tick count
plus one. -/
theorem epoch_count {N : ℕ} (S : CertifiedSection N) (hN : 0 < N) :
    #((range N).image (epochOf S.ticks)) = #S.ticks + 1 := by
  rw [epochs_attained S hN, card_range]

/-! ## 2. Sections read from the motion -/

/-- [definition] The arrivals on a section read by `mark` over an aeon of `N` micro-steps: the
interior micro-states on the section whose predecessor is not. -/
def arrivals (mark : ℕ → Bool) (N : ℕ) : Finset ℕ :=
  (Ioo 0 N).filter (fun j => mark j = true ∧ mark (j - 1) = false)

/-- [definition] The certified section of a mark: its arrivals, which lie inside the aeon. -/
def sectionOf (mark : ℕ → Bool) (N : ℕ) : CertifiedSection N :=
  ⟨arrivals mark N, filter_subset _ _⟩

/-- [definition] A section is **transversal** when the motion never stays on it for two
consecutive micro-states. -/
def Transversal (mark : ℕ → Bool) : Prop := ∀ j, mark j = true → mark (j + 1) = false

/-- [proved-derived; formal-checked] On a transversal section every interior visit is an
arrival. -/
theorem arrivals_of_transversal {mark : ℕ → Bool} (h : Transversal mark) (N : ℕ) :
    arrivals mark N = (Ioo 0 N).filter (fun j => mark j = true) := by
  apply filter_congr
  intro j hj
  have hj0 := (mem_Ioo.mp hj).1
  constructor
  · exact fun h' => h'.1
  · intro hm
    refine ⟨hm, ?_⟩
    cases hprev : mark (j - 1)
    · rfl
    · have := h (j - 1) hprev
      rw [show j - 1 + 1 = j by omega, hm] at this
      exact absurd this (by decide)

/-- [proved-derived; formal-checked] **A sub-section of a transversal section ticks among its
ticks.** -/
theorem arrivals_subset_of_subsection {mark mark' : ℕ → Bool} (h : Transversal mark)
    (hsub : ∀ j, mark' j = true → mark j = true) (N : ℕ) :
    arrivals mark' N ⊆ arrivals mark N := by
  have h' : Transversal mark' := by
    intro j hj
    cases hn : mark' (j + 1)
    · rfl
    · have := h j (hsub j hj)
      rw [hsub _ hn] at this
      exact absurd this (by decide)
  rw [arrivals_of_transversal h, arrivals_of_transversal h']
  exact monotone_filter_right _ (fun j _ hj => hsub j hj)

/-! ## 3. Coarsening by a sub-section, and the tower -/

/-- [definition] **Coarsening**: the coarse epoch of fine epoch `k`, the number of coarse ticks
whose fine epoch is at most `k`. -/
def coarsen (fine coarse : Finset ℕ) (k : ℕ) : ℕ := #(coarse.filter (fun t => epochOf fine t ≤ k))

/-- [proved-derived; formal-checked] **The coarse epoch is a function of the fine epoch** when the
coarse ticks are among the fine ones. -/
theorem epochOf_coarse {fine coarse : Finset ℕ} (h : coarse ⊆ fine) (j : ℕ) :
    epochOf coarse j = coarsen fine coarse (epochOf fine j) := by
  unfold epochOf coarsen
  congr 1
  apply filter_congr
  intro t ht
  constructor
  · exact fun htj => epochOf_mono fine htj
  · intro hle
    by_contra hjt
    have := epochOf_lt_of_mem (h ht) (not_le.mp hjt)
    exact absurd hle (not_le.mpr this)

/-- [proved-derived; formal-checked] Micro-steps sharing a fine epoch share the coarse epoch. -/
theorem coarse_epoch_of_fine_epoch {fine coarse : Finset ℕ} (h : coarse ⊆ fine) {i j : ℕ}
    (hij : epochOf fine i = epochOf fine j) : epochOf coarse i = epochOf coarse j := by
  rw [epochOf_coarse h, epochOf_coarse h, hij]

/-- [proved-derived; formal-checked] **Coarsening composes along a tower** `Σ'' ⊆ Σ' ⊆ Σ`: the
scale square commutes. -/
theorem coarsen_tower {fine mid coarse : Finset ℕ} (h₁ : mid ⊆ fine) (h₂ : coarse ⊆ mid)
    (j : ℕ) :
    coarsen mid coarse (coarsen fine mid (epochOf fine j)) =
      coarsen fine coarse (epochOf fine j) := by
  rw [← epochOf_coarse h₁, ← epochOf_coarse h₂, ← epochOf_coarse (h₂.trans h₁)]

/-- [proved-derived; formal-checked] **Refinement then coarsening is the identity on coarse
epochs.** A coarse epoch is the union of the fine epochs that coarsen to it. -/
theorem coarse_epoch_is_union_of_fine {fine coarse : Finset ℕ} (h : coarse ⊆ fine) (N k' : ℕ) :
    epoch coarse N k' =
      ((range (#fine + 1)).filter (fun k => coarsen fine coarse k = k')).biUnion
        (epoch fine N) := by
  ext j
  simp only [mem_biUnion, mem_filter, mem_range, mem_epoch]
  constructor
  · rintro ⟨hj, hk⟩
    exact ⟨epochOf fine j, ⟨Nat.lt_succ_of_le (card_filter_le _ _),
      (epochOf_coarse h j).symm.trans hk⟩, hj, rfl⟩
  · rintro ⟨k, ⟨_, hk⟩, hj, rfl⟩
    exact ⟨hj, (epochOf_coarse h j).trans hk⟩

/-- [proved-derived; formal-checked] **The fine epochs distribute over the coarse ones.** The
`#fine + 1` fine epoch indices are the sum, over the `#coarse + 1` coarse epochs, of the fine
epochs each contains; the fine ticks are the coarse ticks and the ticks of `Σ ∖ Σ'`. -/
theorem fine_epochs_distribute_over_coarse {fine coarse : Finset ℕ} (h : coarse ⊆ fine) :
    #fine + 1 = ∑ k' ∈ range (#coarse + 1),
        #((range (#fine + 1)).filter (fun k => coarsen fine coarse k = k')) ∧
      #fine = #coarse + #(fine \ coarse) := by
  refine ⟨?_, ?_⟩
  · rw [← card_range (#fine + 1)]
    rw [card_range]
    have := card_eq_sum_card_fiberwise (f := coarsen fine coarse) (s := range (#fine + 1))
      (t := range (#coarse + 1)) (by
        intro k _
        simp only [coe_range, Set.mem_Iio]
        exact Nat.lt_succ_of_le (card_filter_le _ _))
    rwa [card_range] at this
  · rw [card_sdiff_of_subset h]
    have := card_le_card h
    omega

/-! ## 4. Count is flux: the parametron ring -/

section Ring

open Holonics.Objects.Parametron

variable {ClockAddress : Type*}

/-- [proved-derived; formal-checked] The ring's section is transversal for `d ≥ 2`. -/
theorem ring_section_transversal (passage : RationalClockPassage ClockAddress)
    (hd : 2 ≤ passage.denominator) (r : ℕ) :
    Transversal (fun j => (ringOscillator passage).sectionMark (r + j)) := by
  intro j hj
  simp only [ringOscillator, decide_eq_true_eq] at hj
  simp only [ringOscillator, decide_eq_false_iff_not]
  intro h
  have h1 : (r + (j + 1)) % passage.denominator = ((r + j) % passage.denominator + 1) %
      passage.denominator := by
    rw [← Nat.add_assoc, Nat.add_mod (r + j) 1, Nat.one_mod_eq_one.mpr (by omega)]
  rw [hj, zero_add, Nat.one_mod_eq_one.mpr (by omega)] at h1
  omega

/-- [proved-derived; formal-checked] The arrivals on the ring's section over an aeon of `N`
micro-steps, endpoint included, are the owner's ring crossings. -/
theorem ring_arrivals_eq_ringCrossings (passage : RationalClockPassage ClockAddress) (r N : ℕ) :
    #((Ioc 0 N).filter (fun j => (ringOscillator passage).sectionMark (r + j) = true)) =
      ringCrossings passage.denominator r N := by
  unfold ringCrossings
  refine card_nbij' (fun j => j - 1) (fun j => j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [coe_filter, mem_Ioc, ringOscillator, decide_eq_true_eq, Set.mem_ofPred_eq] at hj
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    refine ⟨by omega, ?_⟩
    rw [show r + (j - 1) + 1 = r + j by omega]
    exact hj.2
  · intro j hj
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hj
    simp only [coe_filter, mem_Ioc, ringOscillator, decide_eq_true_eq, Set.mem_ofPred_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [← Nat.add_assoc]
    exact hj.2
  · intro j hj
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hj
    simp only
    omega
  · intro j _
    simp

/-- [proved-derived; formal-checked] **Count is flux.** Over the aeon of `k` source ticks (`n·k`
micro-steps) from residue `r < d`, the arrivals on the ring's section number `targetTicks r k`,
the whole windings of the reading counted from the last crossing; for `d ≥ 2` they are the owner's
crossing records. -/
theorem ring_count_is_flux (passage : RationalClockPassage ClockAddress) (r k : ℕ)
    (hr : r < passage.denominator) :
    #((Ioc 0 (passage.numerator * k)).filter
        (fun j => (ringOscillator passage).sectionMark (r + j) = true)) =
        passage.targetTicks r k ∧
      (#((Ioc 0 (passage.numerator * k)).filter
        (fun j => (ringOscillator passage).sectionMark (r + j) = true)) : ℤ) =
        Winding.windings (((r + passage.numerator * k : ℕ) : ℚ) / passage.denominator) ∧
      (2 ≤ passage.denominator →
        #((Ioc 0 (passage.numerator * k)).filter
          (fun j => (ringOscillator passage).sectionMark (r + j) = true)) =
          ownerCrossings passage r (passage.numerator * k)) := by
  have hcount : #((Ioc 0 (passage.numerator * k)).filter
      (fun j => (ringOscillator passage).sectionMark (r + j) = true)) = passage.targetTicks r k := by
    rw [ring_arrivals_eq_ringCrossings, ringCrossings_eq _ _ hr]
    rfl
  refine ⟨hcount, ?_, fun hd => ?_⟩
  · rw [hcount, Winding.windings_of_microsteps]
    rfl
  · rw [hcount, (ownerCrossings_eq_targetTicks passage hd r k hr).1]

/-- [counterexample; formal-checked] **A non-transversal section is not a flux counter.** At
`d = 1` every ring state lies on the section: the section is not transversal, the ring has no
crossing at all (`no_crossing_of_denominator_one`), yet the reading completes `r + N` whole
windings. -/
theorem nontransversal_count_is_not_flux (passage : RationalClockPassage ClockAddress)
    (hd : passage.denominator = 1) (r N : ℕ) :
    ¬ Transversal (fun j => (ringOscillator passage).sectionMark (r + j)) ∧
      ownerCrossings passage r N = 0 ∧
      PhaseCarry.winding passage.denominator (r + N) = r + N := by
  refine ⟨fun h => ?_, ?_, by simp [PhaseCarry.winding, hd]⟩
  · have := h 0 (by simp [ringOscillator, hd, Nat.mod_one])
    simp [ringOscillator, hd, Nat.mod_one] at this
  · classical
    unfold ownerCrossings
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro j - ⟨c, -⟩
    exact no_crossing_of_denominator_one passage hd c

end Ring

/-! ## 5. The Odometer is a tower of epochs -/

/-- [definition] The ticks of a digit clock of base `n` inside an aeon of `N` micro-steps: the
multiples of `n`. -/
def digitTicks (n N : ℕ) : Finset ℕ := (Ioo 0 N).filter (n ∣ ·)

/-- [proved-derived; formal-checked] **The epoch of a digit clock is the winding.** -/
theorem epochOf_digitTicks (n N j : ℕ) (hj : j < N) :
    epochOf (digitTicks n N) j = PhaseCarry.winding n j := by
  have hset : (digitTicks n N).filter (· ≤ j) = (Ioc 0 j).filter (n ∣ ·) := by
    ext x
    simp only [digitTicks, mem_filter, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h0, _⟩, hd⟩, hx⟩
      exact ⟨⟨h0, hx⟩, hd⟩
    · rintro ⟨⟨h0, hx⟩, hd⟩
      exact ⟨⟨⟨h0, by omega⟩, hd⟩, hx⟩
  rw [epochOf, hset, Nat.Ioc_filter_dvd_card_eq_div]
  rfl

theorem digitTicks_subset (n m N : ℕ) : digitTicks (n * m) N ⊆ digitTicks n N :=
  monotone_filter_right _ (fun _ _ hx => (dvd_mul_right n m).trans hx)

/-- [proved-derived; formal-checked] **The Odometer's upper digit counts epochs**, and its lower
digit is the position inside the epoch. -/
theorem odometer_counts_epochs (n N j : ℕ) (hn : 0 < n) (hj : j < N) :
    ((PhaseCarry.odometer n)^[j] (0, 0)).2 = epochOf (digitTicks n N) j ∧
      ((PhaseCarry.odometer n)^[j] (0, 0)).1 = PhaseCarry.phase n j := by
  rw [PhaseCarry.odometer_iterate n 0 0 j hn hn, epochOf_digitTicks n N j hj]
  simp [PhaseCarry.winding, PhaseCarry.phase]

/-- [proved-derived; formal-checked] **Coarsening a digit clock is the carry.** Passing from the
multiples of `n` to the multiples of `n·m` sends fine epoch `winding n j` to coarse epoch
`winding m (winding n j) = winding (n m) j`, and this is the tower's `coarsen`. -/
theorem odometer_tower (n m N j : ℕ) (hj : j < N) :
    epochOf (digitTicks (n * m) N) j = PhaseCarry.winding m (epochOf (digitTicks n N) j) ∧
      coarsen (digitTicks n N) (digitTicks (n * m) N) (epochOf (digitTicks n N) j) =
        PhaseCarry.winding m (epochOf (digitTicks n N) j) := by
  have h1 : epochOf (digitTicks (n * m) N) j = PhaseCarry.winding m (epochOf (digitTicks n N) j) := by
    rw [epochOf_digitTicks _ _ _ hj, epochOf_digitTicks _ _ _ hj]
    exact (Nat.div_div_eq_div_mul j n m).symm
  refine ⟨h1, ?_⟩
  rw [← epochOf_coarse (digitTicks_subset n m N), h1]

/-! ## 6. The hypotheses are load-bearing -/

/-- [definition] The epochs of a declared tick list: the intervals between consecutive entries of
`0 :: ticks ++ [N]`. A declared list is not a certified section. -/
def declaredEpoch (ts : List ℕ) (N i : ℕ) : Finset ℕ :=
  Ico ((0 :: ts).getD i 0) ((ts ++ [N]).getD i N)

/-- [counterexample; formal-checked] **An uncertified declared tick list does not partition.** The
declared ticks `[3, 1]` on an aeon of four micro-steps give overlapping intervals `[0, 3)` and
`[1, 4)`; the certified tick set `{1, 3}` partitions the same aeon into `{0}, {1, 2}, {3}`, and
the sorted declaration `[1, 3]` agrees with it. -/
theorem declared_ticks_do_not_partition :
    ¬ Disjoint (declaredEpoch [3, 1] 4 0) (declaredEpoch [3, 1] 4 2) ∧
      epoch {1, 3} 4 0 = {0} ∧ epoch {1, 3} 4 1 = {1, 2} ∧ epoch {1, 3} 4 2 = {3} ∧
      (∀ i < 3, declaredEpoch [1, 3] 4 i = epoch {1, 3} 4 i) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  decide

/-- [counterexample; formal-checked] **A tick outside the aeon leaves an empty epoch.** With the
tick at micro-state `0`, epoch `0` of an aeon of two micro-steps is empty and only one epoch is
attained, not `#ticks + 1 = 2`. -/
theorem tick_outside_leaves_an_empty_epoch :
    epoch {0} 2 0 = ∅ ∧ #((range 2).image (epochOf {0})) = 1 := by
  decide

/-- [definition] A section on which the motion lingers for micro-states `1` and `2`. -/
def lingerMark (j : ℕ) : Bool := decide (j = 1 ∨ j = 2)

/-- [definition] Its sub-section: micro-state `2` only. -/
def lingerSub (j : ℕ) : Bool := decide (j = 2)

/-- [counterexample; formal-checked] **A non-transversal section does not coarsen.** The
sub-section's arrival at `2` is not an arrival on the section, and micro-steps `1` and `2` share a
fine epoch but lie in different coarse epochs. -/
theorem nontransversal_subsection_does_not_coarsen :
    ¬ Transversal lingerMark ∧ (∀ j, lingerSub j = true → lingerMark j = true) ∧
      ¬ arrivals lingerSub 4 ⊆ arrivals lingerMark 4 ∧
      epochOf (arrivals lingerMark 4) 1 = epochOf (arrivals lingerMark 4) 2 ∧
      epochOf (arrivals lingerSub 4) 1 ≠ epochOf (arrivals lingerSub 4) 2 := by
  refine ⟨fun h => absurd (h 1 (by decide)) (by decide), ?_, by decide, by decide, by decide⟩
  intro j hj
  simp only [lingerSub, lingerMark, decide_eq_true_eq] at hj ⊢
  exact Or.inr hj

/-! ## 7. Epochs of an aeon: cut clocks and oriented crossings -/

section AeonEpochs

open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading Holonics.Aeon.Clock.Winding

variable {V E F : Type*} {K : ParametricComplex V E F}

/-- [definition] A **cut cochain** takes the values `0` and `1`: `1` on the edges that cross the
section. -/
def IsCut (ω : E → ℤ) : Prop := ∀ e, ω e = 0 ∨ ω e = 1

/-- [definition] **A cut clock**: a receiver's section as a closed cut cochain, a `Clock K ℤ` whose
readings count crossings. -/
structure CutClock (K : ParametricComplex V E F) where
  clock : Clock K ℤ
  isCut : IsCut clock.form

/-- [definition] The steps of a word that cross the section along an edge's orientation. -/
def forwardCrossings (ω : E → ℤ) (w : List (E × Bool)) : ℕ :=
  (w.filter (fun s => s.2 && decide (ω s.1 = 1))).length

/-- [definition] The steps of a word that cross the section against an edge's orientation. -/
def backwardCrossings (ω : E → ℤ) (w : List (E × Bool)) : ℕ :=
  (w.filter (fun s => !s.2 && decide (ω s.1 = 1))).length

theorem forwardCrossings_append (ω : E → ℤ) (p q : List (E × Bool)) :
    forwardCrossings ω (p ++ q) = forwardCrossings ω p + forwardCrossings ω q := by
  simp [forwardCrossings, List.filter_append]

theorem backwardCrossings_append (ω : E → ℤ) (p q : List (E × Bool)) :
    backwardCrossings ω (p ++ q) = backwardCrossings ω p + backwardCrossings ω q := by
  simp [backwardCrossings, List.filter_append]

/-- [proved-derived; formal-checked] **A cut cochain reads oriented crossings**: the reading of a
word is its forward crossings minus its backward crossings. -/
theorem wordReading_eq_crossings {ω : E → ℤ} (hω : IsCut ω) (w : List (E × Bool)) :
    wordReading ω w = (forwardCrossings ω w : ℤ) - backwardCrossings ω w := by
  induction w with
  | nil => simp [forwardCrossings, backwardCrossings]
  | cons s w ih =>
    rw [wordReading_cons, ih]
    rcases s with ⟨e, b⟩
    rcases hω e with h | h <;> cases b <;>
      simp [forwardCrossings, backwardCrossings, stepReading, h] <;> ring

/-- [proved-derived; formal-checked] **Count is oriented flux.** A cut clock reads an aeon as its
forward minus its backward crossings of the section. -/
theorem reading_eq_crossings (c : CutClock K) {u v : V} (γ : Aeon K u v) :
    reading c.clock γ =
      (forwardCrossings c.clock.form γ.steps : ℤ) - backwardCrossings c.clock.form γ.steps :=
  wordReading_eq_crossings c.isCut γ.steps

/-- [proved-derived; formal-checked] **Crossing counts add under concatenation** (the ℤ-valued
epoch cocycle of the record, `Reading.reading_concat`), and reversal exchanges forward and
backward crossings. -/
theorem crossings_concat (c : CutClock K) {u w v : V} (γ : Aeon K u w) (δ : Aeon K w v) :
    forwardCrossings c.clock.form (γ.concat δ).steps =
        forwardCrossings c.clock.form γ.steps + forwardCrossings c.clock.form δ.steps ∧
      backwardCrossings c.clock.form (γ.concat δ).steps =
        backwardCrossings c.clock.form γ.steps + backwardCrossings c.clock.form δ.steps ∧
      reading c.clock (γ.concat δ) = reading c.clock γ + reading c.clock δ ∧
      reading c.clock γ.reverse = -reading c.clock γ :=
  ⟨forwardCrossings_append _ _ _, backwardCrossings_append _ _ _, reading_concat _ _ _,
    reading_reverse _ _⟩

/-- [definition] **The ticks of a word at a section**: micro-state `j + 1` is a tick when step `j`
crosses the section. -/
def crossingTicks (ω : E → ℤ) : List (E × Bool) → Finset ℕ
  | [] => ∅
  | s :: w => (if ω s.1 = 0 then ∅ else {1}) ∪ (crossingTicks ω w).map (addRightEmbedding 1)

theorem crossingTicks_subset (ω : E → ℤ) :
    ∀ w : List (E × Bool), crossingTicks ω w ⊆ Ioo 0 (w.length + 1)
  | [] => by simp [crossingTicks]
  | s :: w => by
    intro t ht
    simp only [crossingTicks, mem_union, mem_map, addRightEmbedding_apply] at ht
    simp only [mem_Ioo, List.length_cons]
    rcases ht with ht | ⟨t', ht', rfl⟩
    · split_ifs at ht with h
      · simp at ht
      · simp only [mem_singleton] at ht; omega
    · have := mem_Ioo.mp (crossingTicks_subset ω w ht')
      omega

/-- [proved-derived; formal-checked] The ticks of a word are its crossings: their number is the
forward plus the backward crossings. -/
theorem card_crossingTicks {ω : E → ℤ} (hω : IsCut ω) :
    ∀ w : List (E × Bool), #(crossingTicks ω w) = forwardCrossings ω w + backwardCrossings ω w
  | [] => by simp [crossingTicks, forwardCrossings, backwardCrossings]
  | s :: w => by
    have hdisj : Disjoint (if ω s.1 = 0 then (∅ : Finset ℕ) else {1})
        ((crossingTicks ω w).map (addRightEmbedding 1)) := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      split_ifs at h1
      · simp at h1
      · simp only [mem_singleton] at h1
        subst h1
        obtain ⟨t', ht', he⟩ := mem_map.mp h2
        simp only [addRightEmbedding_apply] at he
        have := mem_Ioo.mp (crossingTicks_subset ω w ht')
        omega
    rw [crossingTicks, card_union_of_disjoint hdisj, card_map, card_crossingTicks hω w]
    rcases s with ⟨e, b⟩
    rcases hω e with h | h <;> cases b <;>
      simp [forwardCrossings, backwardCrossings, h] <;> omega

/-- [definition] **The epochs of an aeon at a receiver's section**: its crossing ticks, a certified
section of its `length + 1` occurrences. -/
def aeonSection (ω : E → ℤ) {u v : V} (γ : Aeon K u v) : CertifiedSection (γ.steps.length + 1) :=
  ⟨crossingTicks ω γ.steps, crossingTicks_subset ω γ.steps⟩

/-- [proved-derived; formal-checked] **An aeon is cut into one more epoch than it has crossings**
(`epochs_attained`), and the crossings are forward plus backward. -/
theorem aeon_epochs_attained (c : CutClock K) {u v : V} (γ : Aeon K u v) :
    (range (γ.steps.length + 1)).image (epochOf (aeonSection c.clock.form γ).ticks) =
        range (forwardCrossings c.clock.form γ.steps + backwardCrossings c.clock.form γ.steps + 1) := by
  rw [epochs_attained _ (Nat.succ_pos _)]
  simp only [aeonSection, card_crossingTicks c.isCut]

/-! ### The section of a navigator on the lift of the clock torus -/

variable {ι : Type*} [DecidableEq ι]

/-- [definition] The cut of navigator `i`'s section `{x | d ∣ x i}` on the lift: `1` on each
micro-step of `i` that arrives on it. -/
def sectionForm (i : ι) (d : ℕ) : (ι → ℤ) × ι → ℤ :=
  fun e => if e.2 = i ∧ (d : ℤ) ∣ e.1 i + 1 then 1 else 0

theorem sectionForm_isCut (i : ι) (d : ℕ) : IsCut (sectionForm i d) := by
  intro e
  unfold sectionForm
  split_ifs <;> simp

/-- A unit step of the numerator advances the quotient by one exactly at a multiple. -/
theorem add_one_ediv_sub_ediv {d : ℤ} (hd : 0 < d) (a : ℤ) :
    (a + 1) / d - a / d = if d ∣ a + 1 then 1 else 0 := by
  have hlo := (Int.ediv_eq_iff_of_pos hd).mp (rfl : a / d = a / d)
  split_ifs with h
  · obtain ⟨c, hc⟩ := h
    have h1 : (a + 1) / d = c := by rw [hc]; exact Int.mul_ediv_cancel_left c hd.ne'
    have h2 : a / d = c - 1 := by
      rw [Int.ediv_eq_iff_of_pos hd]
      constructor <;> nlinarith
    rw [h1, h2]; ring
  · have h1 : (a + 1) / d = a / d := by
      rw [Int.ediv_eq_iff_of_pos hd]
      refine ⟨by linarith [hlo.1], ?_⟩
      rcases lt_or_eq_of_le (show a + 1 ≤ a / d * d + d by linarith [hlo.2]) with hlt | heq
      · exact hlt
      · exact absurd ⟨a / d + 1, by rw [heq]; ring⟩ h
    rw [h1, sub_self]

/-- [proved-derived; formal-checked] **The section's cut is the exact form of the winding
potential** `x ↦ ⌊x i / d⌋`. -/
theorem sectionForm_eq_exactForm (i : ι) {d : ℕ} (hd : 0 < d) :
    sectionForm i d = exactForm (clockLift ι) (fun x => x i / (d : ℤ)) := by
  funext e
  rcases e with ⟨x, j⟩
  simp only [sectionForm, exactForm, clockLift]
  by_cases hj : j = i
  · subst hj
    rw [Pi.add_apply, Pi.single_eq_same, add_one_ediv_sub_ediv (by exact_mod_cast hd)]
    simp
  · rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hj), add_zero, sub_self]
    simp [hj]

/-- [definition] **The section clock** of navigator `i` with period `d`. -/
def sectionClock (i : ι) {d : ℕ} (hd : 0 < d) : CutClock (clockLift ι) where
  clock := ⟨sectionForm i d, by
    rw [sectionForm_eq_exactForm i hd]
    exact exactForm_isClosed clockLift_wellFormed _⟩
  isCut := sectionForm_isCut i d

/-- [proved-derived; formal-checked] **The signed crossing count is the change of whole windings.**
For any aeon of the lift, a `±1` walk included, forward minus backward crossings of navigator
`i`'s section equal `⌊y i / d⌋ − ⌊x i / d⌋`. -/
theorem signed_count_is_flux (i : ι) {d : ℕ} (hd : 0 < d) {x y : ι → ℤ}
    (γ : Aeon (clockLift ι) x y) :
    (forwardCrossings (sectionForm i d) γ.steps : ℤ) - backwardCrossings (sectionForm i d) γ.steps =
      y i / d - x i / d := by
  have h := reading_eq_crossings (sectionClock i hd) γ
  have he : reading (sectionClock i hd).clock γ = y i / d - x i / d := by
    unfold reading
    change wordReading (sectionForm i d) γ.steps = _
    rw [sectionForm_eq_exactForm i hd]
    exact wordReading_exactForm _ γ.chained
  rw [← he, h]
  rfl

/-- [proved-derived; formal-checked] **The monotone case.** An aeon that only advances has no
backward crossing, so its tick count at the section is the change of whole windings. -/
theorem monotone_count_is_flux (i : ι) {d : ℕ} (hd : 0 < d) {x y : ι → ℤ}
    (γ : Aeon (clockLift ι) x y) (hfwd : ∀ s ∈ γ.steps, s.2 = true) :
    (#(aeonSection (sectionForm i d) γ).ticks : ℤ) = y i / d - x i / d := by
  have hb : backwardCrossings (sectionForm i d) γ.steps = 0 := by
    unfold backwardCrossings
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro s hs
    simp [hfwd s hs]
  have := signed_count_is_flux i hd γ
  rw [hb] at this
  simp only [aeonSection, card_crossingTicks (sectionForm_isCut i d), hb, add_zero]
  push_cast at this ⊢
  linarith

/-- [counterexample; formal-checked] **Unsigned arrivals are not the flux of a walk that turns
back.** On the one-navigator lift with `d = 2`, the aeon `0 → 1 → 2 → 1 → 2` crosses the section
twice forward and once backward: three ticks, while its signed reading and change of whole windings
are `1`. -/
theorem unsigned_count_is_not_flux :
    ∃ γ : Aeon (clockLift (Fin 1)) 0 (Pi.single 0 2),
      #(aeonSection (sectionForm (0 : Fin 1) 2) γ).ticks = 3 ∧
      (forwardCrossings (sectionForm (0 : Fin 1) 2) γ.steps : ℤ) -
          backwardCrossings (sectionForm (0 : Fin 1) 2) γ.steps = 1 ∧
      (Pi.single 0 2 : Fin 1 → ℤ) 0 / 2 - (0 : Fin 1 → ℤ) 0 / 2 = 1 := by
  refine ⟨⟨[((0, 0), true), ((Pi.single 0 1, 0), true), ((Pi.single 0 1, 0), false),
    ((Pi.single 0 1, 0), true)], ?_⟩, ?_, ?_, ?_⟩
  · simp only [ParametricComplex.chained_cons, ParametricComplex.chained_nil, clockLift,
      ParametricComplex.start, ParametricComplex.finish, if_true, Bool.false_eq_true, if_false]
    and_intros <;> trivial
  · simp only [aeonSection]
    rw [card_crossingTicks (sectionForm_isCut 0 2)]
    decide
  · decide
  · decide

end AeonEpochs

end Holonics.Aeon.Clock.Epoch
