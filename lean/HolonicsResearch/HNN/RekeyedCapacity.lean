import Holonics.HNN.ReframedMoment

/-!
# HNN.RekeyedCapacity: the moment's capacity across aeons and re-keys

[proved-derived; formal-checked] The box of #410: "`HNN/Moment.moment_capacity` beyond one aeon,
including re-keys." `HNN/Moment` counts the persisting source state after `n` cells; its `[open]`
paragraph names no re-key, and the atlas row `hnn.moment-capacity` scopes the count to "one aeon (no
re-keying)", as `HNN/RangedMoment` keeps "one opening, no re-key" (`hnn.ranged-moment-capacity`). A
re-key published at an aeon boundary sets a ring's phase class to the key and keeps its winding
(`HNN/Keys.rekey_keeps_winding`, atlas `hnn.rekey-keeps-winding`). `HNN/ReframedMoment` (atlas
`hnn.reframed-moment-capacity`) counts the winding window `[d_g W_g, d_g(W_g + M) + d_g − 1]` of
`d_g(M + 1)` values and leaves the premise that a current lift lies in it to its consumer
(`reframed_mem_box`'s `hcurrent`). The record of October 6,
`research/records/2026-10-06_THE_SOURCE_CAPACITY_BOUNDS_THE_ADMITTED_CLOCK_NOT_THE_OBSERVED_BATCH.md`
("The shared clock and the source's own clock"), derives that window from "every admitted native
occurrence advances at most one period and a rekey preserves winding", and asserts no crossover for
a re-keyed input. This file runs the stream through any number of aeons and proves the window, the
count and the crossover.

[definition] The setting. An event is a source cell or a re-key `(g, key)` with `key < d_g`
(`Event`; the key is a `Fin d_g`). A run of events from a state (`run adv s es`) ingests a cell
by `HNN/RangedMoment.ingestWith adv`, which is `HNN/Moment.ingest` at `adv = advance` (the
identity route, `ingestWith_identity`), and applies `HNN/Keys.rekey` at a re-key. A list of events
is any interleaving, so it holds any number of aeons and any re-keys at their boundaries; `cells es`
lists its cells in order. Of the advance law every theorem asks only that a cell move each ring
forward by at most one period, `τ_g ≤ adv(a, τ)_g ≤ τ_g + d_g`: on the identity route every period
at least two gives it (`advance_le_two`, `identity_range`), and on the located route it is
`RangedClock.advance_range`.

[proved-derived; formal-checked] What is proved.

1. **The windings stay in their window** (`rekey_winding`, `winding_run`, `run_lift_mem_window`).
   After a run with `n` cells and any re-keys, each ring's winding lies in `[W_g, W_g + n]` with
   `W_g = ⌊τ⁰_g / d_g⌋`, so its lift lies in `windingWindow d_g W_g n`, of `d_g(n + 1)` values: an
   advance of at most one period crosses at most one section (`ReframedMoment.winding_step_range`),
   and a re-key keeps every ring's winding. The window does not depend on the number of re-keys or
   aeons.
2. **The source counts keep their totals** (`run_append_rekey`, `run_window`, `run_card_bins`,
   `run_bins_letters`, `run_card_pairBins`). A re-key adds no count and rewrites none. After a run
   the held cells are its last `max Δ` cells, each source ring holds `n` counts whose letters are the
   run's cells, and each offset `δ` holds `n − δ` pairs. The phase class at which a later cell is
   binned is read through the re-keyed clock, so the bins are not those of the unrekeyed stream of
   the same cells (`rekey_changes_later_carries`).
3. **Capacity beyond one aeon** (`persist_mem_rekeyedBox`, `card_rekeyedBox_le`, `rekeyedBound_eq`,
   `rekeyed_moment_capacityWith`, `rekeyed_moment_capacity`, `located_rekeyed_moment_capacity`,
   `rekeyed_capacity_of_schedule`). The persisting state after any run with `n` cells lies in the
   box `rekeyedBox` (the windows times the source factors of `HNN/Moment.box` at `n`) of at most
   `N_rekey(n) = |A|^(max Δ) · ∏_(g<G) d_g(n + 1) · ∏_(g∈𝒮) [C(n + d_g|A| − 1, d_g|A| − 1) ·
   ∏_(δ∈Δ) C(n − δ + d_g|A|² − 1, d_g|A|² − 1)]` values (`rekeyedBound`, which is
   `RangedMoment.capacityBoundWith` at the rate `d_g`), however many aeons or re-keys the run holds.
   Where `N_rekey(n) < |A|ⁿ`, the map from the cells to the persisting state is not injective for
   any placement of re-keys among the cells (`events v` with `cells (events v) = v`), a fixed
   schedule (`scheduled`) among them: the moment stays lossy by construction across aeons.
4. **Against one aeon** (`capacityBound_le_rekeyedBound`, `rekeyedBound_eq_capacityBound`). Each
   lift factor `2n + d_g` of `Moment.capacityBound` widens to `d_g(n + 1)`, so `N(n) ≤ N_rekey(n)`,
   with equality when every period is two; on the located route the no-rekey count already carries
   the factor `d_g n + d_g`, and re-keying adds nothing to it.
5. **The crossover persists** (`rekeyed_capacity_persists`). `N_rekey` is log-concave from `max Δ`
   (`RangedMoment.capacityBoundWith_logConcave`), so a first crossing `n* > max Δ` below `|A|ⁿ`
   stays below at every later `n`.
6. **The window discharges the reframed premise** (`persist_zero_mem_boxWith`,
   `rekeyed_mem_reframedBox`). With the opening windings `W_g` and `M = n` (every cell of the run is
   the source's own), a run's current lifts and its source part satisfy `reframed_mem_box`'s
   `hcurrent` and `hsource`.
7. **Witnesses** (`rekey_changes_later_carries`, `climb_lift`, `descend_lift`,
   `rekeys_raise_the_winding_once_a_cell`). On rings of period `2`, the cells `[true, false]`
   without and with a re-key of ring `0` to `1` reach the lifts `2` and `3` of one winding, the carry
   into ring `1` on the first cell is `0` and `1`, and the bins differ: the re-key is load-bearing.
   On rings of period `4`, three cells with a re-key to `3` before each and to `2` at the end reach
   the winding `W + 3` and the lift `14`, and the same three cells with a re-key to `0` after each
   reach the lift `0`. The winding rises by one a cell, above `W + ⌈2n/d⌉ = W + 2`; the lifts the
   same three cells reach span `15` values, more than `2n + 2d = 14` or `d(⌊2n/d⌋ + 2) = 12`; and
   the climbing run's state lies outside `HNN/Moment.box` at `n = 3`.

What is not claimed. The box counts the stream state alone: a key law that chooses keys from the
stream is covered by item 3 only as a choice of events from the cells, and the law's own retained
state is not counted. Learned constitutions are not counted. The leaky coordinates of
`HNN/LeakyCapacity` multiply a box by their own factor (`card_reframedBox_withCoordinates_le`) and
are not joined here, and neither is the source-local profile of `HNN/ReframedMoment` (a sibling
source's own endpoint and ticks), which `rekeyed_mem_reframedBox` takes as given; cells of a sibling
source that advance the shared current (`M > n` there) are not runs of this file. The box is an
upper count: which of its states a declaration reaches is not stated beyond the witnesses. The
pigeonhole reads a total map on the full `A^n`, as in `moment_capacity`.

The computational object is the helical pair interaction read on the moment: each cell meets every
ring at its phase on the ring's helix and the held cell `δ` back through the pair contacts, and a
re-key turns a ring's phase without a carry, so the interaction continues on the same helix with
its placement moved. Of the winding guide's six general objects this touches the helix (the lift
as phase plus winding, the winding kept and the window holding it), faces and placement (the phase
class at which each later cell is binned), the pair (the offset counts and their totals) and the
tube (the passage read across its aeons as one run of cells and re-keys, at the ring clocks); cell
holonomy and the tower thread (the carry chain between rings, read here only through its bound)
stay attached through `HNN/Moment`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.RekeyedCapacity

open Holonics.HNN.Moment
open Holonics.HNN.Moment.SourceDecl

variable {A : Type*}

/-! ## 1. A stream of aeons -/

/-- [definition] **An event of the stream**: a source cell, or a re-key of ring `g` to a key below
its period, published at an aeon boundary. -/
inductive Event (D : SourceDecl A) where
  | cell (a : A)
  | rekey (g : ℕ) (key : Fin (D.period g))

namespace Event

variable {D : SourceDecl A}

/-- [definition] **One event acts on the stream state**: a cell is ingested under the advance law
`adv` (`RangedMoment.ingestWith`; `HNN/Moment.ingest` at `adv = advance`), and a re-key is
`HNN/Keys.rekey`. -/
def apply (adv : A → (ℕ → ℕ) → ℕ → ℕ) : Event D → D.StreamState → D.StreamState
  | cell a, s => D.ingestWith adv a s
  | rekey g key, s => Keys.rekey g key s

/-- [proved-derived; formal-checked] A cell is ingested. -/
@[simp] theorem apply_cell (adv : A → (ℕ → ℕ) → ℕ → ℕ) (a : A) (s : D.StreamState) :
    (cell a : Event D).apply adv s = D.ingestWith adv a s := rfl

/-- [proved-derived; formal-checked] A re-key is `Keys.rekey`. -/
@[simp] theorem apply_rekey (adv : A → (ℕ → ℕ) → ℕ → ℕ) (g : ℕ) (key : Fin (D.period g))
    (s : D.StreamState) : (rekey g key : Event D).apply adv s = Keys.rekey g key s := rfl

/-- [definition] The cell an event carries, if any. -/
def cellOf : Event D → Option A
  | cell a => some a
  | rekey _ _ => none

end Event

variable {D : SourceDecl A}

/-- [definition] **The run of a list of events** from the state `s` under the advance law `adv`. -/
def run (adv : A → (ℕ → ℕ) → ℕ → ℕ) (s : D.StreamState) (es : List (Event D)) : D.StreamState :=
  es.foldl (fun s e => e.apply adv s) s

/-- [definition] The cells of a list of events, in order. -/
def cells (es : List (Event D)) : List A := es.filterMap Event.cellOf

/-- [proved-derived; formal-checked] The empty run keeps the state. -/
@[simp] theorem run_nil (adv : A → (ℕ → ℕ) → ℕ → ℕ) (s : D.StreamState) : run adv s [] = s := rfl

/-- [proved-derived; formal-checked] A run applies its first event first. -/
@[simp] theorem run_cons (adv : A → (ℕ → ℕ) → ℕ → ℕ) (s : D.StreamState) (e : Event D)
    (es : List (Event D)) : run adv s (e :: es) = run adv (e.apply adv s) es := rfl

/-- [proved-derived; formal-checked] A run applies its last event last. -/
theorem run_append_one (adv : A → (ℕ → ℕ) → ℕ → ℕ) (s : D.StreamState) (es : List (Event D))
    (e : Event D) : run adv s (es ++ [e]) = e.apply adv (run adv s es) := by
  simp [run, List.foldl_append]

/-- [proved-derived; formal-checked] No events, no cells. -/
@[simp] theorem cells_nil : cells ([] : List (Event D)) = [] := rfl

/-- [proved-derived; formal-checked] A cell event contributes its cell. -/
@[simp] theorem cells_cons_cell (a : A) (es : List (Event D)) :
    cells (Event.cell a :: es) = a :: cells es := rfl

/-- [proved-derived; formal-checked] A re-key contributes no cell. -/
@[simp] theorem cells_cons_rekey (g : ℕ) (key : Fin (D.period g)) (es : List (Event D)) :
    cells (Event.rekey g key :: es) = cells es := rfl

/-- [proved-derived; formal-checked] The cells of a concatenation are concatenated. -/
theorem cells_append (es fs : List (Event D)) : cells (es ++ fs) = cells es ++ cells fs := by
  simp [cells, List.filterMap_append]

/-! ## 2. The windings stay in their window -/

/-- [proved-derived; formal-checked] On the identity route a cell moves each ring at most a period. -/
theorem identity_range (hd : ∀ g, 2 ≤ D.period g) (a : A) (τ : ℕ → ℕ) (g : ℕ) :
    τ g ≤ D.advance a τ g ∧ D.advance a τ g ≤ τ g + D.period g := by
  have h := D.advance_le_two hd a τ g
  have := hd g
  omega

/-- [proved-derived; formal-checked] A re-key keeps every ring's winding. -/
theorem rekey_winding (h : ℕ) (key : Fin (D.period h)) (s : D.StreamState) (g : ℕ) :
    (Keys.rekey h key s).lift g / D.period g = s.lift g / D.period g := by
  by_cases hg : g = h
  · subst hg; exact (Keys.rekey_keeps_winding g key key.isLt s).1
  · rw [(Keys.rekey_keeps_winding h key key.isLt s).2.2.1 g hg]

/-- [proved-derived; formal-checked] Over a run with `n` cells a winding rises by at most `n`. -/
theorem winding_run (adv : A → (ℕ → ℕ) → ℕ → ℕ)
    (hrange : ∀ a τ g, τ g ≤ adv a τ g ∧ adv a τ g ≤ τ g + D.period g) (g : ℕ)
    (hdg : 0 < D.period g) :
    ∀ (es : List (Event D)) (s : D.StreamState),
      s.lift g / D.period g ≤ (run adv s es).lift g / D.period g ∧
        (run adv s es).lift g / D.period g ≤ s.lift g / D.period g + (cells es).length
  | [], s => by simp
  | Event.cell a :: es, s => by
      have ih := winding_run adv hrange g hdg es (D.ingestWith adv a s)
      have hw := SourceDecl.winding_step_range hdg (hrange a s.lift g)
      change s.lift g / D.period g ≤ (run adv (D.ingestWith adv a s) es).lift g / D.period g ∧
        (run adv (D.ingestWith adv a s) es).lift g / D.period g ≤
          s.lift g / D.period g + ((cells es).length + 1)
      change adv a s.lift g / D.period g ≤ _ ∧ _ ≤ adv a s.lift g / D.period g + _ at ih
      omega
  | Event.rekey h key :: es, s => by
      have ih := winding_run adv hrange g hdg es (Keys.rekey h key s)
      rw [rekey_winding] at ih
      simpa using ih

/-- [proved-derived; formal-checked] **The lift after any run lies in its winding window.** -/
theorem run_lift_mem_window (adv : A → (ℕ → ℕ) → ℕ → ℕ)
    (hrange : ∀ a τ g, τ g ≤ adv a τ g ∧ adv a τ g ≤ τ g + D.period g)
    (hd1 : ∀ g, 1 ≤ D.period g) (τ₀ : ℕ → ℕ) (es : List (Event D)) (g : ℕ) :
    (run adv (D.initial τ₀) es).lift g ∈
      D.windingWindow (D.period g) (τ₀ g / D.period g) (cells es).length := by
  have hdg : 0 < D.period g := hd1 g
  exact D.mem_windingWindow_of_div_mod hdg (winding_run adv hrange g hdg es (D.initial τ₀))
    (Nat.mod_lt _ hdg)

/-! ## 3. The source counts -/

/-- [proved-derived; formal-checked] A re-key adds no count, no offset pair and no held cell. -/
theorem run_append_rekey (adv : A → (ℕ → ℕ) → ℕ → ℕ) (s : D.StreamState) (es : List (Event D))
    (g : ℕ) (key : Fin (D.period g)) :
    (run adv s (es ++ [Event.rekey g key])).bins = (run adv s es).bins ∧
      (run adv s (es ++ [Event.rekey g key])).pairBins = (run adv s es).pairBins ∧
      (run adv s (es ++ [Event.rekey g key])).window = (run adv s es).window := by
  rw [run_append_one, Event.apply_rekey]
  exact ⟨rfl, rfl, rfl⟩

/-- [proved-derived; formal-checked] After a run the held cells are its last `max Δ` cells. -/
theorem run_window (adv : A → (ℕ → ℕ) → ℕ → ℕ) (τ₀ : ℕ → ℕ) (es : List (Event D)) :
    (run adv (D.initial τ₀) es).window = (cells es).reverse.take D.windowLength := by
  induction es using List.reverseRecOn with
  | nil => simp [initial]
  | append_singleton es e ih =>
      rw [run_append_one, cells_append]
      cases e with
      | cell a =>
          change (a :: (run adv (D.initial τ₀) es).window).take D.windowLength = _
          rw [ih]
          simp only [cells_cons_cell, cells_nil, List.reverse_append, List.reverse_singleton,
            List.singleton_append]
          cases D.windowLength with
          | zero => simp
          | succ m => simp [List.take_take]
      | rekey g key =>
          change (run adv (D.initial τ₀) es).window = _
          rw [ih, cells_cons_rekey, cells_nil, List.append_nil]

/-- [proved-derived; formal-checked] After a run each source ring holds one count per cell. -/
theorem run_card_bins (adv : A → (ℕ → ℕ) → ℕ → ℕ) (τ₀ : ℕ → ℕ) {g : ℕ} (hg : g ∈ D.sources)
    (es : List (Event D)) :
    Multiset.card ((run adv (D.initial τ₀) es).bins g) = (cells es).length := by
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es e ih =>
      rw [run_append_one, cells_append, List.length_append]
      cases e with
      | cell a =>
          change Multiset.card (if g ∈ D.sources then
            ((adv a (run adv (D.initial τ₀) es).lift g : ZMod (D.period g)), a) ::ₘ
              (run adv (D.initial τ₀) es).bins g else (run adv (D.initial τ₀) es).bins g) = _
          rw [if_pos hg, Multiset.card_cons, ih]
          simp
      | rekey h key =>
          change Multiset.card ((run adv (D.initial τ₀) es).bins g) = _
          simp [ih]

/-- [proved-derived; formal-checked] The letters a source ring's counts hold are the run's cells. -/
theorem run_bins_letters (adv : A → (ℕ → ℕ) → ℕ → ℕ) (τ₀ : ℕ → ℕ) {g : ℕ} (hg : g ∈ D.sources)
    (es : List (Event D)) :
    ((run adv (D.initial τ₀) es).bins g).map Prod.snd = (cells es : Multiset A) := by
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es e ih =>
      rw [run_append_one, cells_append]
      cases e with
      | cell a =>
          change Multiset.map Prod.snd (if g ∈ D.sources then
            ((adv a (run adv (D.initial τ₀) es).lift g : ZMod (D.period g)), a) ::ₘ
              (run adv (D.initial τ₀) es).bins g else (run adv (D.initial τ₀) es).bins g) = _
          rw [if_pos hg, Multiset.map_cons, ih]
          simpa using (List.perm_append_singleton a (cells es)).symm
      | rekey h key =>
          change Multiset.map Prod.snd ((run adv (D.initial τ₀) es).bins g) = _
          simp [ih]

/-- [proved-derived; formal-checked] After a run with `n` cells the offset `δ` holds `n − δ` pairs. -/
theorem run_card_pairBins (adv : A → (ℕ → ℕ) → ℕ → ℕ) (τ₀ : ℕ → ℕ) {g δ : ℕ}
    (hg : g ∈ D.sources) (hδ : δ ∈ D.offsets) (hδpos : 1 ≤ δ) (es : List (Event D)) :
    Multiset.card ((run adv (D.initial τ₀) es).pairBins g δ) = (cells es).length - δ := by
  have hδW : δ ≤ D.windowLength := Finset.le_sup (f := id) hδ
  induction es using List.reverseRecOn with
  | nil => simp [initial]
  | append_singleton es e ih =>
      rw [run_append_one, cells_append, List.length_append]
      cases e with
      | cell a =>
          change Multiset.card (if g ∈ D.sources ∧ δ ∈ D.offsets then
            ((run adv (D.initial τ₀) es).window[δ - 1]?).elim
              ((run adv (D.initial τ₀) es).pairBins g δ)
              (fun b => ((adv a (run adv (D.initial τ₀) es).lift g : ZMod (D.period g)), a, b) ::ₘ
                (run adv (D.initial τ₀) es).pairBins g δ)
            else (run adv (D.initial τ₀) es).pairBins g δ) = _
          rw [if_pos ⟨hg, hδ⟩, run_window]
          simp only [cells_cons_cell, cells_nil, List.length_singleton]
          by_cases hl : δ ≤ (cells es).length
          · have hlt : δ - 1 < ((cells es).reverse.take D.windowLength).length := by
              simp only [List.length_take, List.length_reverse]; omega
            rw [List.getElem?_eq_getElem hlt, Option.elim_some, Multiset.card_cons, ih]
            omega
          · have hnone : ((cells es).reverse.take D.windowLength)[δ - 1]? = none := by
              rw [List.getElem?_eq_none_iff]
              simp only [List.length_take, List.length_reverse]; omega
            rw [hnone, Option.elim_none, ih]
            omega
      | rekey h key =>
          change Multiset.card ((run adv (D.initial τ₀) es).pairBins g δ) = _
          simp [ih]

/-! ## 4. Capacity beyond one aeon -/

section Capacity

variable (D)

/-- [definition] The source part of a persisting state: the counts, offset counts and held cells. -/
abbrev SourcePart :=
  ((g : D.sources) → Multiset (ZMod (D.period g.1) × A)) ×
    ((p : D.sources × D.offsets) → Multiset (ZMod (D.period p.1.1) × A × A)) × List A

/-- [definition] The source part of a stream state. -/
def sourcePart (s : D.StreamState) : SourcePart D :=
  (fun g => s.bins g.1, fun p => s.pairBins p.1.1 p.2.1, s.window)

/-- [definition] **The count `N_rekey(n)`**: `RangedMoment.capacityBoundWith` at the rate `d_g`,
the lift factor `d_g n + d_g = d_g(n + 1)` of the winding window on every ring. -/
def rekeyedBound (G alphabet n : ℕ) : ℕ := D.capacityBoundWith D.period G alphabet n

/-- [proved-derived; formal-checked] The persisting state is its lifts beside its source part. -/
theorem persist_eq [Fintype A] [DecidableEq A] (G : ℕ) (s : D.StreamState) :
    D.persist G s = (fun g : Fin G => s.lift g, sourcePart D s) := rfl

variable [Fintype A] [DecidableEq A] [hne : ∀ g, NeZero (D.period g)]

/-- [definition] The source factors of `HNN/Moment.box` at `n` cells. -/
def sourceBox (n : ℕ) : Finset (SourcePart D) :=
  Fintype.piFinset (fun g : D.sources =>
      (Finset.univ : Finset (Sym (ZMod (D.period g.1) × A) n)).map
        ⟨Sym.toMultiset, Sym.coe_injective⟩) ×ˢ
    Fintype.piFinset (fun p : D.sources × D.offsets =>
      (Finset.univ : Finset (Sym (ZMod (D.period p.1.1) × A × A) (n - p.2.1))).map
        ⟨Sym.toMultiset, Sym.coe_injective⟩) ×ˢ
    (Finset.univ : Finset (List.Vector A (min n D.windowLength))).map
      ⟨List.Vector.toList, List.Vector.toList_injective⟩

/-- [proved-derived; formal-checked] `HNN/Moment.box` is its lift ranges beside `sourceBox`. -/
theorem box_eq (τ₀ : ℕ → ℕ) (G n : ℕ) :
    D.box τ₀ G n =
      Fintype.piFinset (fun g : Fin G => Finset.Icc (τ₀ g) (τ₀ g + 2 * n)) ×ˢ sourceBox D n := rfl

/-- [proved-derived; formal-checked] `RangedMoment.boxWith` is its lift ranges beside `sourceBox`. -/
theorem boxWith_eq (rate τ₀ : ℕ → ℕ) (G n : ℕ) :
    D.boxWith rate τ₀ G n =
      Fintype.piFinset (fun g : Fin G => Finset.Icc (τ₀ g) (τ₀ g + rate g * n)) ×ˢ
        sourceBox D n := rfl

/-- [definition] **The box after `n` cells and any re-keys**: the winding windows from the opening
windings on the first `G` rings, beside the source factors at `n`. -/
def rekeyedBox (τ₀ : ℕ → ℕ) (G n : ℕ) : Finset (D.Persist G) :=
  Fintype.piFinset (fun g : Fin G => D.windingWindow (D.period g) (τ₀ g / D.period g) n) ×ˢ
    sourceBox D n

variable {D}

/-- [proved-derived; formal-checked] A run's source part lies in the source factors at its cells. -/
theorem sourcePart_mem_sourceBox (adv : A → (ℕ → ℕ) → ℕ → ℕ) (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ)
    (τ₀ : ℕ → ℕ) (es : List (Event D)) :
    sourcePart D (run adv (D.initial τ₀) es) ∈ sourceBox D (cells es).length := by
  refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun g => ?_,
    Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun p => ?_, ?_⟩⟩
  · exact Finset.mem_map.mpr ⟨⟨(run adv (D.initial τ₀) es).bins g.1,
      run_card_bins adv τ₀ g.2 es⟩, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_map.mpr ⟨⟨(run adv (D.initial τ₀) es).pairBins p.1.1 p.2.1,
      run_card_pairBins adv τ₀ p.1.2 p.2.2 (hδpos _ p.2.2) es⟩, Finset.mem_univ _, rfl⟩
  · refine Finset.mem_map.mpr ⟨(⟨(run adv (D.initial τ₀) es).window, ?_⟩ :
      List.Vector A (min (cells es).length D.windowLength)), Finset.mem_univ _, rfl⟩
    rw [run_window, List.length_take, List.length_reverse, min_comm]

/-- [proved-derived; formal-checked] **The persisting state after any run lies in `rekeyedBox`.** -/
theorem persist_mem_rekeyedBox (adv : A → (ℕ → ℕ) → ℕ → ℕ)
    (hrange : ∀ a τ g, τ g ≤ adv a τ g ∧ adv a τ g ≤ τ g + D.period g)
    (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ) (τ₀ : ℕ → ℕ) (G : ℕ) (es : List (Event D)) :
    D.persist G (run adv (D.initial τ₀) es) ∈ rekeyedBox D τ₀ G (cells es).length := by
  have hd1 : ∀ g, 1 ≤ D.period g := fun g => Nat.pos_of_ne_zero (hne g).out
  rw [persist_eq]
  exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun g =>
    run_lift_mem_window adv hrange hd1 τ₀ es g, sourcePart_mem_sourceBox adv hδpos τ₀ es⟩

/-- [proved-derived; formal-checked] The source factors hold at most the count without lift rings. -/
theorem card_sourceBox_le [Nonempty A] (n : ℕ) :
    (sourceBox D n).card ≤ D.capacityBoundWith D.period 0 (Fintype.card A) n := by
  have h := card_boxWith_le (D := D) D.period (fun _ => 0) 0 n
  rw [boxWith_eq, Finset.card_product] at h
  simpa using h

omit [Fintype A] [DecidableEq A] hne in
/-- [proved-derived; formal-checked] `N_rekey(n)` is the windows' `∏ d_g(n + 1)` times the source factors. -/
theorem rekeyedBound_eq (G alphabet n : ℕ) :
    rekeyedBound D G alphabet n =
      (∏ g : Fin G, D.period g * (n + 1)) * D.capacityBoundWith D.period 0 alphabet n := by
  have hP : ∏ g ∈ Finset.range G, (D.period g * n + D.period g) =
      ∏ g : Fin G, D.period g * (n + 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun g => D.period g * (n + 1)) G]
    exact Finset.prod_congr rfl fun g _ => by ring
  unfold rekeyedBound capacityBoundWith
  rw [hP, Finset.range_zero, Finset.prod_empty]
  ring

/-- [proved-derived; formal-checked] **`rekeyedBox` has at most `N_rekey(n)` states.** -/
theorem card_rekeyedBox_le [Nonempty A] (τ₀ : ℕ → ℕ) (G n : ℕ) :
    (rekeyedBox D τ₀ G n).card ≤ rekeyedBound D G (Fintype.card A) n := by
  have hlift := D.card_reframedLiftBox G (fun g => τ₀ g / D.period g) n
  rw [rekeyedBox, Finset.card_product, hlift, rekeyedBound_eq]
  exact Nat.mul_le_mul_left _ (card_sourceBox_le n)

omit [Fintype A] [DecidableEq A] hne in
/-- [proved-derived; formal-checked] Re-keying widens each lift factor: `N(n) ≤ N_rekey(n)`. -/
theorem capacityBound_le_rekeyedBound (hd : ∀ g, 2 ≤ D.period g) (G alphabet n : ℕ) :
    D.capacityBound G alphabet n ≤ rekeyedBound D G alphabet n := by
  unfold capacityBound rekeyedBound capacityBoundWith
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Finset.prod_le_prod' fun g _ => ?_))
  have := Nat.mul_le_mul_right n (hd g)
  omega

omit [Fintype A] [DecidableEq A] hne in
/-- [proved-derived; formal-checked] On rings of period two re-keying costs nothing: `N_rekey = N`. -/
theorem rekeyedBound_eq_capacityBound (h2 : ∀ g, D.period g = 2) (G alphabet n : ℕ) :
    rekeyedBound D G alphabet n = D.capacityBound G alphabet n := by
  unfold rekeyedBound capacityBoundWith capacityBound
  congr 2
  exact Finset.prod_congr rfl fun g _ => by rw [h2 g]

/-- [proved-derived; formal-checked] **Capacity beyond one aeon**, for any advance of at most a period. -/
theorem rekeyed_moment_capacityWith [Nonempty A] (adv : A → (ℕ → ℕ) → ℕ → ℕ)
    (hrange : ∀ a τ g, τ g ≤ adv a τ g ∧ adv a τ g ≤ τ g + D.period g)
    (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ) (τ₀ : ℕ → ℕ) (G n : ℕ) :
    (∀ es : List (Event D), (cells es).length = n →
      D.persist G (run adv (D.initial τ₀) es) ∈ rekeyedBox D τ₀ G n) ∧
    (rekeyedBox D τ₀ G n).card ≤ rekeyedBound D G (Fintype.card A) n ∧
    (∀ events : (Fin n → A) → List (Event D), (∀ v, cells (events v) = List.ofFn v) →
      rekeyedBound D G (Fintype.card A) n < Fintype.card A ^ n →
        ¬ Function.Injective fun v => D.persist G (run adv (D.initial τ₀) (events v))) := by
  have hmem : ∀ es : List (Event D), (cells es).length = n →
      D.persist G (run adv (D.initial τ₀) es) ∈ rekeyedBox D τ₀ G n := fun es hes =>
    hes ▸ persist_mem_rekeyedBox adv hrange hδpos τ₀ G es
  refine ⟨hmem, card_rekeyedBox_le τ₀ G n, fun events hev hlt hinj => ?_⟩
  let f' : (Fin n → A) → rekeyedBox D τ₀ G n := fun v =>
    ⟨D.persist G (run adv (D.initial τ₀) (events v)), hmem _ (by rw [hev, List.length_ofFn])⟩
  have hinj' : Function.Injective f' := fun v w h => hinj (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f' hinj'
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] at hcard
  have := card_rekeyedBox_le (D := D) τ₀ G n
  omega

/-- [proved-derived; formal-checked] **Capacity beyond one aeon on the identity route** (`HNN/Moment`). -/
theorem rekeyed_moment_capacity [Nonempty A] (hd : ∀ g, 2 ≤ D.period g)
    (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ) (τ₀ : ℕ → ℕ) (G n : ℕ) :
    (∀ es : List (Event D), (cells es).length = n →
      D.persist G (run D.advance (D.initial τ₀) es) ∈ rekeyedBox D τ₀ G n) ∧
    (rekeyedBox D τ₀ G n).card ≤ rekeyedBound D G (Fintype.card A) n ∧
    (∀ events : (Fin n → A) → List (Event D), (∀ v, cells (events v) = List.ofFn v) →
      rekeyedBound D G (Fintype.card A) n < Fintype.card A ^ n →
        ¬ Function.Injective fun v => D.persist G (run D.advance (D.initial τ₀) (events v))) :=
  rekeyed_moment_capacityWith D.advance (identity_range hd) hδpos τ₀ G n

/-- [proved-derived; formal-checked] **Capacity beyond one aeon on the located route** (`RangedMoment`). -/
theorem located_rekeyed_moment_capacity [Nonempty A] (C : RangedClock A D.period)
    (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ) (τ₀ : ℕ → ℕ) (G n : ℕ) :
    (∀ es : List (Event D), (cells es).length = n →
      D.persist G (run C.advance (D.initial τ₀) es) ∈ rekeyedBox D τ₀ G n) ∧
    (rekeyedBox D τ₀ G n).card ≤ rekeyedBound D G (Fintype.card A) n ∧
    (∀ events : (Fin n → A) → List (Event D), (∀ v, cells (events v) = List.ofFn v) →
      rekeyedBound D G (Fintype.card A) n < Fintype.card A ^ n →
        ¬ Function.Injective fun v => D.persist G (run C.advance (D.initial τ₀) (events v))) :=
  rekeyed_moment_capacityWith C.advance C.advance_range hδpos τ₀ G n

omit [Fintype A] [DecidableEq A] hne in
/-- [proved-derived; formal-checked] **The re-keyed crossover persists** past `max Δ`. -/
theorem rekeyed_capacity_persists [Fintype A] [Nonempty A] (hd1 : ∀ g, 1 ≤ D.period g) (G : ℕ)
    {nstar : ℕ} (hstar : D.windowLength + 1 ≤ nstar)
    (hbelow : rekeyedBound D G (Fintype.card A) nstar < Fintype.card A ^ nstar)
    (habove : Fintype.card A ^ (nstar - 1) ≤ rekeyedBound D G (Fintype.card A) (nstar - 1)) :
    ∀ n, nstar ≤ n → rekeyedBound D G (Fintype.card A) n < Fintype.card A ^ n :=
  capacityWith_persists D.period hd1 G hstar hbelow habove

/-- [proved-derived; formal-checked] A run's source part satisfies `reframed_mem_box`'s `hsource`. -/
theorem persist_zero_mem_boxWith (adv : A → (ℕ → ℕ) → ℕ → ℕ) (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ)
    (τ₀ : ℕ → ℕ) (es : List (Event D)) :
    D.persist 0 (run adv (D.initial τ₀) es) ∈
      D.boxWith D.period (fun _ => 0) 0 (cells es).length := by
  rw [boxWith_eq, persist_eq]
  exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun g => g.elim0,
    sourcePart_mem_sourceBox adv hδpos τ₀ es⟩

/-- [proved-derived; formal-checked] **The window discharges `reframed_mem_box`'s `hcurrent`** at `M = n`. -/
theorem rekeyed_mem_reframedBox (adv : A → (ℕ → ℕ) → ℕ → ℕ)
    (hrange : ∀ a τ g, τ g ≤ adv a τ g ∧ adv a τ g ≤ τ g + D.period g)
    (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ) (τ₀ : ℕ → ℕ) (G : ℕ) (rate : ℕ → ℕ) (es : List (Event D))
    (profile : (g : D.sources) → Fin (D.period g.1) × ℕ)
    (hprofile : profile ∈ D.sourceProfileBox rate (cells es).length) :
    (((fun g : Fin G => (run adv (D.initial τ₀) es).lift g), profile),
        D.persist 0 (run adv (D.initial τ₀) es)) ∈
      D.reframedBox G (fun g => τ₀ g / D.period g) (cells es).length (cells es).length rate := by
  have hd1 : ∀ g, 1 ≤ D.period g := fun g => Nat.pos_of_ne_zero (hne g).out
  exact D.reframed_mem_box G _ _ _ rate _ profile _
    (fun g => run_lift_mem_window adv hrange hd1 τ₀ es g) hprofile
    (persist_zero_mem_boxWith adv hδpos τ₀ es)

end Capacity

/-! ## 5. A fixed schedule of re-keys -/

/-- [definition] A published re-key `(g, key)`, `key < d_g`, as an event. -/
def rekeyEvent (p : (g : ℕ) × Fin (D.period g)) : Event D := Event.rekey p.1 p.2

/-- [definition] **A fixed schedule**: `scheduled R k l` publishes the re-keys `R j` at the aeon
boundary before the cell `j` of `l` (cells counted from `k`), and `R (k + |l|)` after the last. -/
def scheduled (R : ℕ → List ((g : ℕ) × Fin (D.period g))) : ℕ → List A → List (Event D)
  | k, [] => (R k).map rekeyEvent
  | k, a :: l => (R k).map rekeyEvent ++ Event.cell a :: scheduled R (k + 1) l

/-- [proved-derived; formal-checked] Published re-keys carry no cells. -/
theorem cells_map_rekeyEvent (L : List ((g : ℕ) × Fin (D.period g))) :
    cells (L.map rekeyEvent) = [] := by
  induction L with
  | nil => rfl
  | cons p L ih => exact ih

/-- [proved-derived; formal-checked] A schedule's cells are the cells it was given. -/
theorem cells_scheduled (R : ℕ → List ((g : ℕ) × Fin (D.period g))) :
    ∀ (k : ℕ) (l : List A), cells (scheduled R k l) = l
  | k, [] => cells_map_rekeyEvent _
  | k, a :: l => by
      rw [scheduled, cells_append, cells_map_rekeyEvent, cells_cons_cell,
        cells_scheduled R (k + 1) l, List.nil_append]

/-- [proved-derived; formal-checked] **For a fixed schedule of re-keys the moment stays lossy.** -/
theorem rekeyed_capacity_of_schedule [Fintype A] [DecidableEq A] [∀ g, NeZero (D.period g)]
    [Nonempty A] (hd : ∀ g, 2 ≤ D.period g) (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ) (τ₀ : ℕ → ℕ)
    (G n : ℕ) (R : ℕ → List ((g : ℕ) × Fin (D.period g)))
    (hlt : rekeyedBound D G (Fintype.card A) n < Fintype.card A ^ n) :
    ¬ Function.Injective fun v : Fin n → A =>
      D.persist G (run D.advance (D.initial τ₀) (scheduled R 0 (List.ofFn v))) :=
  (rekeyed_moment_capacity hd hδpos τ₀ G n).2.2 _ (fun _ => cells_scheduled R 0 _) hlt

/-! ## 6. Witnesses -/

/-- [definition] Every ring of period `d`, each lock fitting every cell, ring `0` the one source. -/
def everyRing (d : ℕ) : SourceDecl Bool where
  period _ := d
  lock _ := {0}
  port _ _ := 0
  sources := {0}
  offsets := ∅

/-- [definition] The periods of `everyRing d` are nonzero with `d`. -/
instance everyRing_neZero (d : ℕ) [NeZero d] (g : ℕ) : NeZero ((everyRing d).period g) := ‹_›

/-- [counterexample; formal-checked] **A re-key changes the later carries and the bins** (period `2`). -/
theorem rekey_changes_later_carries :
    (run (everyRing 2).advance ((everyRing 2).initial fun _ => 0)
        [.cell true, .cell false]).lift 0 = 2 ∧
      (run (everyRing 2).advance ((everyRing 2).initial fun _ => 0)
        [.rekey 0 ⟨1, by decide⟩, .cell true, .cell false]).lift 0 = 3 ∧
      (run (everyRing 2).advance ((everyRing 2).initial fun _ => 0)
          [.cell true, .cell false]).lift 0 / 2 =
        (run (everyRing 2).advance ((everyRing 2).initial fun _ => 0)
          [.rekey 0 ⟨1, by decide⟩, .cell true, .cell false]).lift 0 / 2 ∧
      (everyRing 2).carryIn true (fun _ => 0) 1 = 0 ∧
      (everyRing 2).carryIn true (Keys.rekey 0 1 ((everyRing 2).initial fun _ => 0)).lift 1 = 1 ∧
      (run (everyRing 2).advance ((everyRing 2).initial fun _ => 0)
          [.cell true, .cell false]).bins 0 ≠
        (run (everyRing 2).advance ((everyRing 2).initial fun _ => 0)
          [.rekey 0 ⟨1, by decide⟩, .cell true, .cell false]).bins 0 := by
  decide

/-- [definition] Three cells on period-`4` rings, each after a re-key of ring `0` to `3`, then `2`. -/
def climb : List (Event (everyRing 4)) :=
  [.rekey 0 ⟨3, by decide⟩, .cell true, .rekey 0 ⟨3, by decide⟩, .cell true,
    .rekey 0 ⟨3, by decide⟩, .cell true, .rekey 0 ⟨2, by decide⟩]

/-- [definition] The same three cells, each followed by a re-key of ring `0` to `0`. -/
def descend : List (Event (everyRing 4)) :=
  [.cell true, .rekey 0 ⟨0, by decide⟩, .cell true, .rekey 0 ⟨0, by decide⟩,
    .cell true, .rekey 0 ⟨0, by decide⟩]

/-- [counterexample; formal-checked] The climbing run reaches ring `0`'s lift `14`. -/
theorem climb_lift : (run (everyRing 4).advance ((everyRing 4).initial fun _ => 0) climb).lift 0 = 14 := by
  decide

/-- [counterexample; formal-checked] The descending run reaches ring `0`'s lift `0`. -/
theorem descend_lift :
    (run (everyRing 4).advance ((everyRing 4).initial fun _ => 0) descend).lift 0 = 0 := by
  decide

/-- [counterexample; formal-checked] **Re-keys raise the winding once a cell** and leave `Moment.box`. -/
theorem rekeys_raise_the_winding_once_a_cell :
    cells climb = [true, true, true] ∧ cells descend = [true, true, true] ∧
      (run (everyRing 4).advance ((everyRing 4).initial fun _ => 0) climb).lift 0 / 4 = 0 + 3 ∧
      0 + (2 * 3 + 4 - 1) / 4 < 3 ∧
      2 * 3 + 2 * 4 < 14 - 0 + 1 ∧ 4 * (2 * 3 / 4 + 2) < 14 - 0 + 1 ∧
      (run (everyRing 4).advance ((everyRing 4).initial fun _ => 0) climb).lift 0 ∈
        (everyRing 4).windingWindow 4 (0 / 4) 3 ∧
      (everyRing 4).persist 1 (run (everyRing 4).advance ((everyRing 4).initial fun _ => 0) climb) ∉
        (everyRing 4).box (fun _ => 0) 1 3 := by
  refine ⟨rfl, rfl, by rw [climb_lift], by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [climb_lift]; decide
  · rw [box_eq, persist_eq, Finset.mem_product, not_and_or]
    left
    rw [Fintype.mem_piFinset, not_forall]
    refine ⟨0, ?_⟩
    simp only [Finset.mem_Icc, Fin.val_zero, climb_lift]
    norm_num

end Holonics.HNN.RekeyedCapacity
