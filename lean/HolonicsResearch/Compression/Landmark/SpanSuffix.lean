import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.Prod.Lex
import Holonics.Foundation.ReceiverHistoryCompression

/-!
# A span located from a reading part: its retained suffix is future-sufficient

[definition] [proved-derived; formal-checked] The source is #410's box on `SpanReading`'s retained suffix
(`compression::landmark::context::spans`): the last at most `|held span| − 1` cells, the received count and the
longest, latest located address preserve every later `located` consequence. The owner it reads
is the retired Rust module `crates/holonics/src/compression/landmark/context/spans.rs` (at `fbb9dee61^`, and at
`f5fd8f3b` as `docs/HNN_FORMULA.md` item 7 links it), whose open paragraph defines **the located continuation**: a
part on one port reads a closed span on another, and after each received cell its address across the two ports is
the longest suffix of the part's cells that recurs in the span followed by a cell, the latest in the span among the
longest; the occurrence is kept while it continues and located anew at a break. The atlas row is
`context.span-located` (`docs/atlas/information.tsv`): `located(part, span) = (L, x̂)`,
`L = max{ℓ ≥ 1 : part[n−ℓ, n) = span[j−ℓ, j), j < |span|}`, `x̂ = span[j]` (the latest `j` among the longest), and
`x_n = x̂ ∧ j + 1 < |span| ⇒ (j, L) ↦ (j + 1, L + 1)`, again the longest. The retained state is the one the F5
owner audit lists as the open part's `SpanReading` counters
(`research/records/2026-09-27_F5_ATOMIC_STANDING_OWNER_AUDIT.md`), and the law it instances is the retention law
(`Foundation/Standing.lean`; the quotient that is future-sufficient, atlas `quotient.static-compression` for the
control that a present receiver alone does not certify it). The owner retired on September 30 with the byte-tree
text line (`docs/RECEIVER_HOLARCHY.md`, "The retired byte-tree text line"); this module states its law as
mathematics and builds no stage.

The model. Cells are a type `α` with decidable equality; a part and a span are lists. `l.rtake n` is Mathlib's last
`n` cells of `l` (`l.drop (|l| − n)`). A **match** `(j, ℓ)` (`IsMatch`) has `1 ≤ ℓ ≤ j < |span|`, `ℓ ≤ |part|` and
the last `ℓ` cells of the part equal to `span[j−ℓ, j)`, the last `ℓ` cells of `span.take j` (`window_eq`). The
**located address** (`located`) is the match of largest `ℓ` and, among those, largest `j`, read as the `argmax` of
the order `(ℓ, j)` over the finite list of matches (`matchList`, `rank`); the address's next cell is `x̂ = span[j]`
(`continuation`). The retained capacity is `K = |span| − 1`.

What is proved.

1. **The located address** (`mem_matchList`, `located_isMatch`, `located_max`, `located_longest`,
   `located_latest`, `located_eq_none_iff`, `located_eq_some_iff`, `continuation_isSome_iff`): `located` returns a
   match, no match is longer, no match of the same length ends later, it is `none` exactly when no match exists,
   and it is the one pair with these properties (`IsLocated`); its next cell `x̂` exists whenever it does.
2. **Nothing located before a recurrence** (`isMatch_one_iff`, `exists_isMatch_iff`, `located_eq_none_iff_getLast`,
   `located_nil`, `located_eq_none_iff_of_ne_nil`): `located part span = none` exactly when the part is empty or
   its last cell does not occur in `span.dropLast`; a match of any length gives one of length one
   (`IsMatch.shorten`).
3. **The length bound** (`IsMatch.le_capacity`, `located_bounds`, `located_length_le`): a located length `L` has
   `1 ≤ L ≤ j < |span|`, so `L ≤ |span| − 1`.
4. **The retained suffix suffices** (`isMatch_rtake_iff`, `located_rtake`, `located_retained_suffix`,
   `future_equivalent`, `retainedSuffixCompression`, `transportWord_appendCell`): for every `K ≥ |span| − 1`,
   `located part span = located (part.rtake K) span`; so two parts with the same last `|span| − 1` cells give the
   same `located` reading after every future `f`. The suffix is a `ReceiverHistoryCompression` of the house
   (`Foundation/ReceiverHistoryCompression`): its quotient is `rtake (|span| − 1)`, its generators the received
   cells, and `future_equivalent` is that owner's `quotientEqForcesEverySuccessorFace` read on it.
5. **The continuation law** (`isMatch_concat`, `isMatch_of_concat`, `located_concat_of_continues`,
   `located_concat_retained`): if `located part span = some (j, L)`, `span[j] = x` and `j + 1 < |span|`, then
   `located (part ++ [x]) span = some (j + 1, L + 1)`: the occurrence is kept, again the longest and the latest
   among the longest. Whether or not it continues, the next address is located from the retained suffix and the
   new cell alone.
6. **The incremental reader** (`ReaderState`, `nextAddress`, `step`, `read`, `read_eq`, `read_suffix_length`,
   `read_address_eq_located_suffix`, `step_received_unread`, `foldl_received_unread`): the reader's state is
   `(suffix, received, address)` (the Rust `(part, received, at)`), and a step continues by item 5's rule when it
   applies and otherwise relocates on the new suffix. After reading any list of cells from the empty state the
   address is `located cells span`, the suffix is the list's last `min(|cells|, |span| − 1)` cells and the count
   is `|cells|`; the address is itself `located` of the retained suffix (what the Rust `restore` checks). The
   count is carried and never read: two states that differ only in it read every later list to the same suffix
   and address.
7. **A witness** (`witnessSpan`, `witness_longest_not_latest`, `witness_continues`, `witness_break`,
   `witness_no_cell_after`, `witness_reader`, `witness_latest_among_longest`, `witness_rust_snapshot`): on the
   span `5, 1, 2, 7, 2, 9` the part `1, 2` is located at `(3, 2)` while the latest occurrence of its last cell
   gives only the match `(5, 1)`; reading `7` continues to `(4, 3)`; reading `1` instead of `x̂ = 2` breaks and
   relocates at `(2, 1)`; the part `3, 1, 2, 7, 2, 9` holds a run of the span but no cell after it, so nothing is
   located. All by `decide`.

What is not claimed. The two-port reading's place in the receivers (`receiver::population::admitted`, the copy
stage that consumed the address), and the span's closing letter (which cells a span holds, and when it closes), are
not modelled: the span is a fixed list. The retained suffix is shown sufficient, not minimal: two cells that occur
nowhere in the span are read alike by every later `located`, and no coarsest quotient is derived (the retention
law's "suffices but is not minimal"). The Rust `locate` loop (its scan from the span's end and its early stop) is
not shown to compute `located`; the module states the law the loop was written to, and the witnesses replay the
owner's tests. No cost of relocation is stated.

The computational object is the helical pair interaction, read here as two ports' spans in contact: the reading part
and the held span pair cell by cell along a common suffix, and the address is the face where that pairing is
longest and latest. Of the winding guide's six general objects this module touches **faces and placement** (the
located address and its next cell, placed on the reading part's next tick) and the **tube** (the span from its
letter to its close, and the reading part's span read against it); the helix, the pair, the cell holonomy and the
tower thread stay attached through the receivers that read the address.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.Landmark.SpanSuffix

open Holonics.Foundation.Chronology Holonics.Foundation.LineageCompression

variable {α : Type*}

/-! ## The last cells of a list -/

section Lists

/-- [proved-standard; formal-checked] The last `n` cells of `l` number `min |l| n`. -/
theorem length_rtake (l : List α) (n : ℕ) : (l.rtake n).length = min l.length n := by
  simp only [List.rtake, List.length_drop]
  omega

/-- [proved-standard; formal-checked] The last `m` of the last `n` cells, `m ≤ n`, are the last `m` cells. -/
theorem rtake_rtake (l : List α) {m n : ℕ} (h : m ≤ n) : (l.rtake n).rtake m = l.rtake m := by
  simp only [List.rtake, List.drop_drop, List.length_drop]
  congr 1
  omega

/-- [proved-standard; formal-checked] Cells appended after the last `n` cells leave the last `n` cells unchanged. -/
theorem rtake_rtake_append (l f : List α) (n : ℕ) : (l.rtake n ++ f).rtake n = (l ++ f).rtake n := by
  simp only [List.rtake, List.length_append, List.length_drop, List.drop_append, List.drop_drop]
  congr 2 <;> omega

/-- [proved-standard; formal-checked] The last cell of a list is its last `1` cells. -/
theorem rtake_one (l : List α) : l.rtake 1 = l.getLast?.toList := by
  rw [List.rtake_eq_reverse_take_reverse, List.take_one, List.head?_reverse]
  cases l.getLast? <;> rfl

/-- [proved-standard; formal-checked] Taking one more cell of `s` appends `s[j]`. -/
theorem take_succ_of_lt {s : List α} {j : ℕ} (h : j < s.length) : s.take (j + 1) = s.take j ++ [s[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  rfl

/-- [proved-standard; formal-checked] The last cell of `span.take (i + 1)` is `span[i]`. -/
theorem rtake_one_take_succ {s : List α} {i : ℕ} (h : i < s.length) : (s.take (i + 1)).rtake 1 = [s[i]] := by
  rw [take_succ_of_lt h, List.rtake_concat_succ, List.rtake_zero, List.nil_append]

/-- [proved-standard; formal-checked] An option's list is a singleton exactly when the option holds that cell. -/
theorem toList_eq_singleton {o : Option α} {a : α} : o.toList = [a] ↔ o = some a := by
  cases o <;> simp

/-- [proved-standard; formal-checked] Appending cells one at a time, head of the word last, appends the reversed
word. -/
theorem transportWord_appendCell (w part : List α) :
    transportWord (fun x p => p ++ [x]) w part = part ++ w.reverse := by
  induction w with
  | nil => simp
  | cons x w ih => simp [ih]

end Lists

variable [DecidableEq α]

/-! ## Matches and the located address -/

/-- [definition] **A match of a part on a span** (atlas `context.span-located`): the pair `(j, ℓ)` with
`1 ≤ ℓ ≤ j < |span|`, `ℓ ≤ |part|`, and the part's last `ℓ` cells equal to `span[j−ℓ, j)`. -/
def IsMatch (part span : List α) (j ℓ : ℕ) : Prop :=
  1 ≤ ℓ ∧ ℓ ≤ j ∧ j < span.length ∧ ℓ ≤ part.length ∧ part.rtake ℓ = (span.take j).rtake ℓ

instance (part span : List α) (j ℓ : ℕ) : Decidable (IsMatch part span j ℓ) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

omit [DecidableEq α] in
/-- [proved-standard; formal-checked] The compared window is `span[j−ℓ, j)`. -/
theorem window_eq (span : List α) {j : ℕ} (ℓ : ℕ) (h : j ≤ span.length) :
    (span.take j).rtake ℓ = (span.take j).drop (j - ℓ) := by
  simp only [List.rtake, List.length_take]
  congr 2
  omega

/-- [definition] The candidate addresses `(j, ℓ)` with `j, ℓ < |span|` that match. -/
def matchList (part span : List α) : List (ℕ × ℕ) :=
  (List.range span.length ×ˢ List.range span.length).filter fun p => decide (IsMatch part span p.1 p.2)

/-- [definition] The order of addresses: by length, then by end position. -/
def rank (p : ℕ × ℕ) : ℕ ×ₗ ℕ := toLex (p.2, p.1)

/-- [definition] **The located address** `(j, L)`: the longest match, the latest among the longest; `none` when
nothing matches. -/
def located (part span : List α) : Option (ℕ × ℕ) := (matchList part span).argmax rank

/-- [definition] **The located continuation** `(L, x̂)` of the atlas row: the length and the span's cell after the
occurrence. -/
def continuation (part span : List α) : Option (ℕ × α) :=
  (located part span).bind fun p => span[p.1]?.map fun x => (p.2, x)

/-- [definition] The specification of the located address: a match that no match exceeds in the order
`(ℓ, j)`. -/
def IsLocated (part span : List α) (j ℓ : ℕ) : Prop :=
  IsMatch part span j ℓ ∧ ∀ j' ℓ', IsMatch part span j' ℓ' → ℓ' < ℓ ∨ (ℓ' = ℓ ∧ j' ≤ j)

section Located

variable {part span : List α} {j ℓ j' ℓ' : ℕ}

/-- [proved-derived; formal-checked] The candidate list holds exactly the matches. -/
theorem mem_matchList : (j, ℓ) ∈ matchList part span ↔ IsMatch part span j ℓ := by
  simp only [matchList, List.mem_filter, List.mem_product, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.2.2.1, by have := h.2.1; have := h.2.2.1; omega⟩, h⟩⟩

/-- [proved-derived; formal-checked] The located address is a match. -/
theorem located_isMatch (h : located part span = some (j, ℓ)) : IsMatch part span j ℓ :=
  mem_matchList.1 (List.argmax_mem h)

/-- [proved-derived; formal-checked] No match exceeds the located address in the order `(ℓ, j)`. -/
theorem located_max (h : located part span = some (j, ℓ)) (h' : IsMatch part span j' ℓ') :
    ℓ' < ℓ ∨ (ℓ' = ℓ ∧ j' ≤ j) :=
  Prod.Lex.toLex_le_toLex.1 (List.le_of_mem_argmax (f := rank) (mem_matchList.2 h') h)

/-- [proved-derived; formal-checked] No match is longer than the located one. -/
theorem located_longest (h : located part span = some (j, ℓ)) (h' : IsMatch part span j' ℓ') : ℓ' ≤ ℓ := by
  have := located_max h h'
  omega

/-- [proved-derived; formal-checked] No match of the located length ends later. -/
theorem located_latest (h : located part span = some (j, ℓ)) (h' : IsMatch part span j' ℓ) : j' ≤ j := by
  have := located_max h h'
  omega

/-- [proved-derived; formal-checked] Nothing is located exactly when nothing matches. -/
theorem located_eq_none_iff : located part span = none ↔ ∀ j ℓ, ¬ IsMatch part span j ℓ := by
  rw [located, List.argmax_eq_none, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h j ℓ hm
    exact h _ (mem_matchList.2 hm)
  · rintro h ⟨j, ℓ⟩ hm
    exact h j ℓ (mem_matchList.1 hm)

/-- [proved-derived; formal-checked] The located address is the one match that no match exceeds. -/
theorem located_eq_some_iff : located part span = some (j, ℓ) ↔ IsLocated part span j ℓ := by
  constructor
  · intro h
    exact ⟨located_isMatch h, fun _ _ => located_max h⟩
  · rintro ⟨hm, hmax⟩
    cases h0 : located part span with
    | none => exact absurd hm (located_eq_none_iff.1 h0 j ℓ)
    | some p =>
      obtain ⟨j0, ℓ0⟩ := p
      have a := located_max h0 hm
      have b := hmax j0 ℓ0 (located_isMatch h0)
      have e1 : j0 = j := by omega
      have e2 : ℓ0 = ℓ := by omega
      rw [e1, e2]

/-- [proved-derived; formal-checked] Parts with the same matches are located alike. -/
theorem located_congr {part' : List α} (h : ∀ j ℓ, IsMatch part span j ℓ ↔ IsMatch part' span j ℓ) :
    located part span = located part' span := by
  unfold located matchList
  rw [List.filter_congr fun p _ => decide_eq_decide.2 (h p.1 p.2)]

/-- [proved-derived; formal-checked] The located continuation exists exactly when an address is located. -/
theorem continuation_isSome_iff : (continuation part span).isSome ↔ (located part span).isSome := by
  unfold continuation
  cases h : located part span with
  | none => simp
  | some p =>
    obtain ⟨j, ℓ⟩ := p
    have hj : j < span.length := (located_isMatch h).2.2.1
    simp [List.getElem?_eq_getElem hj]

end Located

/-! ## Nothing located before a recurrence; the length bound -/

section Bounds

variable {part span : List α} {j ℓ L : ℕ}

omit [DecidableEq α] in
/-- [proved-derived; formal-checked] A match's length is at most `|span| − 1`. -/
theorem IsMatch.le_capacity (h : IsMatch part span j ℓ) : ℓ ≤ span.length - 1 := by
  obtain ⟨-, h2, h3, -⟩ := h
  omega

omit [DecidableEq α] in
/-- [proved-derived; formal-checked] A match shortened to any length `m ≥ 1` is a match. -/
theorem IsMatch.shorten (h : IsMatch part span j ℓ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ ℓ) :
    IsMatch part span j m := by
  obtain ⟨-, h2, h3, h4, h5⟩ := h
  refine ⟨hm1, by omega, h3, by omega, ?_⟩
  rw [← rtake_rtake part hm, h5, rtake_rtake _ hm]

omit [DecidableEq α] in
/-- [proved-derived; formal-checked] A match of length one at `i + 1` is the part's last cell at `span[i]`. -/
theorem isMatch_one_iff {i : ℕ} :
    IsMatch part span (i + 1) 1 ↔ i + 1 < span.length ∧ part.getLast? = span[i]? := by
  unfold IsMatch
  constructor
  · rintro ⟨-, -, h3, -, h5⟩
    have hi : i < span.length := by omega
    rw [rtake_one_take_succ hi, rtake_one, toList_eq_singleton] at h5
    exact ⟨h3, by rw [h5, List.getElem?_eq_getElem hi]⟩
  · rintro ⟨h3, h5⟩
    have hi : i < span.length := by omega
    rw [List.getElem?_eq_getElem hi] at h5
    have hne : part ≠ [] := by
      rintro rfl
      simp at h5
    refine ⟨le_rfl, by omega, h3, List.length_pos_iff.2 hne, ?_⟩
    rw [rtake_one_take_succ hi, rtake_one, h5]
    rfl

omit [DecidableEq α] in
/-- [proved-derived; formal-checked] Some match exists exactly when the part's last cell is a cell of the span
that has a cell after it. -/
theorem exists_isMatch_iff :
    (∃ j ℓ, IsMatch part span j ℓ) ↔ ∃ i, i + 1 < span.length ∧ part.getLast? = span[i]? := by
  constructor
  · rintro ⟨j, ℓ, h⟩
    have h1 := h.shorten le_rfl h.1
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by have := h.1; have := h.2.1; omega⟩
    exact ⟨i, isMatch_one_iff.1 h1⟩
  · rintro ⟨i, h⟩
    exact ⟨i + 1, 1, isMatch_one_iff.2 h⟩

/-- [proved-derived; formal-checked] **Nothing is located before a recurrence**: `located part span = none`
exactly when the part has no last cell in `span.dropLast`. -/
theorem located_eq_none_iff_getLast :
    located part span = none ↔ ∀ x ∈ part.getLast?, x ∉ span.dropLast := by
  rw [located_eq_none_iff]
  constructor
  · intro h x hx hmem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
    rw [List.getElem?_dropLast] at hi
    split_ifs at hi with hlt
    · exact h (i + 1) 1 (isMatch_one_iff.2 ⟨by omega, by rw [hi]; exact Option.mem_def.1 hx⟩)
  · intro h j ℓ hm
    obtain ⟨i, hi, hl⟩ := exists_isMatch_iff.1 ⟨j, ℓ, hm⟩
    have hil : i < span.length := by omega
    refine h span[i] ?_ (List.mem_iff_getElem?.2 ⟨i, ?_⟩)
    · rw [hl, List.getElem?_eq_getElem hil]
      rfl
    · rw [List.getElem?_dropLast, if_pos (by omega), List.getElem?_eq_getElem hil]

/-- [proved-derived; formal-checked] Nothing is located before the part's first cell. -/
theorem located_nil : located [] span = none :=
  located_eq_none_iff_getLast.2 (by simp)

/-- [proved-derived; formal-checked] A nonempty part is located nowhere exactly when its last cell is not in
`span.dropLast`. -/
theorem located_eq_none_iff_of_ne_nil (h : part ≠ []) :
    located part span = none ↔ part.getLast h ∉ span.dropLast := by
  rw [located_eq_none_iff_getLast, List.getLast?_eq_some_getLast h]
  simp

/-- [proved-derived; formal-checked] A located address has `1 ≤ L ≤ j < |span|` and `L ≤ |part|`. -/
theorem located_bounds (h : located part span = some (j, L)) :
    1 ≤ L ∧ L ≤ j ∧ j < span.length ∧ L ≤ part.length := by
  obtain ⟨h1, h2, h3, h4, -⟩ := located_isMatch h
  exact ⟨h1, h2, h3, h4⟩

/-- [proved-derived; formal-checked] **The length bound**: a located length is at most `|span| − 1`. -/
theorem located_length_le (h : located part span = some (j, L)) : L ≤ span.length - 1 :=
  (located_isMatch h).le_capacity

end Bounds

/-! ## The retained suffix suffices -/

section Suffix

variable {part span : List α} {j ℓ : ℕ}

omit [DecidableEq α] in
/-- [proved-derived; formal-checked] A part and its last `K ≥ |span| − 1` cells have the same matches. -/
theorem isMatch_rtake_iff {K : ℕ} (hK : span.length - 1 ≤ K) :
    IsMatch (part.rtake K) span j ℓ ↔ IsMatch part span j ℓ := by
  unfold IsMatch
  rw [length_rtake]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hℓK : ℓ ≤ K := by omega
    rw [rtake_rtake _ hℓK] at h5
    exact ⟨h1, h2, h3, by omega, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hℓK : ℓ ≤ K := by omega
    exact ⟨h1, h2, h3, by omega, by rw [rtake_rtake _ hℓK]; exact h5⟩

/-- [proved-derived; formal-checked] The last `K ≥ |span| − 1` cells locate what the whole part locates. -/
theorem located_rtake {K : ℕ} (hK : span.length - 1 ≤ K) : located (part.rtake K) span = located part span :=
  located_congr fun _ _ => isMatch_rtake_iff hK

/-- [proved-derived; formal-checked] **The retained suffix suffices**: the last `|span| − 1` cells locate what the
whole part locates. -/
theorem located_retained_suffix (part span : List α) :
    located part span = located (part.rtake (span.length - 1)) span :=
  (located_rtake le_rfl).symm

/-- [definition] **The retained suffix as a receiver-history compression**
(`Foundation/ReceiverHistoryCompression`): the source is the part, the quotient its last `|span| − 1` cells, a
generator a received cell, and the one receiver the `located` reading. -/
def retainedSuffixCompression (span : List α) :
    ReceiverHistoryCompression α Unit (List α) (List α) (Option (ℕ × ℕ)) where
  present :=
    { quotient := fun part => part.rtake (span.length - 1)
      receiver := fun _ part => located part span
      factor := fun _ suffix => located suffix span
      exact := fun _ _ => located_rtake le_rfl }
  sourceTransport := fun x part => part ++ [x]
  quotientTransport := fun x suffix => (suffix ++ [x]).rtake (span.length - 1)
  generatorExact := fun x part => (rtake_rtake_append part [x] _).symm

/-- [proved-derived; formal-checked] **Future equivalence**: two parts with the same last `|span| − 1` cells give
the same `located` reading after every future `f` (the owner's `quotientEqForcesEverySuccessorFace`). -/
theorem future_equivalent {part' : List α}
    (h : part.rtake (span.length - 1) = part'.rtake (span.length - 1)) (f : List α) :
    located (part ++ f) span = located (part' ++ f) span := by
  have := (retainedSuffixCompression span).quotientEqForcesEverySuccessorFace h () f.reverse
  simpa [retainedSuffixCompression, transportWord_appendCell] using this

end Suffix

/-! ## The continuation law -/

section Continuation

variable {part span : List α} {j ℓ L : ℕ} {x : α}

omit [DecidableEq α] in
/-- [proved-derived; formal-checked] A match followed by the span's next cell grows by one. -/
theorem isMatch_concat (h : IsMatch part span j ℓ) (hx : span[j]? = some x) (hj : j + 1 < span.length) :
    IsMatch (part ++ [x]) span (j + 1) (ℓ + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hx' : span[j] = x := by
    rw [List.getElem?_eq_getElem h3] at hx
    exact Option.some.inj hx
  refine ⟨by omega, by omega, hj, by rw [List.length_append, List.length_singleton]; omega, ?_⟩
  rw [List.rtake_concat_succ, take_succ_of_lt h3, List.rtake_concat_succ, h5, hx']

omit [DecidableEq α] in
/-- [proved-derived; formal-checked] A match of length `ℓ + 1 ≥ 2` of `part ++ [x]` is a match of `part` one
shorter and one earlier. -/
theorem isMatch_of_concat (h : IsMatch (part ++ [x]) span (j + 1) (ℓ + 1)) (hℓ : 1 ≤ ℓ) :
    IsMatch part span j ℓ := by
  obtain ⟨-, h2, h3, h4, h5⟩ := h
  have hj : j < span.length := by omega
  rw [List.length_append, List.length_singleton] at h4
  rw [List.rtake_concat_succ, take_succ_of_lt hj, List.rtake_concat_succ] at h5
  exact ⟨hℓ, by omega, hj, by omega, List.append_inj_left' h5 rfl⟩

/-- [proved-derived; formal-checked] **The continuation law**: when the next cell is `x̂ = span[j]` and
`j + 1 < |span|`, the address moves to `(j + 1, L + 1)`, again the longest and the latest among the longest. -/
theorem located_concat_of_continues (h : located part span = some (j, L)) (hx : span[j]? = some x)
    (hj : j + 1 < span.length) : located (part ++ [x]) span = some (j + 1, L + 1) := by
  rw [located_eq_some_iff]
  refine ⟨isMatch_concat (located_isMatch h) hx hj, fun j' ℓ' hm => ?_⟩
  have hL := (located_isMatch h).1
  rcases Nat.lt_or_ge ℓ' 2 with hlt | hge
  · left
    omega
  · obtain ⟨j0, rfl⟩ : ∃ j0, j' = j0 + 1 := ⟨j' - 1, by have := hm.2.1; omega⟩
    obtain ⟨ℓ0, rfl⟩ : ∃ ℓ0, ℓ' = ℓ0 + 1 := ⟨ℓ' - 1, by omega⟩
    have := located_max h (isMatch_of_concat hm (by omega))
    omega

/-- [proved-derived; formal-checked] The next address, continued or not, is located from the retained suffix and
the new cell alone. -/
theorem located_concat_retained (part span : List α) (x : α) :
    located (part ++ [x]) span = located (part.rtake (span.length - 1) ++ [x]) span := by
  rw [← located_rtake (part := part ++ [x]) le_rfl, ← rtake_rtake_append, located_rtake le_rfl]

end Continuation

/-! ## The incremental reader -/

/-- [definition] **The reader's state** (the Rust `SpanReading`): the last at most `|span| − 1` cells, the count of
cells received, and the current address (the Rust `at`). -/
structure ReaderState (α : Type*) where
  /-- The retained suffix. -/
  suffix : List α
  /-- The count of cells received: carried, never read by `located`. -/
  received : ℕ
  /-- The current located address `(j, L)`. -/
  address : Option (ℕ × ℕ)
  deriving DecidableEq

/-- [definition] The state before the part's first cell. -/
def ReaderState.empty : ReaderState α := ⟨[], 0, none⟩

/-- [definition] The address after the cell `x`: the continuation law when it applies, otherwise located anew on
the new suffix. -/
def nextAddress (span suffix : List α) (x : α) : Option (ℕ × ℕ) → Option (ℕ × ℕ)
  | some (j, L) =>
    if span[j]? = some x ∧ j + 1 < span.length then some (j + 1, L + 1) else located suffix span
  | none => located suffix span

/-- [definition] **The reader's step on one cell** (the Rust `read`). -/
def step (span : List α) (s : ReaderState α) (x : α) : ReaderState α where
  suffix := (s.suffix ++ [x]).rtake (span.length - 1)
  received := s.received + 1
  address := nextAddress span ((s.suffix ++ [x]).rtake (span.length - 1)) x s.address

/-- [definition] The reader after a list of cells, from the empty state. -/
def read (span cells : List α) : ReaderState α := cells.foldl (step span) ReaderState.empty

section Reader

/-- [proved-derived; formal-checked] **The incremental reader is the located address**: after any list of cells
the suffix is its last `|span| − 1` cells, the count is its length, and the address is `located cells span`. -/
theorem read_eq (span cells : List α) :
    read span cells = ⟨cells.rtake (span.length - 1), cells.length, located cells span⟩ := by
  induction cells using List.reverseRecOn with
  | nil => simp [read, ReaderState.empty, located_nil]
  | append_singleton cells x ih =>
    simp only [read] at ih ⊢
    rw [List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, step, rtake_rtake_append, List.length_append,
      List.length_singleton, ReaderState.mk.injEq, true_and]
    have hr : located ((cells ++ [x]).rtake (span.length - 1)) span = located (cells ++ [x]) span :=
      located_rtake le_rfl
    cases h : located cells span with
    | none => simp [nextAddress, hr]
    | some p =>
      obtain ⟨j, L⟩ := p
      simp only [nextAddress]
      split_ifs with hc
      · exact (located_concat_of_continues h hc.1 hc.2).symm
      · exact hr

/-- [proved-derived; formal-checked] The reader keeps the last `min(|cells|, |span| − 1)` cells. -/
theorem read_suffix_length (span cells : List α) :
    (read span cells).suffix.length = min cells.length (span.length - 1) := by
  rw [read_eq, length_rtake]

/-- [proved-derived; formal-checked] The reader's address is `located` of its own retained suffix. -/
theorem read_address_eq_located_suffix (span cells : List α) :
    (read span cells).address = located (read span cells).suffix span := by
  rw [read_eq]
  exact (located_rtake le_rfl).symm

/-- [proved-derived; formal-checked] One step reads the suffix and the address, never the count. -/
theorem step_received_unread (span u : List α) (r r' : ℕ) (a : Option (ℕ × ℕ)) (x : α) :
    (step span ⟨u, r, a⟩ x).suffix = (step span ⟨u, r', a⟩ x).suffix ∧
      (step span ⟨u, r, a⟩ x).address = (step span ⟨u, r', a⟩ x).address :=
  ⟨rfl, rfl⟩

/-- [proved-derived; formal-checked] **The count is carried and never read**: states that differ only in their
count read every later list of cells to the same suffix and address. -/
theorem foldl_received_unread (span f u : List α) (r r' : ℕ) (a : Option (ℕ × ℕ)) :
    (f.foldl (step span) ⟨u, r, a⟩).suffix = (f.foldl (step span) ⟨u, r', a⟩).suffix ∧
      (f.foldl (step span) ⟨u, r, a⟩).address = (f.foldl (step span) ⟨u, r', a⟩).address := by
  induction f generalizing u r r' a with
  | nil => exact ⟨rfl, rfl⟩
  | cons x f ih =>
    exact ih ((u ++ [x]).rtake (span.length - 1))
      (r + 1) (r' + 1) (nextAddress span ((u ++ [x]).rtake (span.length - 1)) x a)

end Reader

/-! ## A witness -/

/-- [definition] The witness span `5, 1, 2, 7, 2, 9`. -/
def witnessSpan : List ℕ := [5, 1, 2, 7, 2, 9]

/-- [proved-derived; formal-checked] The longest match is not the latest occurrence of the last cell: `1, 2` is
located at `(3, 2)`, while the latest `2` before the span's end gives only `(5, 1)`. -/
theorem witness_longest_not_latest :
    located [1, 2] witnessSpan = some (3, 2) ∧ IsMatch [1, 2] witnessSpan 5 1 ∧
      ¬ IsMatch [1, 2] witnessSpan 5 2 := by
  decide

/-- [proved-derived; formal-checked] A continuation: the next cell is `x̂ = 7`, and the address moves to
`(4, 3)`. -/
theorem witness_continues :
    continuation [1, 2] witnessSpan = some (2, 7) ∧ located [1, 2, 7] witnessSpan = some (4, 3) := by
  decide

/-- [proved-derived; formal-checked] A break that relocates: after `1, 2, 7` the span's next cell is `2`, the
reading part gives `1`, and the address is located anew at `(2, 1)`. -/
theorem witness_break :
    witnessSpan[4]? ≠ some 1 ∧ located [1, 2, 7, 1] witnessSpan = some (2, 1) := by
  decide

/-- [proved-derived; formal-checked] A run of the span with no cell after it locates nothing. -/
theorem witness_no_cell_after : located [3, 1, 2, 7, 2, 9] witnessSpan = none := by
  decide

/-- [proved-derived; formal-checked] The incremental reader over `1, 2, 7, 1` and over `3, 1, 2, 7, 2, 9`, the
second keeping its last five cells. -/
theorem witness_reader :
    read witnessSpan [1, 2, 7, 1] = ⟨[1, 2, 7, 1], 4, some (2, 1)⟩ ∧
      read witnessSpan [3, 1, 2, 7, 2, 9] = ⟨[1, 2, 7, 2, 9], 6, none⟩ := by
  decide

/-- [proved-derived; formal-checked] Among the longest, the latest: the owner's restore test, where `1, 2` on
`0, 1, 2, 1, 2, 3` is located at `(5, 2)` and not at `(3, 2)`. -/
theorem witness_latest_among_longest :
    located [1, 2] [0, 1, 2, 1, 2, 3] = some (5, 2) ∧ IsMatch [1, 2] [0, 1, 2, 1, 2, 3] 3 2 := by
  decide

/-- [proved-derived; formal-checked] The owner's snapshot test: `9, 8, 1, 2, 3` on `0, 1, 2, 3, 4` keeps
`8, 1, 2, 3` and five received cells, and reading `4, 9, 0, 1` from the full part and from the retained suffix
gives one address. -/
theorem witness_rust_snapshot :
    read [0, 1, 2, 3, 4] [9, 8, 1, 2, 3] = ⟨[8, 1, 2, 3], 5, some (4, 3)⟩ ∧
      located ([9, 8, 1, 2, 3] ++ [4, 9, 0, 1]) [0, 1, 2, 3, 4] =
        located ([8, 1, 2, 3] ++ [4, 9, 0, 1]) [0, 1, 2, 3, 4] := by
  decide

end Holonics.Compression.Landmark.SpanSuffix
