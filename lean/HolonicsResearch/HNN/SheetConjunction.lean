import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Locked sheets make conjunctions in their transitions, which no reading of the lag-residue counts makes

The torsion record of October 22 (`research/records/2026-10-22_ORDER_IS_TORSION_AND_SUBGRAIN_INFORMATION_DISSOLVES_INTO_THE_CARRIED_RESIDUE.md`,
§6, item 6, "Where the source must enter") read the source's three candidate entries. Moves with one linear part of
finite order reach a state that is a function of the (symbol, lag residue) counts
(`Geometry/ScrewTorsion.laggedRun_lag_residue`, `laggedRun_eq_of_counts`): every linear reading of such a stream is
`c₀ + Σ_(r < N) Σ_a c(r, a) n(a, r)`, with `n(a, r)` the cells `k < t` at lag residue `(t − 1 − k) mod N = r` carrying
`a`. In the locked regime the sheets move by `σ′ = sign(h_s + J_s σ)`, a threshold gate, "so the transitions make
conjunctions"; and "a readout linear in the sheets is additive in them, so the conjunctions must be made in the
transitions". #410's box owes both halves.

[proved-derived; formal-checked] What is proved.

1. **A count reading is additive over cells** (`lagCount`, `countReading`, `lagCount_exchange`,
   `countReading_exchange`): four streams whose symbols at each cell agree as a pair (`{u₁ k, u₂ k} = {u₃ k, u₄ k}`)
   have counts `n₁ + n₂ = n₃ + n₄` at every (symbol, residue), so every count reading obeys
   `R(u₁) + R(u₂) = R(u₃) + R(u₄)`. The streams `aa`, `bb`, `ab`, `ba`, which differ only at the last two cells, are
   such a quadruple (`swapStream`, `swapStream_cell`).
2. **No count reading reads a conjunction** (`no_countReading_reads_conjunction`): for two symbols `a ≠ b`, any modulus
   `N` and any length, no reading `c₀ + Σ c(r, a) n(a, r)` equals the indicator that the last two symbols are both
   `a`: it would give `1 + 0 = 0 + 0` on the quadruple.
3. **No threshold of a count reading reads an agreement** (`no_countThreshold_reads_agreement`): no reading's sign
   tells whether the last two symbols agree on being `a`; the quadruple gives two positive and two nonpositive values
   with equal sums. It is the counts' face of `HNN/Floquet.no_linear_threshold_reads_relative_phase`.
4. **The sheets make both** (`sgn`, `sheetStep`, `sheetRun`, `conjunctionSheets`, `conjunction_sheet_reads`,
   `agreementSheets`, `agreement_sheet_reads`): two locks moving by `σ′ = sign(h_s + J_s σ)`, the first copying whether
   the symbol is `a` and the second gated by the first, read at every cell `t + 2` the conjunction (`h_a = 0`,
   `J_a = 1`, `h_(≠a) = −1`, `J_(≠a) = 0`) or the agreement (`h = 0`, `J_a = 1`, `J_(≠a) = −1`) of the two symbols
   before it, from any opening sheets. The reading is one sheet, a linear reading of the sheets.
5. **So the sheets' state is not a count reading** (`conjunction_sheet_not_countReading`,
   `agreement_sheet_not_countThreshold`): the second sheet of either witness is read by no count reading (resp. no
   count reading's sign), whatever the modulus.

Limits. The sheets are the locked regime's transitions on `{−1, 1}` (the lock read as its sign, `sign 0 = −1`); the
pump, the lock's bifurcation and the passage from amplitudes to sheets (`Holonics/HNN/Ring.locked_sheet_receiver_face`)
are not re-derived. The count readings are the linear readings of a stream with one linear part of finite order, by
`laggedRun_lag_residue`, which this file restates as the count it reads rather than imports. The capacity count
(`2^L` configurations of `L` locks, `L²` additions a cell) is not here.

The computational object is the helical pair interaction: a lock's sheet is a parametron's half-turn side, the
coupling `J_s` the pair contacts between locks, which the symbol selects; the count reading is the shared-linear-part
stream's face. Of the winding guide's six general objects this touches the helix (the lag residue on the shared
part's period), the pair (the contacts `J_s` the symbol selects) and faces and placement (the sheets as the locks'
faces); the cell holonomy, the tube and the tower thread stay attached.

Consumers: #410's box on the locked sheets (#73); the atlas rows `motion.lag-residue-factorization`,
`parametron.locked-sheet-face`, `parametron.no-linear-relative-phase` and `hnn.keyed-modes-move`, beside
`Geometry/ScrewTorsion` and `HNN/Floquet`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.SheetConjunction

open Finset

variable {α : Type*} [DecidableEq α]

/-! ## 1. The lag-residue counts and their readings -/

/-- [definition] **The lag-residue count** `n(a, r)`: the cells `k < t` at lag residue `(t − 1 − k) mod N = r` that
carry `a` (the count of `Geometry/ScrewTorsion.laggedRun_lag_residue`). -/
def lagCount (N t : ℕ) (u : ℕ → α) (r : ℕ) (a : α) : ℕ :=
  ((Finset.range t).filter (fun k => (t - 1 - k) % N = r ∧ u k = a)).card

/-- [definition] **A count reading** `c₀ + Σ_(r < N) Σ_a c(r, a) n(a, r)`: by `laggedRun_lag_residue`, every linear
reading of a stream of moves with one linear part `M`, `M^N = 1`, has this form. -/
def countReading [Fintype α] (N t : ℕ) (c₀ : ℝ) (c : ℕ → α → ℝ) (u : ℕ → α) : ℝ :=
  c₀ + ∑ r ∈ Finset.range N, ∑ a : α, c r a * (lagCount N t u r a : ℝ)

/-- [proved-derived] **Counts are additive over cells**: where the four streams' symbols agree as a pair at every cell,
`n₁ + n₂ = n₃ + n₄` at every (symbol, residue). -/
theorem lagCount_exchange (N t : ℕ) {u₁ u₂ u₃ u₄ : ℕ → α}
    (hcell : ∀ k s, (if u₁ k = s then 1 else 0) + (if u₂ k = s then 1 else 0) =
      (if u₃ k = s then 1 else 0) + (if u₄ k = s then (1 : ℕ) else 0)) (r : ℕ) (s : α) :
    lagCount N t u₁ r s + lagCount N t u₂ r s = lagCount N t u₃ r s + lagCount N t u₄ r s := by
  unfold lagCount
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : (t - 1 - k) % N = r
  · simp only [hk, true_and]
    exact hcell k s
  · simp [hk]

/-- [proved-derived] **A count reading is additive over cells**: `R(u₁) + R(u₂) = R(u₃) + R(u₄)` on such a
quadruple. -/
theorem countReading_exchange [Fintype α] (N t : ℕ) (c₀ : ℝ) (c : ℕ → α → ℝ) {u₁ u₂ u₃ u₄ : ℕ → α}
    (hcell : ∀ k s, (if u₁ k = s then 1 else 0) + (if u₂ k = s then 1 else 0) =
      (if u₃ k = s then 1 else 0) + (if u₄ k = s then (1 : ℕ) else 0)) :
    countReading N t c₀ c u₁ + countReading N t c₀ c u₂ =
      countReading N t c₀ c u₃ + countReading N t c₀ c u₄ := by
  have hn : ∀ r s, (lagCount N t u₁ r s : ℝ) + lagCount N t u₂ r s =
      lagCount N t u₃ r s + lagCount N t u₄ r s := by
    intro r s
    exact_mod_cast lagCount_exchange N t hcell r s
  have e : ∀ v w : ℕ → α,
      (∑ r ∈ Finset.range N, ∑ a : α, c r a * (lagCount N t v r a : ℝ)) +
        (∑ r ∈ Finset.range N, ∑ a : α, c r a * (lagCount N t w r a : ℝ)) =
      ∑ r ∈ Finset.range N, ∑ a : α, c r a * ((lagCount N t v r a : ℝ) + lagCount N t w r a) := by
    intro v w
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  unfold countReading
  have h12 := e u₁ u₂
  have h34 := e u₃ u₄
  simp_rw [hn] at h12
  linarith

/-- [definition] **The stream `x y` after a filler**: the symbols `x` and `y` at cells `t` and `t + 1`, the filler `f`
elsewhere. -/
def swapStream (f x y : α) (t : ℕ) (k : ℕ) : α := if k = t then x else if k = t + 1 then y else f

/-- [proved-derived] **The quadruple `aa`, `bb`, `ab`, `ba` agrees as pairs at every cell.** -/
theorem swapStream_cell (f a b : α) (t k : ℕ) (s : α) :
    (if swapStream f a a t k = s then 1 else 0) + (if swapStream f b b t k = s then 1 else 0) =
      (if swapStream f a b t k = s then 1 else 0) + (if swapStream f b a t k = s then (1 : ℕ) else 0) := by
  unfold swapStream
  by_cases h1 : k = t
  · simp only [h1, if_true]
  · by_cases h2 : k = t + 1
    · simp only [if_neg h1, if_pos h2]
      exact add_comm _ _
    · simp only [h1, h2, if_false]

/-! ## 2. What no count reading reads -/

/-- [proved-derived; formal-checked] **No count reading reads a conjunction**: for `a ≠ b`, no reading
`c₀ + Σ c(r, a) n(a, r)` of the cells `k < t + 2` equals the indicator that cells `t` and `t + 1` both carry `a`. -/
theorem no_countReading_reads_conjunction [Fintype α] {a b : α} (hab : a ≠ b) (N t : ℕ) (c₀ : ℝ)
    (c : ℕ → α → ℝ) :
    ¬ ∀ u : ℕ → α, countReading N (t + 2) c₀ c u = if u t = a ∧ u (t + 1) = a then 1 else 0 := by
  intro h
  have hx := countReading_exchange N (t + 2) c₀ c (swapStream_cell b a b t)
  rw [h, h, h, h] at hx
  simp [swapStream, hab.symm] at hx

/-- [proved-derived; formal-checked] **No threshold of a count reading reads an agreement**: for `a ≠ b`, no reading's
sign tells whether cells `t` and `t + 1` agree on carrying `a`. -/
theorem no_countThreshold_reads_agreement [Fintype α] {a b : α} (hab : a ≠ b) (N t : ℕ) (c₀ : ℝ)
    (c : ℕ → α → ℝ) :
    ¬ ∀ u : ℕ → α, (0 < countReading N (t + 2) c₀ c u ↔ (u t = a ↔ u (t + 1) = a)) := by
  intro h
  have hx := countReading_exchange N (t + 2) c₀ c (swapStream_cell b a b t)
  have haa := (h (swapStream b a a t)).mpr (by simp [swapStream])
  have hbb := (h (swapStream b b b t)).mpr (by simp [swapStream, hab.symm])
  have hab' : ¬ 0 < countReading N (t + 2) c₀ c (swapStream b a b t) := by
    rw [h]
    simp [swapStream, hab.symm]
  have hba : ¬ 0 < countReading N (t + 2) c₀ c (swapStream b b a t) := by
    rw [h]
    simp [swapStream, hab.symm]
  have h1 := not_lt.mp hab'
  have h2 := not_lt.mp hba
  linarith

/-! ## 3. The sheets make them -/

/-- [definition] **The lock's sign**, `1` above zero and `−1` otherwise. -/
def sgn (x : ℤ) : ℤ := if 0 < x then 1 else -1

/-- [definition] **The locked sheets' transition** `σ′_i = sign(h_s i + Σ_j J_s i j σ_j)`: a threshold gate whose bias and
contacts the symbol selects. -/
def sheetStep {L : ℕ} (h : α → Fin L → ℤ) (J : α → Fin L → Fin L → ℤ) (s : α) (σ : Fin L → ℤ) : Fin L → ℤ :=
  fun i => sgn (h s i + ∑ j, J s i j * σ j)

/-- [definition] **The sheets' run** over a stream, from the opening sheets `σ₀`. -/
def sheetRun {L : ℕ} (h : α → Fin L → ℤ) (J : α → Fin L → Fin L → ℤ) (σ₀ : Fin L → ℤ) (u : ℕ → α) :
    ℕ → Fin L → ℤ
  | 0 => σ₀
  | t + 1 => sheetStep h J (u t) (sheetRun h J σ₀ u t)

/-- [definition] **The conjunction's sheets**: the first lock copies whether the symbol is `a`; the second follows the
first under `a` and falls under any other symbol. -/
def conjunctionSheets (a : α) : (α → Fin 2 → ℤ) × (α → Fin 2 → Fin 2 → ℤ) :=
  (fun s i => if i = 0 then (if s = a then 1 else -1) else (if s = a then 0 else -1),
    fun s i j => if i = 1 ∧ j = 0 ∧ s = a then 1 else 0)

/-- [definition] **The agreement's sheets**: the first lock copies whether the symbol is `a`; the second follows the
first under `a` and turns it over under any other symbol. -/
def agreementSheets (a : α) : (α → Fin 2 → ℤ) × (α → Fin 2 → Fin 2 → ℤ) :=
  (fun s i => if i = 0 then (if s = a then 1 else -1) else 0,
    fun s i j => if i = 1 ∧ j = 0 then (if s = a then 1 else -1) else 0)

/-- [proved-derived] The first lock of either witness copies whether the last symbol is `a`. -/
theorem conjunction_first_sheet (a : α) (σ₀ : Fin 2 → ℤ) (u : ℕ → α) (t : ℕ) :
    sheetRun (conjunctionSheets a).1 (conjunctionSheets a).2 σ₀ u (t + 1) 0 = if u t = a then 1 else -1 := by
  show sgn _ = _
  simp only [conjunctionSheets, Fin.sum_univ_two]
  by_cases h : u t = a <;> simp [h, sgn]

/-- [proved-derived; formal-checked] **The second sheet reads the conjunction** of the two symbols before it, from any
opening sheets: `σ₁(t + 2) = 1` exactly when cells `t` and `t + 1` both carry `a`. -/
theorem conjunction_sheet_reads (a : α) (σ₀ : Fin 2 → ℤ) (u : ℕ → α) (t : ℕ) :
    sheetRun (conjunctionSheets a).1 (conjunctionSheets a).2 σ₀ u (t + 2) 1 =
      if u t = a ∧ u (t + 1) = a then 1 else -1 := by
  have h0 := conjunction_first_sheet a σ₀ u t
  show sgn _ = _
  simp only [conjunctionSheets, Fin.sum_univ_two] at h0 ⊢
  change sgn (_ + (_ * sheetRun _ _ σ₀ u (t + 1) 0 + _ * sheetRun _ _ σ₀ u (t + 1) 1)) = _
  rw [h0]
  by_cases h1 : u (t + 1) = a <;> by_cases h2 : u t = a <;> simp [h1, h2, sgn]

/-- [proved-derived] The agreement witness's first lock copies whether the last symbol is `a`. -/
theorem agreement_first_sheet (a : α) (σ₀ : Fin 2 → ℤ) (u : ℕ → α) (t : ℕ) :
    sheetRun (agreementSheets a).1 (agreementSheets a).2 σ₀ u (t + 1) 0 = if u t = a then 1 else -1 := by
  show sgn _ = _
  simp only [agreementSheets, Fin.sum_univ_two]
  by_cases h : u t = a <;> simp [h, sgn]

/-- [proved-derived; formal-checked] **The second sheet reads the agreement** of the two symbols before it, from any
opening sheets: `σ₁(t + 2) = 1` exactly when cells `t` and `t + 1` agree on carrying `a`. -/
theorem agreement_sheet_reads (a : α) (σ₀ : Fin 2 → ℤ) (u : ℕ → α) (t : ℕ) :
    sheetRun (agreementSheets a).1 (agreementSheets a).2 σ₀ u (t + 2) 1 =
      if (u t = a ↔ u (t + 1) = a) then 1 else -1 := by
  have h0 := agreement_first_sheet a σ₀ u t
  show sgn _ = _
  simp only [agreementSheets, Fin.sum_univ_two] at h0 ⊢
  change sgn (_ + (_ * sheetRun _ _ σ₀ u (t + 1) 0 + _ * sheetRun _ _ σ₀ u (t + 1) 1)) = _
  rw [h0]
  by_cases h1 : u (t + 1) = a <;> by_cases h2 : u t = a <;> simp [h1, h2, sgn]

/-! ## 4. So the sheets' state is not a count reading -/

/-- [proved-derived; formal-checked] **The conjunction's sheet is no count reading**: for `a ≠ b`, no reading
`c₀ + Σ c(r, a) n(a, r)` of the cells before `t + 2` equals the second sheet's indicator, whatever the modulus `N`. -/
theorem conjunction_sheet_not_countReading [Fintype α] {a b : α} (hab : a ≠ b) (σ₀ : Fin 2 → ℤ) (N t : ℕ)
    (c₀ : ℝ) (c : ℕ → α → ℝ) :
    ¬ ∀ u : ℕ → α, countReading N (t + 2) c₀ c u =
      if sheetRun (conjunctionSheets a).1 (conjunctionSheets a).2 σ₀ u (t + 2) 1 = 1 then 1 else 0 := by
  intro h
  refine no_countReading_reads_conjunction hab N t c₀ c (fun u => ?_)
  rw [h u, conjunction_sheet_reads]
  by_cases hc : u t = a ∧ u (t + 1) = a <;> simp [hc]

/-- [proved-derived; formal-checked] **The agreement's sheet is no count threshold**: for `a ≠ b`, no reading's sign
equals the second sheet's side, whatever the modulus `N`. -/
theorem agreement_sheet_not_countThreshold [Fintype α] {a b : α} (hab : a ≠ b) (σ₀ : Fin 2 → ℤ) (N t : ℕ)
    (c₀ : ℝ) (c : ℕ → α → ℝ) :
    ¬ ∀ u : ℕ → α, (0 < countReading N (t + 2) c₀ c u ↔
      sheetRun (agreementSheets a).1 (agreementSheets a).2 σ₀ u (t + 2) 1 = 1) := by
  intro h
  refine no_countThreshold_reads_agreement hab N t c₀ c (fun u => ?_)
  rw [h u, agreement_sheet_reads]
  by_cases hc : (u t = a ↔ u (t + 1) = a)
  · simp only [hc, if_true]
  · norm_num [hc]

end Holonics.HNN.SheetConjunction
