import Mathlib
import Holonics.Aeon.Clock.CarryWord

/-!
# The carry word of an irrational rate has `n + 1` factors of length `n`

[definition] Source: §5 of
`research/records/2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS.md`
and the closing `[open]` paragraph of `Holonics/Aeon/Clock/CarryWord`, which names Sturmian factor
complexity `n + 1` (Morse–Hedlund 1940) beside the three-distance theorem.

The carry word of a rate `0 ≤ α < 1` from open phase `ρ` is `s_k = carry α ρ k`
(`CarryWord.carry`), the mechanical word of slope `α`. Its factor of length `n` at the tick `k` is
`(s_k, …, s_(k+n−1))`.

[proved-derived; formal-checked] What is proved.

1. **A letter is a place on the circle** (`carry_eq_one_iff`): the tick `m` carries exactly when
   the open phase of the reading stands in the last arc, `1 − α ≤ fract (mα + ρ)`.
2. **A letter `i` ticks later is read from two cuts** (`letter_iff`). With the cuts
   `cut α j = fract (−jα)`, the letter at `i` ticks past a reading of open phase `t` is decided by
   whether `cut α (i + 1) ≤ t` and whether `cut α i ≤ t`: the arc from the cut `i + 1` forward to
   the cut `i` is where the letter is `1`.
3. **The factor is read from the arc the reading stands in** (`carry_eq_of_arcIndex_eq`). The
   count of cuts `j ≤ n` at or below the open phase, `arcIndex α n t`, takes values in
   `1, …, n + 1` (`arcIndex_pos`, `arcIndex_le`), and two readings with one count stand on the same
   side of every cut (`cut_le_iff_of_arcIndex_eq`), so their factors of length `n` agree.
4. **At most `n + 1` factors** (`ncard_factors_le`): the set of factors of length `n` is finite
   with at most `n + 1` elements, for every rate `0 ≤ α < 1`, rational or not, and every phase.
5. **A word whose factor count does not grow is eventually periodic** (Morse–Hedlund's step,
   `eventually_periodic_of_ncard_le`, for any word `ℤ → A`). If the factors of length `n + 1` are
   no more than those of length `n`, dropping the last letter is injective on them, so a factor of
   length `n` has one next letter (`next_eq_of_ncard_le`) and the factor one tick later is decided
   (`factorAt_succ_eq`, `factorAt_add_eq`); finitely many factors repeat at two ticks, and from
   there the word repeats.
6. **An irrational rate has `n + 1` factors of length `n`, every `n`** (`ncard_factors_eq`): the
   word never locks (`CarryWord.not_eventually_periodic_of_irrational`), so its count grows by at
   least one a letter from the one empty factor, and item 4 bounds it above.

**Limits.** A rational rate `p/q` in lowest terms attains `min(n + 1, q)`; that count is not
proved here (item 4 gives `n + 1` above). Which arc carries which factor, and the factor's
frequency as its arc's length, are not stated. Rates outside `[0, 1)` differ by the constant
`windings α` in every letter (`CarryWord.carry_eq_windings_add_carry`) and are not restated.

**Part of the line served.** Navigators: a rate clock; terrain: the unit clock's sections;
landmarks: the cuts `−jα`, where two factors part; kernel: readings in one arc, which no factor of
length `n` distinguishes; cokernel: none stated here.

The computational object is the helical pair interaction: the unit clock and the rate-`α` clock on
the torus of their joint motion. Of the six objects of the winding guide this module touches the
helix (circle + carry: a letter is a carry) and faces and placement (the arcs are the faces a
factor reads); the pair, cell holonomy, the tube and the tower thread stay attached and are not
used here.

Consumers: `Holonics/Aeon/Clock/CarryWord` (its closing paragraph); the atlas row
`rotation.mechanical-carry`.

No `sorry`, no `axiom`, no `native_decide`.
-/

set_option linter.dupNamespace false

namespace Holonics.Aeon.Clock.SturmianComplexity

open Finset
open Holonics.Aeon.Clock.CarryWord (carry helixReading_eq carry_eq_jointCarry carry_mem_zero_one
  not_eventually_periodic_of_irrational)

/-! ## 1. A letter is a place on the circle -/

/-- [proved-derived; formal-checked] The open phase of a difference: the difference of the open
phases, with one turn added where it would be negative. -/
theorem fract_sub_cases (u v : ℝ) :
    Int.fract (u - v) = if Int.fract v ≤ Int.fract u then Int.fract u - Int.fract v
      else Int.fract u - Int.fract v + 1 := by
  have h1 := Int.fract_nonneg u
  have h2 := Int.fract_lt_one u
  have h3 := Int.fract_nonneg v
  have h4 := Int.fract_lt_one v
  split_ifs with h
  · rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⌊u⌋ - ⌊v⌋, ?_⟩
    simp only [Int.fract]
    push_cast
    ring
  · have h' : Int.fract u < Int.fract v := not_le.mp h
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⌊u⌋ - ⌊v⌋ - 1, ?_⟩
    simp only [Int.fract]
    push_cast
    ring

/-- [proved-derived; formal-checked] **A carry is a place**: below one turn per tick, the tick `m`
carries exactly when the reading's open phase stands in the last arc of length `α`. -/
theorem carry_eq_one_iff {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) (m : ℤ) :
    carry α ρ m = 1 ↔ 1 - α ≤ Int.fract ((m : ℝ) * α + ρ) := by
  rw [carry_eq_jointCarry h0 h1, Winding.carry, helixReading_eq,
    Int.fract_eq_self.mpr ⟨h0, h1⟩, Int.floor_eq_iff]
  have h2 := Int.fract_lt_one ((m : ℝ) * α + ρ)
  constructor
  · rintro ⟨h, _⟩
    push_cast at h
    linarith
  · intro h
    push_cast
    constructor <;> linarith

/-- [definition] **The cut `j`**: the open phase from which `j` ticks reach the section. -/
noncomputable def cut (α : ℝ) (j : ℕ) : ℝ := Int.fract (-((j : ℝ) * α))

/-- [proved-derived; formal-checked] **A letter `i` ticks later is read from the cuts `i` and
`i + 1`**: it is `1` on the arc from the cut `i + 1` forward to the cut `i`. -/
theorem letter_iff {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (x : ℝ) (i : ℕ) :
    (1 - α ≤ Int.fract (x + (i : ℝ) * α)) ↔
      if cut α (i + 1) ≤ cut α i then
        (cut α (i + 1) ≤ Int.fract x ∧ ¬ cut α i ≤ Int.fract x)
      else (cut α (i + 1) ≤ Int.fract x ∨ ¬ cut α i ≤ Int.fract x) := by
  have ht0 := Int.fract_nonneg x
  have ht1 := Int.fract_lt_one x
  have hp0 : 0 ≤ cut α i := Int.fract_nonneg _
  have hp1 : cut α i < 1 := Int.fract_lt_one _
  have hF : Int.fract (x + (i : ℝ) * α) =
      if cut α i ≤ Int.fract x then Int.fract x - cut α i else Int.fract x - cut α i + 1 := by
    have h := fract_sub_cases x (-((i : ℝ) * α))
    rw [sub_neg_eq_add] at h
    exact h
  have hP : cut α (i + 1) = if α ≤ cut α i then cut α i - α else cut α i - α + 1 := by
    have h := fract_sub_cases (-((i : ℝ) * α)) α
    rw [Int.fract_eq_self.mpr ⟨h0, h1⟩] at h
    have e : -(((i + 1 : ℕ) : ℝ) * α) = -((i : ℝ) * α) - α := by push_cast; ring
    unfold cut
    rw [e]
    exact h
  by_cases c1 : α ≤ cut α i
  · rw [if_pos c1] at hP
    have hle : cut α (i + 1) ≤ cut α i := by linarith
    rw [if_pos hle]
    by_cases c2 : cut α i ≤ Int.fract x
    · rw [if_pos c2] at hF
      constructor
      · intro h
        exfalso
        linarith
      · rintro ⟨_, h⟩
        exact absurd c2 h
    · rw [if_neg c2] at hF
      have c2' : Int.fract x < cut α i := not_le.mp c2
      constructor
      · intro h
        exact ⟨by linarith, c2⟩
      · rintro ⟨h, _⟩
        linarith
  · rw [if_neg c1] at hP
    have c1' : cut α i < α := not_le.mp c1
    have hnle : ¬ cut α (i + 1) ≤ cut α i := not_le.mpr (by linarith)
    rw [if_neg hnle]
    by_cases c2 : cut α i ≤ Int.fract x
    · rw [if_pos c2] at hF
      constructor
      · intro h
        left
        linarith
      · rintro (h | h)
        · linarith
        · exact absurd c2 h
    · rw [if_neg c2] at hF
      have c2' : Int.fract x < cut α i := not_le.mp c2
      constructor
      · intro _
        right
        exact c2
      · intro _
        linarith

/-! ## 2. The arc a reading stands in decides its factor -/

/-- [definition] **The arc of a reading**: the count of cuts `j ≤ n` at or below its open phase. -/
noncomputable def arcIndex (α : ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  ((range (n + 1)).filter (fun j => cut α j ≤ t)).card

/-- [proved-derived; formal-checked] The cut `0` is the section, so the count is at least one. -/
theorem arcIndex_pos (α : ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 1 ≤ arcIndex α n t := by
  refine Finset.card_pos.mpr ⟨0, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩⟩
  simpa [cut] using ht

/-- [proved-derived; formal-checked] The count is at most the number of cuts. -/
theorem arcIndex_le (α : ℝ) (n : ℕ) (t : ℝ) : arcIndex α n t ≤ n + 1 := by
  have h := card_filter_le (range (n + 1)) (fun j => cut α j ≤ t)
  rw [card_range] at h
  exact h

/-- [proved-derived; formal-checked] **One count, one side of every cut**: the cuts at or below a
phase are nested as the phase grows, so equal counts are equal sets. -/
theorem cut_le_iff_of_arcIndex_eq {α : ℝ} {n : ℕ} {t t' : ℝ}
    (h : arcIndex α n t = arcIndex α n t') {j : ℕ} (hj : j ≤ n) :
    cut α j ≤ t ↔ cut α j ≤ t' := by
  wlog htt : t ≤ t' generalizing t t'
  · exact (this h.symm (le_of_not_ge htt)).symm
  have hsub : (range (n + 1)).filter (fun j => cut α j ≤ t) ⊆
      (range (n + 1)).filter (fun j => cut α j ≤ t') := by
    intro k hk
    rw [mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.trans htt⟩
  have heq := eq_of_subset_of_card_le hsub (le_of_eq h.symm)
  have hmem : j ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le hj)
  constructor
  · intro hc
    exact hc.trans htt
  · intro hc
    have h2 : j ∈ (range (n + 1)).filter (fun j => cut α j ≤ t') := mem_filter.mpr ⟨hmem, hc⟩
    rw [← heq] at h2
    exact (mem_filter.mp h2).2

/-- [proved-derived; formal-checked] **Two readings in one arc carry the same next `n` letters.** -/
theorem carry_eq_of_arcIndex_eq {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) {n : ℕ} {k k' : ℤ}
    (h : arcIndex α n (Int.fract ((k : ℝ) * α + ρ)) =
      arcIndex α n (Int.fract ((k' : ℝ) * α + ρ)))
    {i : ℕ} (hi : i < n) : carry α ρ (k + i) = carry α ρ (k' + i) := by
  have key : ∀ m : ℤ, (carry α ρ (m + i) = 1 ↔
      if cut α (i + 1) ≤ cut α i then
        (cut α (i + 1) ≤ Int.fract ((m : ℝ) * α + ρ) ∧ ¬ cut α i ≤ Int.fract ((m : ℝ) * α + ρ))
      else (cut α (i + 1) ≤ Int.fract ((m : ℝ) * α + ρ) ∨
        ¬ cut α i ≤ Int.fract ((m : ℝ) * α + ρ))) := by
    intro m
    have e : (((m + (i : ℤ) : ℤ)) : ℝ) * α + ρ = ((m : ℝ) * α + ρ) + (i : ℝ) * α := by
      push_cast
      ring
    rw [carry_eq_one_iff h0 h1, e]
    exact letter_iff h0 h1 _ i
  have e1 := cut_le_iff_of_arcIndex_eq h (j := i) (by omega)
  have e2 := cut_le_iff_of_arcIndex_eq h (j := i + 1) (by omega)
  have hiff : carry α ρ (k + i) = 1 ↔ carry α ρ (k' + i) = 1 := by
    rw [key k, key k', e1, e2]
  rcases carry_mem_zero_one h0 h1 ρ (k + i) with a | a <;>
    rcases carry_mem_zero_one h0 h1 ρ (k' + i) with b | b
  · rw [a, b]
  · exfalso
    have := hiff.mpr b
    omega
  · exfalso
    have := hiff.mp a
    omega
  · rw [a, b]

/-! ## 3. A word whose factor count does not grow is eventually periodic -/

section MorseHedlund

variable {A : Type*}

/-- [definition] **The factor of length `n` at the tick `k`** of a word `s : ℤ → A`. -/
def factorAt (s : ℤ → A) (n : ℕ) (k : ℤ) : Fin n → A := fun i => s (k + (i : ℕ))

/-- [definition] **The factors of length `n`** of a word. -/
def wordFactors (s : ℤ → A) (n : ℕ) : Set (Fin n → A) := Set.range (factorAt s n)

/-- [proved-derived; formal-checked] **One next letter.** Where the factors of length `n + 1` are
no more than those of length `n`, two ticks with one factor of length `n` carry the same letter
after it: dropping the last letter is onto, so it is injective on a finite set no larger. -/
theorem next_eq_of_ncard_le {s : ℤ → A} {n : ℕ} (hfin : (wordFactors s (n + 1)).Finite)
    (hle : (wordFactors s (n + 1)).ncard ≤ (wordFactors s n).ncard) {k k' : ℤ}
    (h : factorAt s n k = factorAt s n k') : s (k + n) = s (k' + n) := by
  let r : (Fin (n + 1) → A) → (Fin n → A) := fun w i => w (Fin.castSucc i)
  have hr : ∀ k, r (factorAt s (n + 1) k) = factorAt s n k := by
    intro k
    funext i
    simp [r, factorAt]
  have himg : r '' wordFactors s (n + 1) = wordFactors s n := by
    ext w
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (hr k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, hr k⟩
  have hcard : (r '' wordFactors s (n + 1)).ncard = (wordFactors s (n + 1)).ncard := by
    refine le_antisymm (Set.ncard_image_le hfin) ?_
    rw [himg]
    exact hle
  have hinj := Set.injOn_of_ncard_image_eq hcard hfin
  have heq : factorAt s (n + 1) k = factorAt s (n + 1) k' :=
    hinj ⟨k, rfl⟩ ⟨k', rfl⟩ (by rw [hr, hr]; exact h)
  have h2 := congr_fun heq (Fin.last n)
  simpa [factorAt] using h2

/-- [proved-derived; formal-checked] With one next letter, the factor one tick later is decided. -/
theorem factorAt_succ_eq {s : ℤ → A} {n : ℕ}
    (hnext : ∀ k k' : ℤ, factorAt s n k = factorAt s n k' → s (k + n) = s (k' + n))
    {k k' : ℤ} (h : factorAt s n k = factorAt s n k') :
    factorAt s n (k + 1) = factorAt s n (k' + 1) := by
  funext i
  simp only [factorAt]
  by_cases hi : (i : ℕ) + 1 < n
  · have h2 := congr_fun h ⟨(i : ℕ) + 1, hi⟩
    simp only [factorAt] at h2
    have e : ∀ m : ℤ, m + 1 + ((i : ℕ) : ℤ) = m + (((i : ℕ) + 1 : ℕ) : ℤ) := by
      intro m
      push_cast
      ring
    rw [e, e]
    exact h2
  · have hin : (i : ℕ) + 1 = n := by
      have := i.isLt
      omega
    have h2 := hnext k k' h
    have e : ∀ m : ℤ, m + 1 + ((i : ℕ) : ℤ) = m + (n : ℤ) := by
      intro m
      omega
    rw [e, e]
    exact h2

/-- [proved-derived; formal-checked] With one next letter, two ticks with one factor keep one
factor at every later tick. -/
theorem factorAt_add_eq {s : ℤ → A} {n : ℕ}
    (hnext : ∀ k k' : ℤ, factorAt s n k = factorAt s n k' → s (k + n) = s (k' + n))
    {k k' : ℤ} (h : factorAt s n k = factorAt s n k') (j : ℕ) :
    factorAt s n (k + j) = factorAt s n (k' + j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have h2 := factorAt_succ_eq hnext ih
    have e : ∀ m : ℤ, m + ((j + 1 : ℕ) : ℤ) = m + (j : ℤ) + 1 := by
      intro m
      push_cast
      ring
    rw [e, e]
    exact h2

/-- [proved-derived; formal-checked] **Morse–Hedlund's step.** A word whose factors of length
`n + 1` are no more than its factors of length `n` is periodic from some tick on. -/
theorem eventually_periodic_of_ncard_le {s : ℤ → A} {n : ℕ}
    (hfin : (wordFactors s (n + 1)).Finite) (hfin' : (wordFactors s n).Finite)
    (hle : (wordFactors s (n + 1)).ncard ≤ (wordFactors s n).ncard) :
    ∃ T : ℕ, 0 < T ∧ ∃ N : ℤ, ∀ m ≥ N, s (m + T) = s m := by
  have hnext : ∀ k k' : ℤ, factorAt s n k = factorAt s n k' → s (k + n) = s (k' + n) :=
    fun k k' h => next_eq_of_ncard_le hfin hle h
  have hninj : ¬ Function.Injective (factorAt s n) := fun hinj =>
    (Set.infinite_of_injective_forall_mem hinj
      (fun k => (⟨k, rfl⟩ : factorAt s n k ∈ wordFactors s n))) hfin'
  obtain ⟨k, k', hkk, hne⟩ := Function.not_injective_iff.mp hninj
  have main : ∀ k k' : ℤ, k < k' → factorAt s n k = factorAt s n k' →
      ∃ T : ℕ, 0 < T ∧ ∃ N : ℤ, ∀ m ≥ N, s (m + T) = s m := by
    intro k k' hlt h
    refine ⟨(k' - k).toNat, by omega, k + n, ?_⟩
    intro m hm
    have h2 := hnext _ _ (factorAt_add_eq hnext h (m - (k + n)).toNat)
    have e1 : k' + ((m - (k + n)).toNat : ℤ) + n = m + ((k' - k).toNat : ℤ) := by omega
    have e2 : k + ((m - (k + n)).toNat : ℤ) + n = m := by omega
    rw [e1, e2] at h2
    exact h2.symm
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact main k k' hlt hkk
  · exact main k' k hlt hkk.symm

end MorseHedlund

/-! ## 4. At most `n + 1` factors, and `n + 1` at an irrational rate -/

/-- [definition] **The factors of length `n`** of the carry word of rate `α` from phase `ρ`. -/
def factors (α ρ : ℝ) (n : ℕ) : Set (Fin n → ℤ) := wordFactors (carry α ρ) n

/-- [proved-derived; formal-checked] **The carry word has at most `n + 1` factors of length `n`**,
for every rate below one turn per tick and every phase: a factor is read from the arc its first
reading stands in, and the `n + 1` cuts leave at most `n + 1` arcs. -/
theorem ncard_factors_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) (n : ℕ) :
    (factors α ρ n).Finite ∧ (factors α ρ n).ncard ≤ n + 1 := by
  classical
  let φ : ℤ → ℕ := fun k => arcIndex α n (Int.fract ((k : ℝ) * α + ρ))
  let W : ℤ → (Fin n → ℤ) := factorAt (carry α ρ) n
  let g : ℕ → (Fin n → ℤ) := fun c => if h : ∃ k, φ k = c then W h.choose else 0
  have hW : ∀ k, W k = g (φ k) := by
    intro k
    have hex : ∃ k', φ k' = φ k := ⟨k, rfl⟩
    simp only [g, dif_pos hex]
    funext i
    exact carry_eq_of_arcIndex_eq h0 h1 ρ (hex.choose_spec).symm i.isLt
  have hsub : factors α ρ n ⊆ g '' ((Finset.Icc 1 (n + 1) : Finset ℕ) : Set ℕ) := by
    rintro w ⟨k, rfl⟩
    refine ⟨φ k, ?_, (hW k).symm⟩
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨arcIndex_pos α n (Int.fract_nonneg _), arcIndex_le α n _⟩
  have hfin : (g '' ((Finset.Icc 1 (n + 1) : Finset ℕ) : Set ℕ)).Finite :=
    (Finset.finite_toSet _).image g
  refine ⟨hfin.subset hsub, ?_⟩
  calc (factors α ρ n).ncard
      ≤ (g '' ((Finset.Icc 1 (n + 1) : Finset ℕ) : Set ℕ)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (((Finset.Icc 1 (n + 1) : Finset ℕ) : Set ℕ)).ncard :=
        Set.ncard_image_le (Finset.finite_toSet _)
    _ = n + 1 := by
        rw [Set.ncard_coe_finset]
        simp

/-- [proved-derived; formal-checked] **Sturmian factor complexity.** The carry word of an
irrational rate has `n + 1` factors of length `n`, for every `n` and every phase: it never locks,
so its factor count grows with each letter (Morse–Hedlund's step), and the arcs bound it above. -/
theorem ncard_factors_eq {α : ℝ} (hα : Irrational α) (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) (n : ℕ) :
    (factors α ρ n).ncard = n + 1 := by
  refine le_antisymm (ncard_factors_le h0 h1 ρ n).2 ?_
  induction n with
  | zero =>
    have hne : (factors α ρ 0).Nonempty := Set.range_nonempty _
    have hpos := (Set.ncard_pos (ncard_factors_le h0 h1 ρ 0).1).mpr hne
    omega
  | succ n ih =>
    by_contra hlt
    rw [not_le] at hlt
    have hle : (factors α ρ (n + 1)).ncard ≤ (factors α ρ n).ncard := by omega
    obtain ⟨T, hT, N, hper⟩ := eventually_periodic_of_ncard_le (s := carry α ρ)
      (ncard_factors_le h0 h1 ρ (n + 1)).1 (ncard_factors_le h0 h1 ρ n).1 hle
    exact not_eventually_periodic_of_irrational hα ρ hT N hper

end Holonics.Aeon.Clock.SturmianComplexity
