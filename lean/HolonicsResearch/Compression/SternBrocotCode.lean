import Mathlib
import HolonicsResearch.Geometry.Farey

/-!
# A Stern–Brocot path is a word, and a length coded first makes it a prefix code

[proved-standard] The source is the learner record of September 27
(`research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md`,
"Mode locking weights simple keys more heavily"): the tongues are ordered by Farey mediants, every rational has a
unique finite path in the Stern–Brocot tree, the raw path is not self-delimiting (`L` is a prefix of `LL`), and it
becomes a prefix code only with its length coded first.

A word is a list of letters, `false` for `L` and `true` for `R`. A letter moves a pair of naturals, `L (a, b) =
(a, a + b)` and `R (a, b) = (a + b, b)`, which are the matrices `!![1,0;1,1]` and `!![1,1;0,1]` of determinant one,
and a word's node is its letters applied to `(1, 1)`, the first letter outermost (the first step from the root).

What is proved.

1. **Every node is in lowest terms.** The letters' matrices are the generators `sbL`, `sbR` of `Geometry/Farey`
   (`letter_eq_generators`); a word's matrix has determinant one (`det_wordMatrix`) and carries `(1, 1)` to the node
   (`wordMatrix_mulVec`); the node's parts are positive and coprime (`node_pos`, `node_coprime`).
2. **Words and positive rationals are one set.** Subtracting the smaller part from the larger reads the word back
   from the pair (`path`, `path_node`), and every coprime positive pair is the node of its path (`node_path`). So the
   value `a/b` of a word has numerator and denominator its node (`num_value`, `den_value`), distinct words have
   distinct values (`value_injective`), every positive rational is the value of its path (`value_pathOf`,
   `pathOf_value`), and the map from words to positive rationals is a bijection (`value_bijective`).
3. **A run is a quotient of Euclid's division.** `k` letters `R` before a word add `k` times the denominator to the
   numerator, and `k` letters `L` add `k` times the numerator to the denominator (`node_replicate_true`,
   `node_replicate_false`); a word of `n` letters has parts summing to at least `n + 2` (`length_add_two_le`).
4. **The raw paths are not a prefix code.** Every word is a path, and `L`, the path of `1/2`, is a prefix of `LL`,
   the path of `1/3` (`ruler_not_self_delimiting`).
5. **A length coded first makes one.** For any prefix-free code `len` of the naturals, `w ↦ len |w| ++ w` is
   prefix-free on words (`code_prefixFree`) and so on positive rationals (`rational_code_prefixFree`); its length is
   `|len |w|| + |w|` (`code_length`). The unary code `Rⁿ L` is prefix-free (`unary_prefixFree`), and with it a word of
   `n` letters costs `2n + 1` (`unary_code_length`).
6. **Kraft's inequality.** A prefix-free set of nonempty words is uniquely decodable
   (`uniquelyDecodable_of_prefixFree`), so by Mathlib's Kraft–McMillan theorem every finite set of words has
   `Σ 2^(−|len |w|| − |w|) ≤ 1` (`kraft_code`), and `Σ 2^(−(2|w| + 1)) ≤ 1` with the unary length (`kraft_unary`).
   Over all words of fewer than `N` letters, `2ⁿ` of each length `n` (`card_wordsOfLength`), the unary sum is
   `1 − 2^(−N)` (`unary_sum_below`, `unary_sum_words`): the code's sum tends to one, no share being left unused.

Limits. The tree's order (a word's value lies between its ancestors' mediants) and the mediant rule itself are not
stated; the bijection is through Euclid's subtraction. That a path's length is the sum of the continued fraction's
partial quotients less one is stated only through the runs of statement 3 and is not joined to Mathlib's continued
fractions. The record's other cited result in the same #410 box, the standard family's tongue contact order `q`, is
analysis of the sine circle map and is not here. Kraft's inequality is taken from Mathlib
(`InformationTheory.kraft_mcmillan_inequality`).

The computational object is the helical pair interaction: a rational is a pair's undivided ratio, and its path is the
word of shears that Euclid's division writes for it. Of the winding guide's six general objects this touches the pair
(the ratio and its two shears) and faces and placement (a code length is the face a receiver reads); the helix, cell
holonomy, tube and tower thread stay attached.

Consumers: #410's box "Classical results cited in the learner record: the Stern–Brocot path with a length prefix as a
prefix code"; the record's simplicity weighting of locked ratios, which needs a code that is a prefix code before a
length is read as a prior.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.SternBrocotCode

open Matrix

/-! ## 1. Words, nodes and lowest terms -/

/-- [definition] A letter's move on a pair: `L = false` sends `(a, b)` to `(a, a + b)`, `R = true` to
`(a + b, b)`. -/
def step (l : Bool) (x : ℕ × ℕ) : ℕ × ℕ := if l then (x.1 + x.2, x.2) else (x.1, x.1 + x.2)

/-- [definition] The node of a word: its letters applied to `(1, 1)`, the first letter outermost. -/
def node : List Bool → ℕ × ℕ
  | [] => (1, 1)
  | l :: w => step l (node w)

/-- [proved-standard] Both parts of a node are positive. -/
theorem node_pos (w : List Bool) : 0 < (node w).1 ∧ 0 < (node w).2 := by
  induction w with
  | nil => simp [node]
  | cons l w ih =>
    cases l <;> simp only [node, step] <;> constructor <;> simp <;> omega

/-- [proved-standard] **Every node is in lowest terms.** -/
theorem node_coprime (w : List Bool) : Nat.Coprime (node w).1 (node w).2 := by
  induction w with
  | nil => simp [node]
  | cons l w ih =>
    cases l
    · simpa [node, step, Nat.coprime_self_add_right] using ih
    · simpa [node, step, Nat.coprime_add_self_left] using ih

/-- [definition] A letter's matrix: `R = !![1,1;0,1]`, `L = !![1,0;1,1]`. -/
def letter (l : Bool) : Matrix (Fin 2) (Fin 2) ℤ := if l then !![1, 1; 0, 1] else !![1, 0; 1, 1]

/-- [proved-standard] The letters' matrices are the Stern–Brocot generators of `Geometry/Farey`. -/
theorem letter_eq_generators :
    letter false = Holonics.Geometry.Farey.sbL ∧ letter true = Holonics.Geometry.Farey.sbR :=
  ⟨rfl, rfl⟩

/-- [definition] A word's matrix, the product of its letters' in order. -/
def wordMatrix : List Bool → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | l :: w => letter l * wordMatrix w

/-- [proved-standard] A word's matrix has determinant one. -/
theorem det_wordMatrix (w : List Bool) : (wordMatrix w).det = 1 := by
  induction w with
  | nil => simp [wordMatrix]
  | cons l w ih =>
    rw [wordMatrix, Matrix.det_mul, ih]
    cases l <;> simp [letter, Matrix.det_fin_two]

/-- [proved-standard] A word's matrix carries `(1, 1)` to its node. -/
theorem wordMatrix_mulVec (w : List Bool) :
    wordMatrix w *ᵥ ![1, 1] = ![((node w).1 : ℤ), ((node w).2 : ℤ)] := by
  induction w with
  | nil => simp [wordMatrix, node]
  | cons l w ih =>
    rw [wordMatrix, ← Matrix.mulVec_mulVec, ih]
    cases l <;> ext i <;> fin_cases i <;> simp [letter, node, step, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ## 2. Words and positive rationals are one set -/

/-- [definition] Euclid's subtraction with a count of steps allowed: the word read back from a pair. -/
def pathAux : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | fuel + 1, a, b =>
    if a < b then false :: pathAux fuel a (b - a)
    else if b < a then true :: pathAux fuel (a - b) b
    else []

/-- [definition] The path of a pair. -/
def path (a b : ℕ) : List Bool := pathAux (a + b) a b

/-- [proved-standard] With steps enough, the subtraction reads a word back from its node. -/
theorem pathAux_node (w : List Bool) (fuel : ℕ) (h : (node w).1 + (node w).2 ≤ fuel) :
    pathAux fuel (node w).1 (node w).2 = w := by
  induction w generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp [node] at h
    | succ f => simp [pathAux, node]
  | cons l w ih =>
    obtain ⟨ha, hb⟩ := node_pos w
    cases fuel with
    | zero =>
      exfalso
      cases l <;> simp only [node, step] at h <;> simp at h <;> omega
    | succ f =>
      cases l
      · simp only [node, step, Bool.false_eq_true, if_false] at h ⊢
        have h1 : (node w).1 < (node w).1 + (node w).2 := by omega
        rw [pathAux, if_pos h1, Nat.add_sub_cancel_left, ih f (by omega)]
      · simp only [node, step, if_true] at h ⊢
        have h1 : ¬ (node w).1 + (node w).2 < (node w).2 := by omega
        have h2 : (node w).2 < (node w).1 + (node w).2 := by omega
        rw [pathAux, if_neg h1, if_pos h2, Nat.add_sub_cancel, ih f (by omega)]

/-- [proved-standard] **The path of a node is its word.** -/
theorem path_node (w : List Bool) : path (node w).1 (node w).2 = w :=
  pathAux_node w _ le_rfl

/-- [proved-standard] Distinct words have distinct nodes. -/
theorem node_injective : Function.Injective node := by
  intro w w' h
  rw [← path_node w, ← path_node w', h]

/-- [proved-standard] With steps enough, the word of a coprime positive pair has that pair as its node. -/
theorem node_pathAux (fuel a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) (h : a + b ≤ fuel) :
    node (pathAux fuel a b) = (a, b) := by
  induction fuel generalizing a b with
  | zero => omega
  | succ f ih =>
    rw [pathAux]
    by_cases h1 : a < b
    · rw [if_pos h1, node, ih a (b - a) ha (by omega) ((Nat.coprime_sub_self_right h1.le).mpr hcop) (by omega)]
      simp only [step, Bool.false_eq_true, if_false]
      congr 1
      omega
    · rw [if_neg h1]
      by_cases h2 : b < a
      · rw [if_pos h2, node, ih (a - b) b (by omega) hb ((Nat.coprime_sub_self_left h2.le).mpr hcop) (by omega)]
        simp only [step, if_true]
        congr 1
        omega
      · rw [if_neg h2]
        have hab : a = b := by omega
        subst hab
        have h1 : a = 1 := (Nat.coprime_self a).mp hcop
        subst h1
        rfl

/-- [proved-standard] **Every coprime positive pair is the node of its path.** -/
theorem node_path (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) : node (path a b) = (a, b) :=
  node_pathAux _ a b ha hb hcop le_rfl

/-- [definition] The value of a word: its node read as a ratio. -/
def value (w : List Bool) : ℚ := ((node w).1 : ℚ) / ((node w).2 : ℚ)

/-- [proved-standard] A word's value is positive. -/
theorem value_pos (w : List Bool) : 0 < value w := by
  obtain ⟨ha, hb⟩ := node_pos w
  unfold value
  positivity

private theorem value_eq_int (w : List Bool) :
    value w = (((node w).1 : ℤ) : ℚ) / (((node w).2 : ℤ) : ℚ) := by
  simp [value]

/-- [proved-standard] The numerator of a word's value is its node's first part. -/
theorem num_value (w : List Bool) : (value w).num = (node w).1 := by
  rw [value_eq_int]
  exact Rat.num_div_eq_of_coprime (by exact_mod_cast (node_pos w).2) (by simpa using node_coprime w)

/-- [proved-standard] The denominator of a word's value is its node's second part. -/
theorem den_value (w : List Bool) : (value w).den = (node w).2 := by
  have h : (((value w).den : ℕ) : ℤ) = ((node w).2 : ℤ) := by
    rw [value_eq_int]
    exact Rat.den_div_eq_of_coprime (by exact_mod_cast (node_pos w).2) (by simpa using node_coprime w)
  exact_mod_cast h

/-- [proved-standard] **Distinct words have distinct values.** -/
theorem value_injective : Function.Injective value := by
  intro w w' h
  apply node_injective
  have h1 : (((node w).1 : ℕ) : ℤ) = ((node w').1 : ℤ) := by rw [← num_value, ← num_value, h]
  have h2 : (node w).2 = (node w').2 := by rw [← den_value, ← den_value, h]
  exact Prod.ext (by exact_mod_cast h1) h2

/-- [definition] The path of a rational: Euclid's subtraction on its numerator and denominator. -/
def pathOf (q : ℚ) : List Bool := path q.num.natAbs q.den

/-- [proved-standard] **Every positive rational is the value of its path.** -/
theorem value_pathOf {q : ℚ} (hq : 0 < q) : value (pathOf q) = q := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hn : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnum.ne'
  unfold value pathOf
  rw [node_path _ _ hn q.den_pos q.reduced]
  have h : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_pos hnum]
  simp only [h]
  exact Rat.num_div_den q

/-- [proved-standard] The path of a word's value is the word. -/
theorem pathOf_value (w : List Bool) : pathOf (value w) = w :=
  value_injective (value_pathOf (value_pos w))

/-- [proved-standard] **Words and positive rationals are one set**: the value is a bijection. -/
theorem value_bijective :
    Function.Bijective (fun w : List Bool => (⟨value w, value_pos w⟩ : {q : ℚ // 0 < q})) := by
  constructor
  · intro w w' h
    exact value_injective (congrArg Subtype.val h)
  · rintro ⟨q, hq⟩
    exact ⟨pathOf q, Subtype.ext (value_pathOf hq)⟩

/-! ## 3. Runs are Euclid's quotients -/

/-- [proved-standard] `k` letters `R` before a word add `k` times the denominator to the numerator. -/
theorem node_replicate_true (k : ℕ) (w : List Bool) :
    node (List.replicate k true ++ w) = ((node w).1 + k * (node w).2, (node w).2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, node, ih]
    simp only [step, if_true]
    congr 1
    ring

/-- [proved-standard] `k` letters `L` before a word add `k` times the numerator to the denominator. -/
theorem node_replicate_false (k : ℕ) (w : List Bool) :
    node (List.replicate k false ++ w) = ((node w).1, (node w).2 + k * (node w).1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, node, ih]
    simp only [step, Bool.false_eq_true, if_false]
    congr 1
    ring

/-- [proved-standard] A word of `n` letters has a node whose parts sum to at least `n + 2`. -/
theorem length_add_two_le (w : List Bool) : w.length + 2 ≤ (node w).1 + (node w).2 := by
  induction w with
  | nil => simp [node]
  | cons l w ih =>
    obtain ⟨ha, hb⟩ := node_pos w
    cases l <;> simp only [node, step, List.length_cons] <;> simp <;> omega

/-! ## 4. The raw paths are not a prefix code -/

/-- [counterexample] **The raw path is not self-delimiting**: `L` is the path of `1/2`, `LL` the path of `1/3`, and
the first is a prefix of the second. -/
theorem ruler_not_self_delimiting :
    value [false] = 1 / 2 ∧ value [false, false] = 1 / 3 ∧ [false] <+: [false, false] ∧
      [false] ≠ [false, false] := by
  refine ⟨by norm_num [value, node, step], by norm_num [value, node, step], by simp, by simp⟩

/-- [proved-standard] Rulers: the root, its two children and three nodes below them. -/
theorem ruler_values :
    value [] = 1 ∧ value [true] = 2 ∧ value [false, true] = 2 / 3 ∧ value [true, false] = 3 / 2 ∧
      value [false, false, true] = 2 / 5 := by
  refine ⟨by norm_num [value, node, step], by norm_num [value, node, step], by norm_num [value, node, step],
    by norm_num [value, node, step], by norm_num [value, node, step]⟩

/-! ## 5. A length coded first makes a prefix code -/

/-- [definition] A code is prefix-free: no codeword is a prefix of another's. -/
def PrefixFree {ι : Type*} (c : ι → List Bool) : Prop := ∀ i j, c i <+: c j → i = j

/-- [definition] A word with its length coded first by `len`. -/
def code (len : ℕ → List Bool) (w : List Bool) : List Bool := len w.length ++ w

/-- [definition] The unary code of a natural number: `n` letters `R`, then `L`. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- [proved-standard] The unary code is prefix-free. -/
theorem unary_prefixFree : PrefixFree unary := by
  intro m
  induction m with
  | zero =>
    intro n h
    cases n with
    | zero => rfl
    | succ n => simp [unary, List.replicate_succ] at h
  | succ m ih =>
    intro n h
    cases n with
    | zero => simp [unary, List.replicate_succ] at h
    | succ n =>
      have h' : unary m <+: unary n := by
        simpa [unary, List.replicate_succ] using h
      rw [ih n h']

/-- [proved-standard] The length of a coded word: `|len |w|| + |w|`. -/
theorem code_length (len : ℕ → List Bool) (w : List Bool) :
    (code len w).length = (len w.length).length + w.length := by
  simp [code]

/-- [proved-standard] With the unary length a word of `n` letters costs `2n + 1`. -/
theorem unary_code_length (w : List Bool) : (code unary w).length = 2 * w.length + 1 := by
  simp [code, unary]
  omega

/-- [proved-standard] **A length coded first makes the paths a prefix code**: for a prefix-free `len`, no coded
word is a prefix of another. -/
theorem code_prefixFree {len : ℕ → List Bool} (hlen : PrefixFree len) : PrefixFree (code len) := by
  intro w w' h
  have h1 : len w.length <+: len w'.length ++ w' := (List.prefix_append _ _).trans h
  have h2 : len w'.length <+: len w'.length ++ w' := List.prefix_append _ _
  have hl : w.length = w'.length := by
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h3 | h3
    · exact hlen _ _ h3
    · exact (hlen _ _ h3).symm
  unfold code at h
  rw [hl, List.prefix_append_right_inj] at h
  exact h.eq_of_length hl

/-- [proved-standard] The same on positive rationals: no rational's coded path is a prefix of another's. -/
theorem rational_code_prefixFree {len : ℕ → List Bool} (hlen : PrefixFree len) {x y : ℚ} (hx : 0 < x)
    (hy : 0 < y) (h : code len (pathOf x) <+: code len (pathOf y)) : x = y := by
  have hw := code_prefixFree hlen _ _ h
  rw [← value_pathOf hx, ← value_pathOf hy, hw]

/-! ## 6. Kraft's inequality -/

/-- [proved-standard] A prefix-free set of nonempty words is uniquely decodable. -/
theorem uniquelyDecodable_of_prefixFree {S : Set (List Bool)}
    (hS : ∀ u ∈ S, ∀ v ∈ S, u <+: v → u = v) (hne : [] ∉ S) : InformationTheory.UniquelyDecodable S := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ _ h₂ hflat
    cases L₂ with
    | nil => rfl
    | cons v L₂ =>
      exfalso
      have hv : v ∈ S := h₂ v List.mem_cons_self
      have hv0 : v = [] := by
        have h := hflat.symm
        rw [List.flatten_cons, List.flatten_nil, List.append_eq_nil_iff] at h
        exact h.1
      exact hne (hv0 ▸ hv)
  | cons u L₁ ih =>
    intro L₂ h₁ h₂ hflat
    have hu : u ∈ S := h₁ u List.mem_cons_self
    cases L₂ with
    | nil =>
      exfalso
      have hu0 : u = [] := by
        rw [List.flatten_cons, List.flatten_nil, List.append_eq_nil_iff] at hflat
        exact hflat.1
      exact hne (hu0 ▸ hu)
    | cons v L₂ =>
      have hv : v ∈ S := h₂ v List.mem_cons_self
      rw [List.flatten_cons, List.flatten_cons] at hflat
      have huv : u = v := by
        have p1 : u <+: v ++ L₂.flatten := hflat ▸ List.prefix_append u L₁.flatten
        have p2 : v <+: v ++ L₂.flatten := List.prefix_append v L₂.flatten
        rcases List.prefix_or_prefix_of_prefix p1 p2 with h | h
        · exact hS u hu v hv h
        · exact (hS v hv u hu h).symm
      subst huv
      have htail := List.append_cancel_left hflat
      rw [ih L₂ (fun w hw => h₁ w (List.mem_cons_of_mem _ hw)) (fun w hw => h₂ w (List.mem_cons_of_mem _ hw))
        htail]

/-- [proved-standard] A prefix-free code of the naturals has no empty codeword. -/
theorem len_ne_nil {len : ℕ → List Bool} (hlen : PrefixFree len) (n : ℕ) : len n ≠ [] := by
  intro h
  have h1 : len n <+: len (n + 1) := by
    rw [h]
    exact List.nil_prefix
  have := hlen _ _ h1
  omega

/-- [proved-standard] **Kraft's inequality for the coded paths**: over every finite set of words,
`Σ 2^(−|len |w|| − |w|) ≤ 1`. -/
theorem kraft_code {len : ℕ → List Bool} (hlen : PrefixFree len) (S : Finset (List Bool)) :
    ∑ w ∈ S, (1 / 2 : ℝ) ^ (code len w).length ≤ 1 := by
  classical
  have hinj : Function.Injective (code len) := fun w w' h => code_prefixFree hlen w w' (h ▸ List.prefix_rfl)
  have hud : InformationTheory.UniquelyDecodable ((S.image (code len) : Finset (List Bool)) : Set (List Bool)) := by
    apply uniquelyDecodable_of_prefixFree
    · intro u hu v hv huv
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
      obtain ⟨w, -, rfl⟩ := hu
      obtain ⟨w', -, rfl⟩ := hv
      rw [code_prefixFree hlen w w' huv]
    · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, not_exists, not_and]
      intro w _ h
      unfold code at h
      rw [List.append_eq_nil_iff] at h
      exact len_ne_nil hlen _ h.1
  have h := InformationTheory.kraft_mcmillan_inequality hud
  rw [Finset.sum_image (fun w _ w' _ h => hinj h)] at h
  simpa using h

/-- [proved-standard] With the unary length: `Σ 2^(−(2|w| + 1)) ≤ 1` over every finite set of words. -/
theorem kraft_unary (S : Finset (List Bool)) : ∑ w ∈ S, (1 / 2 : ℝ) ^ (2 * w.length + 1) ≤ 1 := by
  have h := kraft_code unary_prefixFree S
  simpa only [unary_code_length] using h

/-- [proved-standard] **The unary-length code leaves nothing unused in the limit**: the words of fewer than `N`
letters, `2ⁿ` of each length `n`, carry `Σ_(n < N) 2ⁿ · 2^(−(2n + 1)) = 1 − 2^(−N)`. -/
theorem unary_sum_below (N : ℕ) :
    ∑ n ∈ Finset.range N, (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ (2 * n + 1) = 1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h : (2 : ℝ) ^ N * (1 / 2 : ℝ) ^ (2 * N + 1) = (1 / 2 : ℝ) ^ (N + 1) := by
      rw [pow_succ, pow_mul, pow_succ]
      have h2 : (2 : ℝ) ^ N * ((1 / 2 : ℝ) ^ 2) ^ N = (1 / 2 : ℝ) ^ N := by
        rw [← mul_pow]
        norm_num
      linear_combination (1 / 2 : ℝ) * h2
    rw [h, pow_succ]
    ring

/-- [definition] The words of `n` letters. -/
def wordsOfLength (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (List.Vector Bool n)).image List.Vector.toList

/-- [proved-standard] A word is among the words of `n` letters when and only when its length is `n`. -/
theorem mem_wordsOfLength {n : ℕ} {w : List Bool} : w ∈ wordsOfLength n ↔ w.length = n := by
  unfold wordsOfLength
  constructor
  · intro h
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp h
    exact v.toList_length
  · intro h
    exact Finset.mem_image.mpr ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩

/-- [proved-standard] There are `2ⁿ` words of `n` letters. -/
theorem card_wordsOfLength (n : ℕ) : (wordsOfLength n).card = 2 ^ n := by
  rw [wordsOfLength, Finset.card_image_of_injective _ List.Vector.toList_injective, Finset.card_univ, card_vector,
    Fintype.card_bool]

/-- [proved-standard] **The coded words of fewer than `N` letters carry `1 − 2^(−N)`** under the unary length, so
the code's Kraft sum tends to one. -/
theorem unary_sum_words (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ w ∈ wordsOfLength n, (1 / 2 : ℝ) ^ (code unary w).length = 1 - (1 / 2 : ℝ) ^ N := by
  rw [← unary_sum_below N]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h : ∀ w ∈ wordsOfLength n, (1 / 2 : ℝ) ^ (code unary w).length = (1 / 2 : ℝ) ^ (2 * n + 1) := by
    intro w hw
    rw [unary_code_length, mem_wordsOfLength.mp hw]
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_wordsOfLength, nsmul_eq_mul]
  push_cast
  rfl

end Holonics.Compression.SternBrocotCode
