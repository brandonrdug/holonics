import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exact addressed fractal packing

The existing sphere-packing files prove curvature-reflection orbits but deliberately stop before a
geometric residual fractal.  This file supplies the smallest exact geometric owner: a rational
two-branch packing whose cells are genuine intervals, whose children are separated by a positive
gap, whose scale is exact at every word depth, and whose ordered address is retained.

It is the one-dimensional Cantor carrier because every quantity is rational and no limiting,
floating-point, statistical, or dimension estimate is required.  The reusable law is not the
number `3`; it is the simultaneous recurrence of restriction, rebase, separation, and lineage.
Sphere, polyhedral, crystal, and lightning realizations must provide their own child maps and
separation laws before consuming that pattern.

The second part integrates over the packing by conjugate reflection.  The cells are the images of
the unit cell under the Cantor maps `S₀ x = x/3`, `S₁ x = (x+2)/3` (`descend_root_eq_wordMap`),
and the half-turn `J x = 1 − x` conjugates them, `S₁ = J S₀ J`.  The depth-`n` word partition is
a receiver's grain; the word average `A_n(f, x₀) = 2^(−n) Σ_(|w|=n) f(S_w x₀)` is its reading and
`K·3^(−n)` is the residual it leaves for a `K`-Lipschitz `f`.  Every finite law there is exact in
any linearly ordered field, hence over `ℚ`; only the limit, the integral against the equal-weight
self-similar measure, is taken in `ℝ`.
-/

namespace Holonics.Foundation.FractalPacking

/-- The two oriented child choices at one restriction event. -/
inductive Hand
  | left
  | right
deriving DecidableEq, Repr

/-- A situated rational one-cell.  Order is carried as a predicate because degenerate and reversed
cells are useful exact counterexamples rather than forbidden encodings. -/
structure Cell where
  lower : ℚ
  upper : ℚ
deriving DecidableEq, Repr

/-- The oriented cell length. -/
def Cell.width (cell : Cell) : ℚ := cell.upper - cell.lower

/-- A cell has a genuine interior exactly when its oriented width is positive. -/
def Cell.Positive (cell : Cell) : Prop := 0 < cell.width

/-- Exact containment of one closed cell in another. -/
def Cell.Contains (outer inner : Cell) : Prop :=
  outer.lower ≤ inner.lower ∧ inner.upper ≤ outer.upper

/-- The left third of one cell. -/
def leftChild (cell : Cell) : Cell :=
  ⟨cell.lower, cell.lower + cell.width / 3⟩

/-- The right third of one cell. -/
def rightChild (cell : Cell) : Cell :=
  ⟨cell.lower + 2 * cell.width / 3, cell.upper⟩

/-- Apply one polarized restriction. -/
def child : Hand → Cell → Cell
  | .left, cell => leftChild cell
  | .right, cell => rightChild cell

/-- Both child orientations have exactly one third of the parent width. -/
theorem child_width (hand : Hand) (cell : Cell) :
    (child hand cell).width = cell.width / 3 := by
  cases hand <;> simp [child, leftChild, rightChild, Cell.width] <;> ring

/-- Positive width is preserved by each exact restriction. -/
theorem child_positive (hand : Hand) {cell : Cell} (positive : cell.Positive) :
    (child hand cell).Positive := by
  rw [Cell.Positive, child_width]
  exact div_pos positive (by norm_num)

/-- Every child lies inside its parent. -/
theorem contains_child (hand : Hand) {cell : Cell} (positive : cell.Positive) :
    cell.Contains (child hand cell) := by
  have width_nonneg : 0 ≤ cell.width := positive.le
  cases hand with
  | left =>
      constructor
      · exact le_rfl
      · change cell.lower + cell.width / 3 ≤ cell.upper
        rw [Cell.width] at width_nonneg ⊢
        linarith
  | right =>
      constructor
      · change cell.lower ≤ cell.lower + 2 * cell.width / 3
        linarith
      · exact le_rfl

/-- The open gap between siblings has exactly one third of the parent width. -/
theorem sibling_gap (cell : Cell) :
    (rightChild cell).lower - (leftChild cell).upper = cell.width / 3 := by
  simp [rightChild, leftChild]
  ring

/-- The two child faces return an exact total-width reading of their
parent's generator. This is a constitutive scale identity, not a sampled
or externally supplied bound. -/
theorem sibling_total_width (cell : Cell) :
    (leftChild cell).width + (rightChild cell).width =
      (2 / 3 : ℚ) * cell.width := by
  simp [leftChild, rightChild, Cell.width]
  ring

/-- Positive parent width makes the two child cells strictly separated. -/
theorem siblings_separated {cell : Cell} (positive : cell.Positive) :
    (leftChild cell).upper < (rightChild cell).lower := by
  have gap_positive : 0 < cell.width / 3 := div_pos positive (by norm_num)
  linarith [sibling_gap cell]

/-- Ordered restriction words generate the finite approximants.  The head is the newest local
restriction, so the tail is its exact coarser parent address. -/
def descend : List Hand → Cell → Cell
  | [], cell => cell
  | hand :: word, cell => child hand (descend word cell)

/-- The exact similarity ratio after any finite restriction word. -/
theorem descend_width (word : List Hand) (cell : Cell) :
    (descend word cell).width = (1 / 3 : ℚ) ^ word.length * cell.width := by
  induction word with
  | nil => simp [descend]
  | cons hand word induction =>
      rw [descend, child_width, induction]
      simp only [List.length_cons, pow_succ]
      ring

/-- Every finite descendant of a positive cell remains positive. -/
theorem descend_positive (word : List Hand) {cell : Cell} (positive : cell.Positive) :
    (descend word cell).Positive := by
  induction word with
  | nil => simpa [descend] using positive
  | cons hand word induction =>
      exact child_positive hand induction

/-- Containment is transitive as an exact chart relation. -/
theorem Cell.Contains.trans {first second third : Cell}
    (firstSecond : first.Contains second) (secondThird : second.Contains third) :
    first.Contains third :=
  ⟨firstSecond.1.trans secondThird.1, secondThird.2.trans firstSecond.2⟩

/-- Every finite descendant is geometrically contained in its source cell. -/
theorem contains_descend (word : List Hand) {cell : Cell} (positive : cell.Positive) :
    cell.Contains (descend word cell) := by
  induction word with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons hand word induction =>
      exact induction.trans (contains_child hand (descend_positive word positive))

/-- The unit rational source cell. -/
def root : Cell := ⟨0, 1⟩

theorem root_positive : root.Positive := by
  norm_num [root, Cell.Positive, Cell.width]

/-- Every addressed finite cell has the exact rational width `3⁻ⁿ`. -/
theorem root_descend_width (word : List Hand) :
    (descend word root).width = (1 / 3 : ℚ) ^ word.length := by
  rw [descend_width]
  norm_num [root, Cell.width]

/-- The two possible newest restrictions over one parent address have the same coarse address. -/
theorem polarized_addresses_share_parent (word : List Hand) :
    (Hand.left :: word).tail = (Hand.right :: word).tail := rfl

/-- Yet their geometric cells are strictly separated.  Coarse address equality therefore retains
both polarized children in its reconstruction fibre rather than identifying their geometry. -/
theorem polarized_descendants_are_separated (word : List Hand) :
    (descend (Hand.left :: word) root).upper <
      (descend (Hand.right :: word) root).lower := by
  exact siblings_separated (descend_positive word root_positive)

/-- Restriction chronology is geometric data: left-then-right and right-then-left occupy distinct
cells even though their hand populations agree. -/
theorem restriction_word_cannot_collapse_to_a_multiset :
    descend [.left, .right] root ≠ descend [.right, .left] root := by
  norm_num [descend, child, leftChild, rightChild, root, Cell.width]

/-! ## Integration by conjugate reflection over the packing

The cells above are the images of the unit cell under the two Cantor maps `S₀ x = x/3` and
`S₁ x = (x+2)/3`.  The half-turn `J x = 1 − x` about the centre `½` conjugates one into the other,
`S₁ = J S₀ J`, and `J J = id`.  Along a restriction word `w` the composite `S_w` contracts every
distance by exactly `3^(−|w|)`.

The finite word partition at depth `n` is a receiver's grain: it reads a function `f` only through
the word average `A_n(f, x₀) = 2^(−n) Σ_(|w|=n) f(S_w x₀)`.  What the grain leaves is the residual
`K·3^(−n)` of a function with Lipschitz constant `K`: two base points, or two depths `≥ n`, differ
by at most that much.  The limit is the integral against the equal-weight self-similar measure,
and the reflection sends every word to its complement word, so the integral of `f ∘ J` is the
integral of `f`: integration by reflection.

The finite laws hold in every linearly ordered field, so over `ℚ` they are exact rational
identities and bounds; only the limit is taken in `ℝ`.  The measure itself is not constructed
here: `reflectedIntegral` is the limit of the grains, and its identification with a Mathlib measure
integral is an open join. -/

section Reflection

/-- [definition] The complementary hand: the half-turn `J` exchanges the two restrictions. -/
def Hand.flip : Hand → Hand
  | .left => .right
  | .right => .left

/-- [proved-derived; formal-checked] Complementing a hand twice returns it. -/
@[simp] theorem Hand.flip_flip (hand : Hand) : hand.flip.flip = hand := by
  cases hand <;> rfl

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- [definition] The two Cantor maps: `S₀ x = x/3` (left) and `S₁ x = (x+2)/3` (right).  Their
images of the unit cell are `leftChild root` and `rightChild root`. -/
def cantorMap : Hand → 𝕜 → 𝕜
  | .left, x => x / 3
  | .right, x => (x + 2) / 3

/-- [definition] The reflection `J x = 1 − x`: the half-turn of the unit cell about `½`. -/
def reflect (x : 𝕜) : 𝕜 := 1 - x

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] `J ∘ J = id`: the reflection is an involution. -/
theorem reflect_reflect (x : 𝕜) : reflect (reflect x) = x := by
  simp [reflect]

/-- [proved-derived; formal-checked] `S₁ = J ∘ S₀ ∘ J`: the right restriction is the left one
conjugated by the half-turn. -/
theorem cantorMap_right_eq_conj (x : 𝕜) :
    cantorMap .right x = reflect (cantorMap .left (reflect x)) := by
  simp only [cantorMap, reflect]
  ring

/-- [proved-derived; formal-checked] `J ∘ S_h = S_(h̄) ∘ J` for either hand: the reflection
carries each restriction to the complementary one. -/
theorem reflect_cantorMap (hand : Hand) (x : 𝕜) :
    reflect (cantorMap hand x) = cantorMap hand.flip (reflect x) := by
  cases hand <;> simp only [cantorMap, reflect, Hand.flip] <;> ring

/-- [proved-derived; formal-checked] Each Cantor map contracts differences by exactly `3`. -/
theorem cantorMap_sub (hand : Hand) (x y : 𝕜) :
    cantorMap hand x - cantorMap hand y = (x - y) / 3 := by
  cases hand <;> simp only [cantorMap] <;> ring

/-- [proved-derived; formal-checked] Each Cantor map sends the unit cell into itself. -/
theorem cantorMap_mem_unit (hand : Hand) {x : 𝕜} (hx : x ∈ Set.Icc (0 : 𝕜) 1) :
    cantorMap hand x ∈ Set.Icc (0 : 𝕜) 1 := by
  obtain ⟨h0, h1⟩ := hx
  cases hand <;> simp only [cantorMap, Set.mem_Icc] <;> constructor <;> linarith

/-- [proved-derived; formal-checked] The reflection sends the unit cell onto itself. -/
theorem reflect_mem_unit {x : 𝕜} (hx : x ∈ Set.Icc (0 : 𝕜) 1) :
    reflect x ∈ Set.Icc (0 : 𝕜) 1 := by
  obtain ⟨h0, h1⟩ := hx
  simp only [reflect, Set.mem_Icc]
  constructor <;> linarith

/-- [definition] The composite `S_w` along a restriction word.  As in `descend`, the head is the
newest, finest restriction, so it acts first: `S_(h :: w) = S_w ∘ S_h`. -/
def wordMap : List Hand → 𝕜 → 𝕜
  | [], x => x
  | hand :: word, x => wordMap word (cantorMap hand x)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] Composites concatenate: `S_(u ++ v) = S_v ∘ S_u`. -/
theorem wordMap_append (u v : List Hand) (x : 𝕜) :
    wordMap (u ++ v) x = wordMap v (wordMap u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons hand u ih => exact ih _

/-- [proved-derived; formal-checked] **Exact contraction.** `S_w x − S_w y = 3^(−|w|)·(x − y)`. -/
theorem wordMap_sub (word : List Hand) (x y : 𝕜) :
    wordMap word x - wordMap word y = (1 / 3 : 𝕜) ^ word.length * (x - y) := by
  induction word generalizing x y with
  | nil => simp [wordMap]
  | cons hand word ih =>
      rw [wordMap, wordMap, ih, cantorMap_sub, List.length_cons, pow_succ]
      ring

/-- [proved-derived; formal-checked] `|S_w x − S_w y| = 3^(−|w|)·|x − y|`. -/
theorem abs_wordMap_sub (word : List Hand) (x y : 𝕜) :
    |wordMap word x - wordMap word y| = (1 / 3 : 𝕜) ^ word.length * |x - y| := by
  rw [wordMap_sub, abs_mul, abs_of_nonneg (by positivity)]

/-- [proved-derived; formal-checked] Every composite sends the unit cell into itself. -/
theorem wordMap_mem_unit (word : List Hand) {x : 𝕜} (hx : x ∈ Set.Icc (0 : 𝕜) 1) :
    wordMap word x ∈ Set.Icc (0 : 𝕜) 1 := by
  induction word generalizing x with
  | nil => simpa [wordMap] using hx
  | cons hand word ih => exact ih (cantorMap_mem_unit hand hx)

/-- [proved-derived; formal-checked] **The reflection complements the word.**
`J ∘ S_w ∘ J = S_(w̄)`, where `w̄` flips every hand. -/
theorem reflect_wordMap_reflect (word : List Hand) (x : 𝕜) :
    reflect (wordMap word (reflect x)) = wordMap (word.map Hand.flip) x := by
  induction word generalizing x with
  | nil => simp [wordMap, reflect_reflect]
  | cons hand word ih =>
      have conj : cantorMap hand (reflect x) = reflect (cantorMap hand.flip x) := by
        rw [reflect_cantorMap, Hand.flip_flip]
      rw [List.map_cons, wordMap, wordMap, conj, ih]

/-- [proved-derived; formal-checked] The composites chart the addressed cells: over `ℚ`,
`descend w root = [S_w 0, S_w 1]`. -/
theorem descend_root_eq_wordMap (word : List Hand) :
    descend word root = ⟨wordMap word 0, wordMap word 1⟩ := by
  induction word with
  | nil => rfl
  | cons hand word ih =>
      have affine : ∀ y : ℚ, wordMap word y = wordMap word 0 + (1 / 3 : ℚ) ^ word.length * y := by
        intro y
        have := wordMap_sub word y 0
        linarith
      rw [descend, ih, wordMap, wordMap, affine (cantorMap hand 0), affine (cantorMap hand 1),
        affine 1]
      cases hand <;> simp only [child, leftChild, rightChild, Cell.width, cantorMap] <;>
        congr 1 <;> ring

/-- [definition] The restriction words of length `n`, each exactly once
(`mem_words`, `nodup_words`). -/
def words : ℕ → List (List Hand)
  | 0 => [[]]
  | n + 1 => (words n).map (Hand.left :: ·) ++ (words n).map (Hand.right :: ·)

/-- [proved-derived; formal-checked] `words n` holds exactly the words of length `n`. -/
theorem mem_words {n : ℕ} {word : List Hand} : word ∈ words n ↔ word.length = n := by
  induction n generalizing word with
  | zero => simp [words]
  | succ n ih =>
      cases word with
      | nil => simp [words]
      | cons hand word => cases hand <;> simp [words, ih]

/-- [proved-derived; formal-checked] `words n` lists no word twice. -/
theorem nodup_words (n : ℕ) : (words n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
      rw [words, List.nodup_append]
      refine ⟨ih.map (fun _ _ h => List.cons_injective h),
        ih.map (fun _ _ h => List.cons_injective h), ?_⟩
      simp

/-- [proved-derived; formal-checked] There are `2^n` words of length `n`. -/
theorem length_words (n : ℕ) : (words n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [words, List.length_append, List.length_map, List.length_map, ih, pow_succ]
      ring

/-- [proved-derived; formal-checked] Complementing every word permutes the words of length `n`. -/
theorem words_map_flip_perm (n : ℕ) : ((words n).map (List.map Hand.flip)).Perm (words n) := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
      have hl : (List.map Hand.flip ∘ (Hand.left :: ·)) =
          (Hand.right :: ·) ∘ List.map Hand.flip := by
        funext word
        rfl
      have hr : (List.map Hand.flip ∘ (Hand.right :: ·)) =
          (Hand.left :: ·) ∘ List.map Hand.flip := by
        funext word
        rfl
      rw [words, List.map_append, List.map_map, List.map_map, hl, hr, ← List.map_map,
        ← List.map_map]
      exact ((ih.map _).append (ih.map _)).trans List.perm_append_comm

/-- [definition] The word sum `Σ_(|w|=n) f(S_w x)`. -/
def wordSum (n : ℕ) (f : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 :=
  ((words n).map fun word => f (wordMap word x)).sum

/-- [definition] **The word average** `A_n(f, x) = 2^(−n) Σ_(|w|=n) f(S_w x)`: the reading of `f`
at the grain of the depth-`n` word partition. -/
def wordAverage (n : ℕ) (f : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 :=
  wordSum n f x / 2 ^ n

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] The depth-`0` grain reads `f` at the base point. -/
theorem wordSum_zero (f : 𝕜 → 𝕜) (x : 𝕜) : wordSum 0 f x = f x := by
  simp [wordSum, words, wordMap]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] The fine refinement: splitting on the newest hand. -/
theorem wordSum_succ (n : ℕ) (f : 𝕜 → 𝕜) (x : 𝕜) :
    wordSum (n + 1) f x = wordSum n f (cantorMap .left x) + wordSum n f (cantorMap .right x) := by
  simp only [wordSum, words, List.map_append, List.map_map, List.sum_append, Function.comp_def,
    wordMap]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] The coarse refinement: splitting on the oldest hand,
`Σ_(|w|=n+1) f∘S_w = Σ_(|w|=n) (f∘S₀)∘S_w + Σ_(|w|=n) (f∘S₁)∘S_w`. -/
theorem wordSum_succ_restrict (n : ℕ) (f : 𝕜 → 𝕜) (x : 𝕜) :
    wordSum (n + 1) f x = wordSum n (f ∘ cantorMap .left) x + wordSum n (f ∘ cantorMap .right) x := by
  induction n generalizing x with
  | zero => simp [wordSum_succ, wordSum_zero]
  | succ n ih =>
      rw [wordSum_succ (n + 1) f x, ih (cantorMap .left x), ih (cantorMap .right x),
        wordSum_succ n (f ∘ cantorMap .left) x, wordSum_succ n (f ∘ cantorMap .right) x]
      ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] The `n`-fold restricted-map sum:
`Σ_(|u|=n+m) f∘S_u = Σ_(|w|=n) Σ_(|v|=m) (f∘S_w)∘S_v`. -/
theorem wordSum_add_restrict (n m : ℕ) (f : 𝕜 → 𝕜) (x : 𝕜) :
    wordSum (n + m) f x = ((words n).map fun word => wordSum m (f ∘ wordMap word) x).sum := by
  induction n generalizing m with
  | zero =>
      simp only [Nat.zero_add, words, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rfl
  | succ n ih =>
      rw [show n + 1 + m = n + (m + 1) by omega, ih (m + 1)]
      simp only [wordSum_succ_restrict m, List.sum_map_add, words, List.map_append, List.map_map,
        List.sum_append]
      rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] A list sum of differences is the difference of the sums. -/
private theorem list_sum_map_sub {ι : Type*} (l : List ι) (g h : ι → 𝕜) :
    (l.map fun i => g i - h i).sum = (l.map g).sum - (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- [proved-derived; formal-checked] The average of a constant is that constant. -/
theorem wordAverage_const (n : ℕ) (c x : 𝕜) : wordAverage n (fun _ => c) x = c := by
  simp only [wordAverage, wordSum, List.map_const', List.sum_replicate, length_words, nsmul_eq_mul]
  push_cast
  field_simp

/-- [proved-derived; formal-checked] The average is affine in the function:
`A_n(c − f, x) = c − A_n(f, x)`. -/
theorem wordAverage_const_sub (n : ℕ) (c : 𝕜) (f : 𝕜 → 𝕜) (x : 𝕜) :
    wordAverage n (fun y => c - f y) x = c - wordAverage n f x := by
  have hsum : wordSum n (fun y => c - f y) x = wordSum n (fun _ => c) x - wordSum n f x :=
    list_sum_map_sub (words n) (fun _ => c) fun word => f (wordMap word x)
  have hc := wordAverage_const n c x
  simp only [wordAverage] at hc ⊢
  rw [hsum, sub_div, hc]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] `A_0(f, x) = f x`. -/
theorem wordAverage_zero (f : 𝕜 → 𝕜) (x : 𝕜) : wordAverage 0 f x = f x := by
  simp [wordAverage, wordSum_zero]

/-- [proved-derived; formal-checked] **Refinement at the finest hand.**
`A_(n+1)(f, x) = ½(A_n(f, S₀ x) + A_n(f, S₁ x))`. -/
theorem wordAverage_succ (n : ℕ) (f : 𝕜 → 𝕜) (x : 𝕜) :
    wordAverage (n + 1) f x =
      (wordAverage n f (cantorMap .left x) + wordAverage n f (cantorMap .right x)) / 2 := by
  simp only [wordAverage, wordSum_succ, pow_succ]
  field_simp

/-- [proved-derived; formal-checked] **The refinement identity** (restricted-map form of the
self-similar equation): `A_(n+1)(f, x) = ½(A_n(f∘S₀, x) + A_n(f∘S₁, x))`. -/
theorem wordAverage_succ_restrict (n : ℕ) (f : 𝕜 → 𝕜) (x : 𝕜) :
    wordAverage (n + 1) f x =
      (wordAverage n (f ∘ cantorMap .left) x + wordAverage n (f ∘ cantorMap .right) x) / 2 := by
  simp only [wordAverage, wordSum_succ_restrict, pow_succ]
  field_simp

/-- [proved-derived; formal-checked] **The `n`-fold self-similar equation at finite grain:**
`A_(n+m)(f, x) = 2^(−n) Σ_(|w|=n) A_m(f∘S_w, x)`. -/
theorem wordAverage_add_restrict (n m : ℕ) (f : 𝕜 → 𝕜) (x : 𝕜) :
    wordAverage (n + m) f x =
      ((words n).map fun word => wordAverage m (f ∘ wordMap word) x).sum / 2 ^ n := by
  rw [wordAverage, wordSum_add_restrict n m]
  simp only [wordAverage, div_eq_mul_inv, List.sum_map_mul_right, pow_add, mul_inv]
  ring

/-- [proved-derived; formal-checked] **Reflection invariance at every grain:**
`A_n(f∘J, J x) = A_n(f, x)`.  The reflection sends the word `w` to its complement `w̄`
(`reflect_wordMap_reflect`), and complementation permutes the words of length `n`. -/
theorem wordAverage_reflect (n : ℕ) (f : 𝕜 → 𝕜) (x : 𝕜) :
    wordAverage n (f ∘ reflect) (reflect x) = wordAverage n f x := by
  have hsum : wordSum n (f ∘ reflect) (reflect x) = wordSum n f x := by
    have hmap : (words n).map (fun word => (f ∘ reflect) (wordMap word (reflect x))) =
        ((words n).map (List.map Hand.flip)).map (fun word => f (wordMap word x)) := by
      rw [List.map_map]
      refine List.map_congr_left fun word _ => ?_
      simp [reflect_wordMap_reflect]
    rw [wordSum, hmap, ((words_map_flip_perm n).map _).sum_eq, wordSum]
  rw [wordAverage, hsum, wordAverage]

/-- [definition] `f` is `K`-Lipschitz on the unit cell. -/
def LipschitzOnUnit (K : 𝕜) (f : 𝕜 → 𝕜) : Prop :=
  ∀ ⦃x⦄, x ∈ Set.Icc (0 : 𝕜) 1 → ∀ ⦃y⦄, y ∈ Set.Icc (0 : 𝕜) 1 → |f x - f y| ≤ K * |x - y|

namespace LipschitzOnUnit

variable {K : 𝕜} {f : 𝕜 → 𝕜}

/-- [proved-derived; formal-checked] A Lipschitz constant on the unit cell is nonnegative. -/
theorem nonneg (hf : LipschitzOnUnit K f) : 0 ≤ K := by
  have h := hf (x := 1) ⟨zero_le_one, le_rfl⟩ (y := 0) ⟨le_rfl, zero_le_one⟩
  rw [sub_zero, abs_one, mul_one] at h
  exact (abs_nonneg _).trans h

/-- [proved-derived; formal-checked] Restriction along `S_h` divides the constant by `3`. -/
theorem comp_cantorMap (hf : LipschitzOnUnit K f) (hand : Hand) :
    LipschitzOnUnit (K / 3) (f ∘ cantorMap hand) := by
  intro x hx y hy
  calc |f (cantorMap hand x) - f (cantorMap hand y)|
      ≤ K * |cantorMap hand x - cantorMap hand y| :=
        hf (cantorMap_mem_unit hand hx) (cantorMap_mem_unit hand hy)
    _ = K / 3 * |x - y| := by
        rw [cantorMap_sub, abs_div, abs_of_pos (by norm_num : (0 : 𝕜) < 3)]
        ring

/-- [proved-derived; formal-checked] Restriction along `S_w` multiplies the constant by
`3^(−|w|)`. -/
theorem comp_wordMap (hf : LipschitzOnUnit K f) (word : List Hand) :
    LipschitzOnUnit (K * (1 / 3 : 𝕜) ^ word.length) (f ∘ wordMap word) := by
  intro x hx y hy
  calc |f (wordMap word x) - f (wordMap word y)|
      ≤ K * |wordMap word x - wordMap word y| :=
        hf (wordMap_mem_unit word hx) (wordMap_mem_unit word hy)
    _ = K * (1 / 3 : 𝕜) ^ word.length * |x - y| := by
        rw [abs_wordMap_sub]
        ring

/-- [proved-derived; formal-checked] The reflection keeps the constant. -/
theorem comp_reflect (hf : LipschitzOnUnit K f) : LipschitzOnUnit K (f ∘ reflect) := by
  intro x hx y hy
  calc |f (reflect x) - f (reflect y)| ≤ K * |reflect x - reflect y| :=
        hf (reflect_mem_unit hx) (reflect_mem_unit hy)
    _ = K * |x - y| := by
        rw [show reflect x - reflect y = -(x - y) by simp only [reflect]; ring, abs_neg]

end LipschitzOnUnit

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] The difference of two half-sums. -/
private theorem abs_half_sum_sub_half_sum (a b c d : 𝕜) :
    (a + b) / 2 - (c + d) / 2 = ((a - c) + (b - d)) / 2 := by
  ring

/-- [proved-derived; formal-checked] **The grain residual between base points.** For `f`
`K`-Lipschitz on the unit cell and `x, y` in it,
`|A_n(f, x) − A_n(f, y)| ≤ K·3^(−n)·|x − y|`. -/
theorem abs_wordAverage_sub_le_mul {K : 𝕜} {f : 𝕜 → 𝕜} (hf : LipschitzOnUnit K f) (n : ℕ)
    {x y : 𝕜} (hx : x ∈ Set.Icc (0 : 𝕜) 1) (hy : y ∈ Set.Icc (0 : 𝕜) 1) :
    |wordAverage n f x - wordAverage n f y| ≤ K * (1 / 3 : 𝕜) ^ n * |x - y| := by
  induction n generalizing x y with
  | zero => simpa [wordAverage_zero] using hf hx hy
  | succ n ih =>
      have h0 := ih (cantorMap_mem_unit .left hx) (cantorMap_mem_unit .left hy)
      have h1 := ih (cantorMap_mem_unit .right hx) (cantorMap_mem_unit .right hy)
      have hK := hf.nonneg
      rw [cantorMap_sub, abs_div, abs_of_pos (by norm_num : (0 : 𝕜) < 3)] at h0 h1
      rw [wordAverage_succ, wordAverage_succ, abs_half_sum_sub_half_sum, abs_div, abs_two]
      calc |(wordAverage n f (cantorMap .left x) - wordAverage n f (cantorMap .left y)) +
              (wordAverage n f (cantorMap .right x) - wordAverage n f (cantorMap .right y))| / 2
          ≤ (|wordAverage n f (cantorMap .left x) - wordAverage n f (cantorMap .left y)| +
              |wordAverage n f (cantorMap .right x) - wordAverage n f (cantorMap .right y)|) / 2 := by
            gcongr
            exact abs_add_le _ _
        _ ≤ (K * (1 / 3 : 𝕜) ^ n * (|x - y| / 3) + K * (1 / 3 : 𝕜) ^ n * (|x - y| / 3)) / 2 := by
            gcongr
        _ = K * (1 / 3 : 𝕜) ^ (n + 1) * |x - y| := by
            rw [pow_succ]
            ring

/-- [proved-derived; formal-checked] **(1) The Lipschitz grain bound.** For `x₀, y₀` in the unit
cell, `|A_n(f, x₀) − A_n(f, y₀)| ≤ K·3^(−n)`: the depth-`n` grain cannot tell two base points
apart by more than the residual it leaves. -/
theorem abs_wordAverage_sub_le {K : 𝕜} {f : 𝕜 → 𝕜} (hf : LipschitzOnUnit K f) (n : ℕ)
    {x y : 𝕜} (hx : x ∈ Set.Icc (0 : 𝕜) 1) (hy : y ∈ Set.Icc (0 : 𝕜) 1) :
    |wordAverage n f x - wordAverage n f y| ≤ K * (1 / 3 : 𝕜) ^ n := by
  have hxy : |x - y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  calc |wordAverage n f x - wordAverage n f y| ≤ K * (1 / 3 : 𝕜) ^ n * |x - y| :=
        abs_wordAverage_sub_le_mul hf n hx hy
    _ ≤ K * (1 / 3 : 𝕜) ^ n * 1 := by
        have := hf.nonneg
        gcongr
    _ = K * (1 / 3 : 𝕜) ^ n := mul_one _

/-- [proved-derived; formal-checked] **Refinement stays inside the grain.** For `x, y` in the
unit cell and every `k`, `|A_(n+k)(f, x) − A_n(f, y)| ≤ K·3^(−n)`. -/
theorem abs_wordAverage_add_sub_le {K : 𝕜} {f : 𝕜 → 𝕜} (hf : LipschitzOnUnit K f) (n k : ℕ)
    {x y : 𝕜} (hx : x ∈ Set.Icc (0 : 𝕜) 1) (hy : y ∈ Set.Icc (0 : 𝕜) 1) :
    |wordAverage (n + k) f x - wordAverage n f y| ≤ K * (1 / 3 : 𝕜) ^ n := by
  induction k generalizing x with
  | zero => exact abs_wordAverage_sub_le hf n hx hy
  | succ k ih =>
      have h0 := ih (cantorMap_mem_unit .left hx)
      have h1 := ih (cantorMap_mem_unit .right hx)
      rw [← Nat.add_assoc, wordAverage_succ]
      set a := wordAverage (n + k) f (cantorMap .left x)
      set b := wordAverage (n + k) f (cantorMap .right x)
      set c := wordAverage n f y
      rw [show (a + b) / 2 - c = ((a - c) + (b - c)) / 2 by ring, abs_div, abs_two]
      calc |(a - c) + (b - c)| / 2 ≤ (|a - c| + |b - c|) / 2 := by
            gcongr
            exact abs_add_le _ _
        _ ≤ (K * (1 / 3 : 𝕜) ^ n + K * (1 / 3 : 𝕜) ^ n) / 2 := by gcongr
        _ = K * (1 / 3 : 𝕜) ^ n := by ring

/-- [proved-derived; formal-checked] **(3) The Cauchy bound.** For `x, y` in the unit cell,
`|A_n(f, x) − A_m(f, y)| ≤ K·3^(−min(n,m))`; with `x = y` this is the bound between two grains
at one base point.  The coarser grain fixes the residual. -/
theorem abs_wordAverage_sub_wordAverage_le {K : 𝕜} {f : 𝕜 → 𝕜} (hf : LipschitzOnUnit K f)
    (n m : ℕ) {x y : 𝕜} (hx : x ∈ Set.Icc (0 : 𝕜) 1) (hy : y ∈ Set.Icc (0 : 𝕜) 1) :
    |wordAverage n f x - wordAverage m f y| ≤ K * (1 / 3 : 𝕜) ^ min n m := by
  rcases le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [min_eq_left h, abs_sub_comm]
    exact abs_wordAverage_add_sub_le hf n k hy hx
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [min_eq_right h]
    exact abs_wordAverage_add_sub_le hf m k hx hy

/-- [proved-derived; formal-checked] **The exact residual of the first moment.**
`A_n(id, x) = ½ + 3^(−n)·(x − ½)`: the grain at depth `n` leaves exactly `3^(−n)·(x − ½)`, which
vanishes at the fixed point `½` of the reflection `J`. -/
theorem wordAverage_id (n : ℕ) (x : 𝕜) :
    wordAverage n id x = 1 / 2 + (1 / 3 : 𝕜) ^ n * (x - 1 / 2) := by
  induction n generalizing x with
  | zero =>
      rw [wordAverage_zero, pow_zero]
      simp
  | succ n ih =>
      rw [wordAverage_succ, ih, ih, pow_succ]
      simp only [cantorMap]
      ring

/-- [proved-derived; formal-checked] **Integration by reflection at finite grain.** Over the
identity, `A_n(id, x) + A_n(id, J x) = 1`: the reflection pairs every word with its complement,
whose images sum to `1`. -/
theorem wordAverage_id_add_reflect (n : ℕ) (x : 𝕜) :
    wordAverage n id x + wordAverage n id (reflect x) = 1 := by
  have h := wordAverage_reflect n (id : 𝕜 → 𝕜) (reflect x)
  rw [reflect_reflect] at h
  have hJ : (id ∘ reflect : 𝕜 → 𝕜) = fun y => 1 - id y := rfl
  rw [hJ, wordAverage_const_sub] at h
  linarith

end Reflection

/-! ### The limit: the integral against the self-similar measure -/

section Limit

open Filter Topology

/-- [proved-derived; formal-checked] The word averages of a Lipschitz function form a Cauchy
sequence in `ℝ`. -/
theorem cauchySeq_wordAverage {K : ℝ} {f : ℝ → ℝ} (hf : LipschitzOnUnit K f) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : CauchySeq fun n => wordAverage n f x := by
  refine cauchySeq_of_le_geometric (1 / 3) K (by norm_num) fun n => ?_
  rw [Real.dist_eq, abs_sub_comm]
  exact abs_wordAverage_add_sub_le hf n 1 hx hx

/-- [definition] The reflected integral: the limit of the word averages at the base point `0`,
the fixed point of `S₀`.  For Lipschitz `f` it is the integral of `f` against the equal-weight
self-similar measure, and every base point in the unit cell gives it (`tendsto_wordAverage`). -/
noncomputable def reflectedIntegral (f : ℝ → ℝ) : ℝ :=
  limUnder atTop fun n => wordAverage n f 0

private theorem zero_mem_unit : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩

/-- [proved-derived; formal-checked] **The limit exists and forgets the base point.** For
`K`-Lipschitz `f` and any `x₀` in the unit cell, `A_n(f, x₀) → ∫ f dμ`. -/
theorem tendsto_wordAverage {K : ℝ} {f : ℝ → ℝ} (hf : LipschitzOnUnit K f) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => wordAverage n f x) atTop (𝓝 (reflectedIntegral f)) := by
  have h0 : Tendsto (fun n => wordAverage n f 0) atTop (𝓝 (reflectedIntegral f)) :=
    (cauchySeq_wordAverage hf zero_mem_unit).tendsto_limUnder
  refine tendsto_of_tendsto_of_dist h0 ?_
  have hgeom : Tendsto (fun n : ℕ => K * (1 / 3 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num)).const_mul K
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hgeom
  rw [Real.dist_eq]
  exact abs_wordAverage_sub_le hf n zero_mem_unit hx

/-- [proved-derived; formal-checked] **The finite-partition error.** For `K`-Lipschitz `f` and
`x₀` in the unit cell, `|A_n(f, x₀) − ∫ f dμ| ≤ K·3^(−n)`: the residual the depth-`n` grain
leaves. -/
theorem abs_wordAverage_sub_reflectedIntegral_le {K : ℝ} {f : ℝ → ℝ} (hf : LipschitzOnUnit K f)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |wordAverage n f x - reflectedIntegral f| ≤ K * (1 / 3 : ℝ) ^ n := by
  have hlim : Tendsto (fun m => |wordAverage n f x - wordAverage m f x|) atTop
      (𝓝 |wordAverage n f x - reflectedIntegral f|) :=
    ((tendsto_wordAverage hf hx).const_sub _).abs
  refine le_of_tendsto hlim (eventually_atTop.2 ⟨n, fun m hm => ?_⟩)
  have h := abs_wordAverage_sub_wordAverage_le hf n m hx hx
  rwa [min_eq_left hm] at h

/-- [proved-derived; formal-checked] **The self-similar equation over `n`-words.**
`∫ f dμ = 2^(−n) Σ_(|w|=n) ∫ f∘S_w dμ` for Lipschitz `f`. -/
theorem reflectedIntegral_eq_sum {K : ℝ} {f : ℝ → ℝ} (hf : LipschitzOnUnit K f) (n : ℕ) :
    reflectedIntegral f =
      ((words n).map fun word => reflectedIntegral (f ∘ wordMap word)).sum / 2 ^ n := by
  have hshift : Tendsto (fun m => wordAverage (n + m) f 0) atTop (𝓝 (reflectedIntegral f)) := by
    have := (tendsto_add_atTop_iff_nat n).2 (tendsto_wordAverage hf zero_mem_unit)
    simpa only [add_comm] using this
  have hsum : Tendsto (fun m => ((words n).map fun word =>
      wordAverage m (f ∘ wordMap word) 0).sum / 2 ^ n) atTop
      (𝓝 (((words n).map fun word => reflectedIntegral (f ∘ wordMap word)).sum / 2 ^ n)) :=
    (tendsto_list_sum _ fun word _ =>
      tendsto_wordAverage (hf.comp_wordMap word) zero_mem_unit).div_const _
  refine tendsto_nhds_unique hshift ?_
  simpa only [wordAverage_add_restrict] using hsum

/-- [proved-derived; formal-checked] **(2) The self-similar equation.**
`∫ f dμ = ½ ∫ f∘S₀ dμ + ½ ∫ f∘S₁ dμ` for Lipschitz `f`. -/
theorem reflectedIntegral_self_similar {K : ℝ} {f : ℝ → ℝ} (hf : LipschitzOnUnit K f) :
    reflectedIntegral f =
      (reflectedIntegral (f ∘ cantorMap .left) + reflectedIntegral (f ∘ cantorMap .right)) / 2 := by
  have hshift : Tendsto (fun n => wordAverage (n + 1) f 0) atTop (𝓝 (reflectedIntegral f)) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_wordAverage hf zero_mem_unit)
  have hsplit := ((tendsto_wordAverage (hf.comp_cantorMap .left) zero_mem_unit).add
    (tendsto_wordAverage (hf.comp_cantorMap .right) zero_mem_unit)).div_const 2
  refine tendsto_nhds_unique hshift ?_
  simpa only [wordAverage_succ_restrict] using hsplit

/-- [proved-derived; formal-checked] **(4) Integration by reflection.** `∫ f∘J dμ = ∫ f dμ` for
Lipschitz `f`: the reflection sends every word to its complement word, so the self-similar
measure is `J`-invariant. -/
theorem reflectedIntegral_reflect {K : ℝ} {f : ℝ → ℝ} (hf : LipschitzOnUnit K f) :
    reflectedIntegral (f ∘ reflect) = reflectedIntegral f := by
  have hJ : reflect (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := reflect_mem_unit zero_mem_unit
  have hleft := tendsto_wordAverage hf.comp_reflect hJ
  simp only [wordAverage_reflect] at hleft
  exact tendsto_nhds_unique hleft (tendsto_wordAverage hf zero_mem_unit)

/-- [proved-derived; formal-checked] **The centre is read by reflection alone.** The first
moment of the self-similar measure is `∫ x dμ = ½`: reflection gives `∫ x dμ = ∫ (1 − x) dμ`,
and the average of a constant is that constant. -/
theorem reflectedIntegral_id : reflectedIntegral id = 1 / 2 := by
  have hid : LipschitzOnUnit (1 : ℝ) id := fun x _ y _ => by simp
  have hrefl := reflectedIntegral_reflect hid
  have hJ : Tendsto (fun n => wordAverage n (id ∘ reflect) 0) atTop
      (𝓝 (1 - reflectedIntegral id)) := by
    have hc : (id ∘ reflect : ℝ → ℝ) = fun y => 1 - id y := rfl
    simp only [hc, wordAverage_const_sub]
    exact (tendsto_wordAverage hid zero_mem_unit).const_sub 1
  have hJ' := tendsto_wordAverage hid.comp_reflect zero_mem_unit
  have := tendsto_nhds_unique hJ' hJ
  linarith

end Limit

section Audit

#print axioms child_width
#print axioms siblings_separated
#print axioms sibling_total_width
#print axioms descend_width
#print axioms contains_descend
#print axioms polarized_descendants_are_separated
#print axioms restriction_word_cannot_collapse_to_a_multiset
#print axioms reflect_reflect
#print axioms cantorMap_right_eq_conj
#print axioms reflect_cantorMap
#print axioms wordMap_sub
#print axioms reflect_wordMap_reflect
#print axioms descend_root_eq_wordMap
#print axioms mem_words
#print axioms nodup_words
#print axioms length_words
#print axioms words_map_flip_perm
#print axioms wordAverage_succ
#print axioms wordAverage_succ_restrict
#print axioms wordAverage_add_restrict
#print axioms wordAverage_reflect
#print axioms wordAverage_const_sub
#print axioms abs_wordAverage_sub_le_mul
#print axioms abs_wordAverage_sub_le
#print axioms abs_wordAverage_add_sub_le
#print axioms abs_wordAverage_sub_wordAverage_le
#print axioms wordAverage_id
#print axioms wordAverage_id_add_reflect
#print axioms cauchySeq_wordAverage
#print axioms tendsto_wordAverage
#print axioms abs_wordAverage_sub_reflectedIntegral_le
#print axioms reflectedIntegral_eq_sum
#print axioms reflectedIntegral_self_similar
#print axioms reflectedIntegral_reflect
#print axioms reflectedIntegral_id

end Audit

end Holonics.Foundation.FractalPacking
