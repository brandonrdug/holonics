import Mathlib.Tactic

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
-/

namespace Soma.Holonics.Foundation.FractalPacking

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

section Audit

#print axioms child_width
#print axioms siblings_separated
#print axioms descend_width
#print axioms contains_descend
#print axioms polarized_descendants_are_separated
#print axioms restriction_word_cannot_collapse_to_a_multiset

end Audit

end Soma.Holonics.Foundation.FractalPacking
