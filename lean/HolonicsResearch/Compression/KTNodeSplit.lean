import Mathlib
import Holonics.Compression.Landmark.Context.Tree

/-!
# Krichevsky–Trofimov: the node split moves by `(y − a)/(N + 2)`, and a code is its log widths

Source: the egg record of September 27, §3 as corrected on September 28
(`research/records/2026-09-27_THE_EGG_IS_A_GENERATORS_GENOME_SELECTION_IS_BAYES_AND_THE_FACES_OF_INTEGERS_ARE_MOIRES_OF_GRATINGS.md`):
"a node's Krichevsky–Trofimov split `a = (n₀ + ½)/(N + 1)` moves by `a′ − a = (y − a)/(N + 2)`
when side `y` arrives, the descent covector `q − p` at the rate of the node's own epochs". The box
of #410 adds "the log-width sum from `Context/Tree.face_cell_width`"; its binary regret bound
`kt_regret` and the CTW redundancy at binary scope were done before (`Context/PriorMass`).

## What is proved

* **Every KT face moves toward the arrival at the node's own rate.** For any finite alphabet, one
  arrival of `y` moves the face `k(c) = (n_c + ½)/(N + |A|/2)` of `Context/Tree.ktFace` by
  `k′(c) − k(c) = ([c = y] − k(c))/(N + |A|/2 + 1)` (`ktFace_bump_sub`): the descent covector
  `q − p` of the declared comparison, the arrival's indicator less the face, at the rate one over
  the node's arrivals plus `|A|/2 + 1`.
* **The binary node split.** At `|A| = 2` the split `a = (n₀ + ½)/(N + 1)` is the face of side
  zero (`nodeSplit_eq_ktProb`), and an arrival `y` (one for side zero, zero for side one) moves it
  by `(y − a)/(N + 2)` (`nodeSplit_arrive`). The split stays strictly inside the unit interval
  (`nodeSplit_pos`, `nodeSplit_lt_one`).
* **The split is the stochastic-approximation recursion from one half.** The recursion
  `a₀ = ½`, `a_(N+1) = a_N + (y_(N+1) − a_N)/(N + 2)` read on a word of sides returns the KT
  split of its counts (`splitOf_snoc`), and it is the only law with that start and that step
  (`splitOf_unique`).
* **A code is the sum of its log widths.** The face cell of a digit word, whose width is the
  emitted face (`Context/Tree.face_cell_width`), has `−log₂ width` equal to the sum of the digits'
  `−log₂ q(prefix, bit)` (`emitCode`, `logb_emit`, `faceCell_code_length`); and the sequential KT
  likelihood's code length is the sum of its conditionals' (`ktCode_snoc`).

## Limits

* The step law is the face's own arithmetic; no claim is made that a learner's deposit at a node
  uses this rate (the record's reading, "the rate of the node's own epochs", is the interpretation
  of `N + |A|/2 + 1`).
* Code lengths are read in the real chart (`Real.logb 2`) of the rational faces; nothing here
  rounds a face to a grain.

The computational object is the helical pair interaction; of the winding guide's six objects this
touches faces and placement (the receiving face and its dyadic cell) and the tower thread (a node's
arrivals are the epochs of its section), keeping the helix, the pair, cell holonomy and the tube
attached through `Context/Tree`.

Consumers: `Context/Tree`'s node law (`ktFace`, `bump`, `ktSeq`) and its face cells
(`faceCell`, `emit`), and the atlas rows on the KT face and the node split.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.KTNodeSplit

open Holonics.Compression.Landmark.Context.Tree
open Holonics.HNN.RegionCounts (ktProb)
open Holonics.Foundation.FractalPacking (Cell root)

/-! ## 1. Every KT face moves toward the arrival -/

section Face

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- [proved-derived; formal-checked] **The KT face's step.** One arrival of `y` moves each face
`k(c) = (n_c + ½)/(N + |A|/2)` by `([c = y] − k(c))/(N + |A|/2 + 1)`: the descent covector of the
declared comparison, the arrival's indicator less the face, at the node's own rate. -/
theorem ktFace_bump_sub (n : A → ℕ) (y c : A) :
    ktFace (bump n y) c - ktFace n c =
      ((if c = y then 1 else 0) - ktFace n c) /
        (((∑ c', n c' : ℕ) : ℚ) + Fintype.card A / 2 + 1) := by
  have hk : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℚ) < ((∑ c', n c' : ℕ) : ℚ) + Fintype.card A / 2 := by positivity
  have hN1 : (0 : ℚ) < ((∑ c', n c' : ℕ) : ℚ) + Fintype.card A / 2 + 1 := by positivity
  unfold ktFace ktProb
  rw [sum_bump]
  simp only [bump]
  push_cast
  by_cases h : c = y
  · simp only [h, if_true]
    field_simp
    ring
  · simp only [h, if_false]
    field_simp
    ring

end Face

/-! ## 2. The binary node split -/

/-- [definition] **The node split** `a = (n₀ + ½)/(N + 1)`: the KT share of side zero after `N`
arrivals of which `n₀` fell on side zero. -/
def nodeSplit (n₀ N : ℕ) : ℚ := ((n₀ : ℚ) + 1 / 2) / ((N : ℚ) + 1)

/-- [proved-derived; formal-checked] The split is the binary KT face of side zero. -/
theorem nodeSplit_eq_ktProb (n₀ N : ℕ) : nodeSplit n₀ N = ktProb n₀ N 2 := by
  unfold nodeSplit ktProb
  norm_num

/-- [proved-derived; formal-checked] The split is positive. -/
theorem nodeSplit_pos (n₀ N : ℕ) : 0 < nodeSplit n₀ N := by
  unfold nodeSplit; positivity

/-- [proved-derived; formal-checked] The split is below one whenever side zero holds at most the
arrivals there are. -/
theorem nodeSplit_lt_one {n₀ N : ℕ} (h : n₀ ≤ N) : nodeSplit n₀ N < 1 := by
  unfold nodeSplit
  rw [div_lt_one (by positivity)]
  have : (n₀ : ℚ) ≤ N := by exact_mod_cast h
  linarith

/-- [definition] The arrival's side as a number: one for side zero, zero for side one. -/
def sideIndicator (b : Bool) : ℚ := if b then 1 else 0

/-- [proved-derived; formal-checked] **The node split moves by `(y − a)/(N + 2)`** when side `y`
arrives (`b = true` is side zero). -/
theorem nodeSplit_arrive (n₀ N : ℕ) (b : Bool) :
    nodeSplit (n₀ + if b then 1 else 0) (N + 1) - nodeSplit n₀ N =
      (sideIndicator b - nodeSplit n₀ N) / ((N : ℚ) + 2) := by
  unfold nodeSplit sideIndicator
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true, add_zero] <;> push_cast <;>
    field_simp <;> ring

/-! ## 3. The split is the recursion from one half -/

/-- [definition] The split read on a word of sides (`true` is side zero). -/
def splitOf (w : List Bool) : ℚ := nodeSplit (w.count true) w.length

/-- [proved-derived; formal-checked] The empty word's split is one half. -/
theorem splitOf_nil : splitOf [] = 1 / 2 := by
  simp [splitOf, nodeSplit]

/-- [proved-derived; formal-checked] **The stochastic-approximation step.** Appending a side moves
the split by `(y − a)/(N + 2)`. -/
theorem splitOf_snoc (w : List Bool) (b : Bool) :
    splitOf (w ++ [b]) = splitOf w + (sideIndicator b - splitOf w) / ((w.length : ℚ) + 2) := by
  have hstep := nodeSplit_arrive (w.count true) w.length b
  have hcount : (w ++ [b]).count true = w.count true + if b then 1 else 0 := by
    cases b <;> simp
  unfold splitOf
  rw [hcount, List.length_append, List.length_singleton]
  linarith

/-- [proved-derived; formal-checked] **The recursion has one solution**: a law that starts at one
half and takes that step on every arrival is the KT split. -/
theorem splitOf_unique (f : List Bool → ℚ) (h0 : f [] = 1 / 2)
    (hstep : ∀ w b, f (w ++ [b]) = f w + (sideIndicator b - f w) / ((w.length : ℚ) + 2)) :
    ∀ w, f w = splitOf w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => rw [h0, splitOf_nil]
  | append_singleton w b ih => rw [hstep, splitOf_snoc, ih]

/-! ## 4. A code is the sum of its log widths -/

/-- [definition] The code length of a digit word under binary faces: the sum of the digits'
`−log₂ q(prefix, bit)`. -/
noncomputable def emitCode (q : List Bool → Bool → ℚ) : List Bool → List Bool → ℝ
  | _, [] => 0
  | pre, b :: rest => -Real.logb 2 (q pre b) + emitCode q (pre ++ [b]) rest

/-- [proved-derived; formal-checked] For positive faces, `log₂` of the emitted face is minus the
summed code. -/
theorem logb_emit {q : List Bool → Bool → ℚ} (hq : ∀ π b, 0 < q π b) :
    ∀ pre l, Real.logb 2 (emit q pre l : ℝ) = -emitCode q pre l
  | pre, [] => by simp [emit, emitCode]
  | pre, b :: rest => by
      have h1 : (0 : ℝ) < q pre b := by exact_mod_cast hq pre b
      have h2 : (0 : ℝ) < emit q (pre ++ [b]) rest := by exact_mod_cast emit_pos hq _ _
      rw [emit, Rat.cast_mul, Real.logb_mul h1.ne' h2.ne', logb_emit hq (pre ++ [b]) rest,
        emitCode]
      ring

/-- [proved-derived; formal-checked] **The log-width sum.** From the unit cell, the face cell of a
digit word has `−log₂ width` equal to the sum of its digits' `−log₂ q(prefix, bit)`
(`Context/Tree.face_cell_width`). -/
theorem faceCell_code_length {q : List Bool → Bool → ℚ} (hq : ∀ π b, 0 < q π b)
    (hs : ∀ π, q π false + q π true = 1) (l : List Bool) :
    -Real.logb 2 ((faceCell q [] l root).width : ℝ) = emitCode q [] l := by
  rw [(face_cell_width q hs).2]
  simp only [root, Cell.width, sub_zero, mul_one]
  rw [logb_emit hq [] l, neg_neg]

section Sequential

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- [definition] The code length of a word under the sequential KT likelihood. -/
noncomputable def ktCode (w : List A) : ℝ := -Real.logb 2 (ktSeq w : ℝ)

/-- [proved-derived; formal-checked] **The KT code is additive along arrivals**: appending `c`
adds the conditional's code `−log₂ ((n_c + ½)/(N + |A|/2))`, and the empty word costs nothing. -/
theorem ktCode_snoc (w : List A) (c : A) :
    ktCode (w ++ [c]) =
      ktCode w - Real.logb 2 (ktProb (w.count c) w.length (Fintype.card A) : ℝ) := by
  have h1 : (0 : ℝ) < ktSeq w := by exact_mod_cast ktMass_pos (counts w)
  have h2 : (0 : ℝ) < ktProb (w.count c) w.length (Fintype.card A) := by
    have hk : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    have : (0 : ℚ) < ktProb (w.count c) w.length (Fintype.card A) := by
      unfold ktProb; positivity
    exact_mod_cast this
  unfold ktCode
  rw [ktSeq_snoc, Rat.cast_mul, Real.logb_mul h1.ne' h2.ne']
  ring

omit [Nonempty A] in
/-- [proved-derived; formal-checked] The empty word's KT code is zero. -/
theorem ktCode_nil : ktCode ([] : List A) = 0 := by
  simp [ktCode, ktSeq_nil]

end Sequential

end Holonics.Compression.KTNodeSplit
