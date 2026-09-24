import Holonics.Foundation.ContinuingTower
import Holonics.Foundation.ReceiverCodeCost

/-!
# C5 — cost as a receipt, and the receiver-relative Pareto frontier

[definition] This file deposits item **C5** of
`docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md`: a `CostReceipt` with exact natural
coordinates — `bytes`, `decodeWork`, `updateWork`, `certificateWork`, `residual` — each one a
*measured or derived count carrying its provenance*, and the receiver-relative **Pareto frontier**
of presentations that is the actual target.

The representation objective
`C(P;q) = a*bytes + b*decodeWork + c*updateWork + d*certificateWork + e*residual`
is `Weighting.objective`. It is **one receiver of the receipt** — a declared nonnegative weight
vector `q` — and never the identity of a presentation. The theorems that make that precise:

* `dominates_refl`/`dominates_trans`/`dominates_antisymm_vector` — dominance is the product partial
  order, and it is antisymmetric on the *cost vector* only: two receipts with equal counts and
  different provenance dominate each other and stay two receipts
  (`dominates_antisymm_fails_on_receipts`).
* `frontier_nonempty`, `exists_frontier_dominating`, `frontier_isAntichain` — the frontier of a
  finite nonempty family is nonempty and dominates all of it.
* `minimizer_isFrontierPoint` — every strictly positive weighting's minimizer is on the frontier.
* `unsupported_not_minimizer` — **the converse fails.** A frontier point that no weighting putting
  weight on either varying axis selects. This is the formal reason a scalar score cannot stand in
  for the frontier: the objective sees only the lower convex hull of the frontier, and a frontier
  point strictly above the chord between two others is invisible to every linear receiver.
* `frontier_reparameterization_invariant` versus
  `scalar_minimizer_not_reparameterization_invariant` — the frontier survives a monotone change of
  unit on each coordinate; the scalar minimizer does not.
* `serial_receipt_balance` and `CostReceipt.compose_vector` — receipts compose.
* `codeBits_residual_comp_le` — the residual coordinate behaves as the carrier's residual does.
* `padicCostedTower`, `unitCostedTower` and `costBoundedByRefinementRoute_padic` — two towers whose
  restrictions carry the receipts they themselves determine, and the refinement-route comparison
  discharged at one of them with neither side supplied by a caller;
  `no_costedTower_with_squaredGapReceipt` — a receipt assignment that is not one of them.

## What is **not** claimed

[definition] **Kolmogorov minimality is incomputable and no minimal encoding is asserted here.**
Nothing in this file defines, computes, approximates or bounds the shortest program for an object.
A `CostReceipt` records counts a named instrument actually produced under a named rule; `frontier`
returns the antichain of nondominated presentations among a *finite declared family*. It is not a
minimum, and `frontier_has_no_least_point` proves that in general no member of a frontier is below
all the others — so "the optimal presentation" is not a well-formed request at a receiver that
weighs more than one axis. A scalar score of a presentation is a receiver reading, exactly as
`THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md` requires of every face.

## Cited owners — nothing here is rebuilt

[established-bounded; source-inspected]

* `Foundation/ReceiverCodeCost.lean:100-126`'s `serial_boundary_balance` **owns the additivity
  law**: serial code costs add and the endpoint potentials cancel at the joined boundary through
  the stored pullback equality. `serial_receipt_balance` below *instantiates* that theorem at a
  two-chart holon; `CostReceipt.compose` is the definition it licenses, and the additivity is never
  re-proved here.
* `Foundation/ContinuingTower.lean`'s `Transition.comp` owns the composite residual: it is the
  **pair** of component residuals (`Transition.comp_residual`). The residual coordinate therefore
  behaves as the carrier's residual does — the residual *fibre* multiplies under composition and
  its *code size* is subadditive (`codeBits_residual_comp_le`), strictly so at
  `codeBits_residual_comp_lt_witness`.
* `Foundation/ContinuingTower.lean`'s open `Migration.CostBoundedByRefinementRoute` is discharged
  and sharpened in the last section rather than restated, and `padicTower`, `padicRestrictTransition`
  and `padicHalfMigration` are the tower, the transition and the migration it is discharged at —
  cited, never rebuilt.

## Rust counterpart

[definition] The paired executable owner is `crates/holonic-engine/src/presentation_cost.rs`:
`Axis`, `Provenance`, `Counted`, `CostReceipt`, `Weighting`, `ParetoPoint`, `pareto_frontier`,
`CostReceipt::compose`, `code_bits`, over `BigUint` counts and exact `BigRational` weights, with
each theorem below appearing as a named test.
-/

namespace Holonics.Foundation.PresentationCost

open Holonics
open Holonics.Foundation.ContinuingTower
open scoped BigOperators

universe u v w

/-! ## The five coordinates -/

/-- [definition] The five declared coordinates of a presentation receipt. The receipt never sums
them; summing them is what a `Weighting` does, and that is a receiver reading. -/
inductive Axis
  | /-- Octets the presentation occupies. -/ bytes
  | /-- Elementary steps to decode the object from the presentation. -/ decodeWork
  | /-- Elementary steps to re-present after one admitted change. -/ updateWork
  | /-- Elementary steps to verify that the presentation decodes to the object. -/ certificateWork
  | /-- Code size of the residual the presentation does not carry. -/ residual
  deriving DecidableEq, Repr

namespace Axis

instance : Fintype Axis where
  elems := {Axis.bytes, Axis.decodeWork, Axis.updateWork, Axis.certificateWork, Axis.residual}
  complete := fun x => by cases x <;> decide

instance : Inhabited Axis := ⟨Axis.bytes⟩

end Axis

/-- [proved-derived; formal-checked] A sum over the five axes, written out. -/
theorem sum_axis {M : Type*} [AddCommMonoid M] (f : Axis → M) :
    ∑ ax, f ax =
      f .bytes + f .decodeWork + f .updateWork + f .certificateWork + f .residual := by
  rw [show (Finset.univ : Finset Axis) =
      {Axis.bytes, Axis.decodeWork, Axis.updateWork, Axis.certificateWork, Axis.residual} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-- [definition] The exact cost vector: one natural count per axis. Its order is the **product
partial order** supplied by `Pi.partialOrder`, and that order *is* dominance. -/
abbrev CostVector := Axis → ℕ

/-! ## Provenance: a coordinate is a count that was obtained, not a number typed in -/

/-- [definition] How one coordinate was obtained. A `CostReceipt` cannot be formed without one of
these per coordinate; that is what makes it a receipt rather than a tuple of numbers. -/
inductive Provenance
  | /-- Counted directly off the presented data by the named instrument. -/
    measured (instrument : String)
  | /-- Computed from measured counts by the named rule. -/
    derived (rule : String)
  | /-- Supplied by the named exterior party. Not a measurement; carried, not trusted. -/
    declared (declarer : String)
  deriving DecidableEq, Repr

/-- [definition] A coordinate is **accounted** when it was measured or derived from measurements.
A declared coordinate is carried, and is not accounted. -/
def Provenance.Accounted : Provenance → Prop
  | .measured _ => True
  | .derived _ => True
  | .declared _ => False

/-- [definition] One coordinate: an exact natural count together with the provenance that produced
it. Rust counterpart: `presentation_cost.rs::Counted`. -/
structure Counted where
  /-- The exact count. -/
  count : ℕ
  /-- Where the count came from. -/
  provenance : Provenance
  deriving DecidableEq, Repr

/-! ## The receipt -/

/-- [definition] A **cost receipt** for one presentation of one object at one receiver. Five exact
coordinates, each with its provenance. This is not a score: `Weighting.objective` is the score, and
it is a receiver reading *of* this receipt.

Rust counterpart: `presentation_cost.rs::CostReceipt`. -/
structure CostReceipt where
  /-- Octets occupied. -/
  bytes : Counted
  /-- Steps to decode. -/
  decodeWork : Counted
  /-- Steps to re-present after one admitted change. -/
  updateWork : Counted
  /-- Steps to verify the presentation decodes to the object. -/
  certificateWork : Counted
  /-- Code size of what the presentation does not carry. -/
  residual : Counted
  deriving DecidableEq, Repr

namespace CostReceipt

/-- [definition] The coordinate carried at one axis. -/
def counted (R : CostReceipt) : Axis → Counted
  | .bytes => R.bytes
  | .decodeWork => R.decodeWork
  | .updateWork => R.updateWork
  | .certificateWork => R.certificateWork
  | .residual => R.residual

/-- [definition] The exact cost vector of a receipt: its counts, with the provenance forgotten.
Forgetting the provenance is exactly what makes dominance a partial order rather than an equality;
`dominates_antisymm_fails_on_receipts` is where that shows. -/
def vector (R : CostReceipt) : CostVector := fun ax => (R.counted ax).count

/-- [definition] Every coordinate was measured or derived. -/
def Accounted (R : CostReceipt) : Prop := ∀ ax, (R.counted ax).provenance.Accounted

/-- [definition] **Serial composition of receipts.** Coordinatewise addition, with every coordinate
marked derived and naming the law that licenses it. The law is
`Foundation/ReceiverCodeCost.lean`'s `serial_boundary_balance`, instantiated at
`serial_receipt_balance` below; it is cited, not re-proved.

Rust counterpart: `presentation_cost.rs::CostReceipt::compose`. -/
def compose (a b : CostReceipt) : CostReceipt :=
  let rule : Provenance :=
    .derived "serial composition, ReceiverCodeCost.serial_boundary_balance"
  { bytes := ⟨a.bytes.count + b.bytes.count, rule⟩
    decodeWork := ⟨a.decodeWork.count + b.decodeWork.count, rule⟩
    updateWork := ⟨a.updateWork.count + b.updateWork.count, rule⟩
    certificateWork := ⟨a.certificateWork.count + b.certificateWork.count, rule⟩
    residual := ⟨a.residual.count + b.residual.count, rule⟩ }

/-- [proved-derived; formal-checked] Composition adds coordinatewise. -/
@[simp] theorem compose_vector (a b : CostReceipt) (ax : Axis) :
    (a.compose b).vector ax = a.vector ax + b.vector ax := by
  cases ax <;> rfl

/-- [proved-derived; formal-checked] A composed receipt is accounted whatever its inputs were: the
composition step itself is derived, and it says so. -/
theorem compose_accounted (a b : CostReceipt) : (a.compose b).Accounted := by
  intro ax; cases ax <;> exact trivial

/-- [proved-derived; formal-checked] Composition is commutative and associative on the cost vector.
-/
theorem compose_vector_comm (a b : CostReceipt) : (a.compose b).vector = (b.compose a).vector := by
  funext ax; simp [Nat.add_comm]

theorem compose_vector_assoc (a b c : CostReceipt) :
    ((a.compose b).compose c).vector = (a.compose (b.compose c)).vector := by
  funext ax; simp [Nat.add_assoc]

end CostReceipt

/-! ### The additivity law is cited, never rebuilt -/

/-- [proved-derived; formal-checked] **Receipts compose through the owner of additivity.** Two
presentations of one continuing object, the first taking chart `i` to chart `m` and the second `m`
to `j`, each with a declared reading measured against the receiver's endpoint potential `φ`. Their
declared readings add, the middle potential cancels at the joined boundary, and what is left is
exactly `CostReceipt.compose` on the axis in question.

The proof is `Foundation/ReceiverCodeCost.lean`'s `serial_boundary_balance` instantiated at a
one-occurrence holon over the chart type; the cancellation comes from that theorem's stored
`Holon.Interaction`, not from anything proved here. -/
theorem serial_receipt_balance {Chart : Type u} (ax : Axis) (φ : Chart → ℝ)
    (a b : CostReceipt) (i m j : Chart) (declaredA declaredB residualA residualB : ℝ)
    (hA : declaredA = (a.vector ax : ℝ) + φ i - φ m + residualA)
    (hB : declaredB = (b.vector ax : ℝ) + φ m - φ j + residualB) :
    declaredA + declaredB
      = (((a.compose b).vector ax : ℕ) : ℝ) + φ i - φ j + (residualA + residualB) := by
  classical
  let left : Holon Chart Chart ℝ :=
    { Occurrence := Unit
      source := fun _ => i
      target := fun _ => m
      receive := fun _ => declaredA }
  let right : Holon Chart Chart ℝ :=
    { Occurrence := Unit
      source := fun _ => m
      target := fun _ => j
      receive := fun _ => declaredB }
  have joined : Holon.Interaction left right := ⟨(), (), rfl⟩
  have balance := ReceiverCodeCost.serial_boundary_balance left right 1
    (fun _ => (a.vector ax : ℝ)) (fun _ => (b.vector ax : ℝ)) φ φ φ
    (fun _ => residualA) (fun _ => residualB)
    (fun _ => by simpa [left, one_mul] using hA)
    (fun _ => by simpa [right, one_mul] using hB) joined
  simp only [left, right, one_mul] at balance
  rw [CostReceipt.compose_vector]
  push_cast
  linarith [balance]

/-! ## Dominance is the product partial order -/

/-- [definition] `Dominates a b`: the presentation with receipt `a` costs no more than the one with
receipt `b` on **every** axis. This is `Pi.partialOrder` on `CostVector` and nothing else. -/
def Dominates (a b : CostReceipt) : Prop := a.vector ≤ b.vector

/-- [definition] Strict dominance: no more on every axis and strictly less somewhere. -/
def StrictlyDominates (a b : CostReceipt) : Prop := a.vector < b.vector

/-- [proved-derived; formal-checked] Dominance is reflexive. -/
theorem dominates_refl (a : CostReceipt) : Dominates a a := le_refl _

/-- [proved-derived; formal-checked] Dominance is transitive. -/
theorem dominates_trans {a b c : CostReceipt} (hab : Dominates a b) (hbc : Dominates b c) :
    Dominates a c := le_trans hab hbc

/-- [proved-derived; formal-checked] **Dominance is antisymmetric on the cost vector, and on the
cost vector only.** Two receipts that dominate each other carry the same counts; they need not be
the same receipt, because provenance is not ordered and is not forgotten. This is the formal sense
in which a cost is a receipt and not an identity. -/
theorem dominates_antisymm_vector {a b : CostReceipt} (hab : Dominates a b) (hba : Dominates b a) :
    a.vector = b.vector := le_antisymm hab hba

/-- [proved-derived; formal-checked] Dominance *is* the product partial order. -/
theorem dominates_iff_vector_le (a b : CostReceipt) : Dominates a b ↔ a.vector ≤ b.vector := Iff.rfl

/-- [proved-derived; formal-checked] Strict dominance is "no worse everywhere and strictly better
somewhere". -/
theorem strictlyDominates_iff (a b : CostReceipt) :
    StrictlyDominates a b ↔ Dominates a b ∧ ∃ ax, a.vector ax < b.vector ax :=
  Pi.lt_def

/-- [proved-derived; formal-checked] Strict dominance is irreflexive. -/
theorem not_strictlyDominates_self (a : CostReceipt) : ¬ StrictlyDominates a a := lt_irrefl _

/-- [proved-derived; formal-checked] Strict dominance is transitive. -/
theorem strictlyDominates_trans {a b c : CostReceipt}
    (hab : StrictlyDominates a b) (hbc : StrictlyDominates b c) : StrictlyDominates a c :=
  lt_trans hab hbc

/-- [counterexample; formal-checked] Antisymmetry does **not** lift from the cost vector to the
receipt. A measured 12 and a supplier's declared 12 are one cost vector and two receipts; each
dominates the other and they are distinct. -/
theorem dominates_antisymm_fails_on_receipts :
    ∃ a b : CostReceipt, Dominates a b ∧ Dominates b a ∧ a ≠ b := by
  classical
  refine ⟨⟨⟨12, .measured "wc -c"⟩, ⟨0, .measured "wc -c"⟩, ⟨0, .measured "wc -c"⟩,
            ⟨0, .measured "wc -c"⟩, ⟨0, .measured "wc -c"⟩⟩,
          ⟨⟨12, .declared "vendor datasheet"⟩, ⟨0, .measured "wc -c"⟩, ⟨0, .measured "wc -c"⟩,
            ⟨0, .measured "wc -c"⟩, ⟨0, .measured "wc -c"⟩⟩, ?_, ?_, ?_⟩
  · intro ax; cases ax <;> exact le_refl _
  · intro ax; cases ax <;> exact le_refl _
  · decide

/-! ## The frontier -/

section Frontier

variable {ι : Type u}

/-- [definition] A **Pareto point**: a labelled presentation carrying its receipt. The label is what
the receipt is *of*; the receipt never replaces it.

Rust counterpart: `presentation_cost.rs::ParetoPoint`. -/
structure ParetoPoint (Label : Type u) where
  /-- Which presentation this is. -/
  label : Label
  /-- What it cost. -/
  receipt : CostReceipt

/-- [definition] `i` is a **frontier point** of the finite family `S` under the cost reading `w`: it
is in the family and nothing in the family strictly dominates it. The frontier is the antichain of
nondominated points. -/
def IsFrontierPoint (S : Finset ι) (w : ι → CostVector) (i : ι) : Prop :=
  i ∈ S ∧ ∀ j ∈ S, ¬ w j < w i

/-- [definition] The frontier as a `Finset`, mirroring `presentation_cost.rs::pareto_frontier`. -/
noncomputable def frontier (S : Finset ι) (w : ι → CostVector) : Finset ι := by
  classical
  exact S.filter (fun i => ∀ j ∈ S, ¬ w j < w i)

theorem mem_frontier {S : Finset ι} {w : ι → CostVector} {i : ι} :
    i ∈ frontier S w ↔ IsFrontierPoint S w i := by
  classical
  simp [frontier, IsFrontierPoint, Finset.mem_filter]

/-- [definition] The total of the coordinates. It is used **only** as a well-founded measure in the
existence proof below. It is not a cost and no theorem here reads it as one. -/
def total (v : CostVector) : ℕ := ∑ ax, v ax

/-- [proved-derived; formal-checked] Strict dominance strictly decreases the coordinate total, so
the dominance order on a finite family is well founded. -/
theorem total_lt_of_lt {u v : CostVector} (h : u < v) : total u < total v := by
  obtain ⟨hle, ax, hax⟩ := Pi.lt_def.mp h
  exact Finset.sum_lt_sum (fun i _ => hle i) ⟨ax, Finset.mem_univ ax, hax⟩

/-- [proved-derived; formal-checked] **Every point of a finite family is dominated by a frontier
point.** No presentation is left without a frontier witness at least as cheap on every axis. -/
theorem exists_frontier_dominating (S : Finset ι) (w : ι → CostVector) {i : ι} (hi : i ∈ S) :
    ∃ f, IsFrontierPoint S w f ∧ w f ≤ w i := by
  classical
  obtain ⟨f, hfD, hfmin⟩ :=
    (S.filter (fun j => w j ≤ w i)).exists_min_image (fun j => total (w j))
      ⟨i, by simp [Finset.mem_filter, hi]⟩
  obtain ⟨hfS, hfle⟩ := Finset.mem_filter.mp hfD
  refine ⟨f, ⟨hfS, ?_⟩, hfle⟩
  intro j hj hlt
  have hjD : j ∈ S.filter (fun j => w j ≤ w i) :=
    Finset.mem_filter.mpr ⟨hj, le_trans (le_of_lt hlt) hfle⟩
  exact absurd (hfmin j hjD) (not_le.mpr (total_lt_of_lt hlt))

/-- [proved-derived; formal-checked] **The frontier of a finite nonempty family is nonempty.** -/
theorem frontier_nonempty (S : Finset ι) (w : ι → CostVector) (hS : S.Nonempty) :
    ∃ f, IsFrontierPoint S w f := by
  obtain ⟨i, hi⟩ := hS
  obtain ⟨f, hf, -⟩ := exists_frontier_dominating S w hi
  exact ⟨f, hf⟩

/-- [proved-derived; formal-checked] The frontier is an antichain: no frontier point strictly
dominates another. -/
theorem frontier_isAntichain {S : Finset ι} {w : ι → CostVector} {i j : ι}
    (hi : IsFrontierPoint S w i) (hj : IsFrontierPoint S w j) : ¬ w i < w j :=
  hj.2 i hi.1

end Frontier

/-! ## The scalar objective is one receiver of the receipt -/

/-- [definition] A **weighting** `q`: a declared nonnegative weight per axis. This is the receiver,
and `objective` is its reading.

Rust counterpart: `presentation_cost.rs::Weighting`, whose constructor refuses a negative weight. -/
structure Weighting where
  /-- The weight at each axis. -/
  weight : Axis → ℚ
  /-- No weight is negative. -/
  nonneg : ∀ ax, 0 ≤ weight ax

namespace Weighting

/-- [definition] `C(P;q) = a*bytes + b*decodeWork + c*updateWork + d*certificateWork + e*residual`.
One number: a receiver reading of the receipt, never the identity of the presentation. -/
def objective (q : Weighting) (v : CostVector) : ℚ := ∑ ax, q.weight ax * (v ax : ℚ)

/-- [definition] A weighting is **strictly positive** when every axis carries weight. -/
def Positive (q : Weighting) : Prop := ∀ ax, 0 < q.weight ax

/-- [proved-derived; formal-checked] A strictly positive weighting is strictly monotone for
dominance: a strictly dominated presentation scores strictly worse. -/
theorem objective_strictMono {q : Weighting} (hq : q.Positive) {u v : CostVector} (h : u < v) :
    q.objective u < q.objective v := by
  obtain ⟨hle, ax, hax⟩ := Pi.lt_def.mp h
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨ax, Finset.mem_univ ax, ?_⟩
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle i) (q.nonneg i)
  · exact mul_lt_mul_of_pos_left (by exact_mod_cast hax) (hq ax)

/-- [proved-derived; formal-checked] Any nonnegative weighting is monotone for dominance. -/
theorem objective_mono (q : Weighting) {u v : CostVector} (h : u ≤ v) :
    q.objective u ≤ q.objective v :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by exact_mod_cast h i) (q.nonneg i)

/-- [proved-derived; formal-checked] The objective written out on the five axes. -/
theorem objective_eq (q : Weighting) (v : CostVector) :
    q.objective v = q.weight .bytes * (v .bytes : ℚ)
      + q.weight .decodeWork * (v .decodeWork : ℚ)
      + q.weight .updateWork * (v .updateWork : ℚ)
      + q.weight .certificateWork * (v .certificateWork : ℚ)
      + q.weight .residual * (v .residual : ℚ) :=
  sum_axis _

end Weighting

/-- [proved-derived; formal-checked] **Every strictly positive weighting's minimizer lies on the
frontier.** A scalar optimum is never *outside* the frontier: the objective is a sound selector. -/
theorem minimizer_isFrontierPoint {ι : Type u} {S : Finset ι} {w : ι → CostVector} {q : Weighting}
    (hq : q.Positive) {i : ι} (hi : i ∈ S)
    (hmin : ∀ j ∈ S, q.objective (w i) ≤ q.objective (w j)) :
    IsFrontierPoint S w i :=
  ⟨hi, fun j hj hlt => absurd (hmin j hj) (not_le.mpr (Weighting.objective_strictMono hq hlt))⟩

/-! ### The converse fails: a frontier point that no weighting selects

[counterexample] Three presentations of one object, differing only in `bytes` and `decodeWork`: a
byte-free presentation that is expensive to decode, a decode-free presentation that is expensive in
bytes, and a balanced one **strictly above the chord** between them (`6 + 6 > 10`). All three are
nondominated, so all three are on the frontier. No nonnegative weighting that puts weight on either
varying axis selects the balanced one. The objective sees only the lower convex hull; the frontier
is the antichain, and the two differ. -/

/-- [definition] A synthetic receipt used only as a formal witness. Every coordinate is `declared`,
not measured, and says so. -/
def witnessReceipt (name : String) (b d u c r : ℕ) : CostReceipt where
  bytes := ⟨b, .declared ("formal witness " ++ name)⟩
  decodeWork := ⟨d, .declared ("formal witness " ++ name)⟩
  updateWork := ⟨u, .declared ("formal witness " ++ name)⟩
  certificateWork := ⟨c, .declared ("formal witness " ++ name)⟩
  residual := ⟨r, .declared ("formal witness " ++ name)⟩

@[simp] theorem witnessReceipt_vector (name : String) (b d u c r : ℕ) (ax : Axis) :
    (witnessReceipt name b d u c r).vector ax =
      match ax with
      | .bytes => b
      | .decodeWork => d
      | .updateWork => u
      | .certificateWork => c
      | .residual => r := by
  cases ax <;> rfl

/-- [definition] The byte-free, decode-expensive corner. -/
def chordLeft : CostReceipt := witnessReceipt "chordLeft" 0 10 0 0 0
/-- [definition] The decode-free, byte-expensive corner. -/
def chordRight : CostReceipt := witnessReceipt "chordRight" 10 0 0 0 0
/-- [definition] The balanced presentation strictly above the chord. -/
def unsupported : CostReceipt := witnessReceipt "unsupported" 6 6 0 0 0

/-- [definition] The three-presentation family. -/
inductive Chord
  | /-- The byte-free corner. -/ left
  | /-- The decode-free corner. -/ right
  | /-- The balanced presentation above the chord. -/ balanced
  deriving DecidableEq, Repr

namespace Chord

instance : Fintype Chord where
  elems := {Chord.left, Chord.right, Chord.balanced}
  complete := fun x => by cases x <;> decide

end Chord

/-- [definition] Its cost reading. -/
def chordCost : Chord → CostVector
  | .left => chordLeft.vector
  | .right => chordRight.vector
  | .balanced => unsupported.vector

/-- [definition] The family itself. -/
def chordFamily : Finset Chord := Finset.univ

/-- [proved-derived; formal-checked] All three are on the frontier: the family is an antichain of
three, and in particular the balanced presentation is a frontier point. -/
theorem chordFamily_frontier_is_everything (i : Chord) :
    IsFrontierPoint chordFamily chordCost i := by
  refine ⟨Finset.mem_univ _, ?_⟩
  intro j _ hlt
  have hle := hlt.le
  cases i <;> cases j <;>
    first
      | exact absurd hlt (lt_irrefl _)
      | exact absurd (hle Axis.bytes) (by decide)
      | exact absurd (hle Axis.decodeWork) (by decide)

/-- [proved-derived; formal-checked] In particular the balanced presentation is on the frontier. -/
theorem unsupported_isFrontierPoint : IsFrontierPoint chordFamily chordCost .balanced :=
  chordFamily_frontier_is_everything _

/-- [counterexample; formal-checked] **No weighting that weighs either varying axis selects the
balanced presentation.** For every nonnegative `q` with positive weight on `bytes` or on
`decodeWork`, one of the two corners scores strictly lower. In particular no *strictly positive*
weighting selects it, although it is a frontier point: the converse of
`minimizer_isFrontierPoint` is false, and a scalar score cannot stand in for the frontier. -/
theorem unsupported_not_minimizer (q : Weighting)
    (h : 0 < q.weight .bytes ∨ 0 < q.weight .decodeWork) :
    ∃ j ∈ chordFamily, q.objective (chordCost j) < q.objective (chordCost .balanced) := by
  have hb0 : (0 : ℚ) ≤ q.weight .bytes := q.nonneg _
  have hd0 : (0 : ℚ) ≤ q.weight .decodeWork := q.nonneg _
  have hL : q.objective (chordCost .left) = 10 * q.weight .decodeWork := by
    rw [Weighting.objective_eq]; simp [chordCost, chordLeft]; ring
  have hR : q.objective (chordCost .right) = 10 * q.weight .bytes := by
    rw [Weighting.objective_eq]; simp [chordCost, chordRight]; ring
  have hB : q.objective (chordCost .balanced)
      = 6 * q.weight .bytes + 6 * q.weight .decodeWork := by
    rw [Weighting.objective_eq]; simp [chordCost, unsupported]; ring
  rcases le_total (q.weight .bytes) (q.weight .decodeWork) with hle | hle
  · refine ⟨.right, Finset.mem_univ _, ?_⟩
    have hdpos : 0 < q.weight .decodeWork := by rcases h with h | h <;> linarith
    rw [hR, hB]; linarith
  · refine ⟨.left, Finset.mem_univ _, ?_⟩
    have hbpos : 0 < q.weight .bytes := by rcases h with h | h <;> linarith
    rw [hL, hB]; linarith

/-- [proved-derived; formal-checked] **The frontier has no least point.** No member of this
frontier is at most every other on every axis, so "the minimal presentation" does not name anything
here. This is the statement that replaces a Kolmogorov-minimal encoding, which is incomputable and
is not claimed anywhere in this file. -/
theorem frontier_has_no_least_point : ¬ ∃ i : Chord, ∀ j : Chord, chordCost i ≤ chordCost j := by
  rintro ⟨i, hi⟩
  cases i
  · exact absurd (hi Chord.right Axis.decodeWork) (by decide)
  · exact absurd (hi Chord.left Axis.bytes) (by decide)
  · exact absurd (hi Chord.left Axis.bytes) (by decide)

/-! ## Monotone reparameterization -/

/-- [definition] A **reparameterization**: a strictly monotone change of unit on each coordinate,
independently. Reporting decode work in operation-pairs rather than operations, or bytes after a
fixed framing, is such a change. -/
structure Reparameterization where
  /-- The unit change at each axis. -/
  map : Axis → ℕ → ℕ
  /-- Each one is strictly monotone: it reorders nothing. -/
  strictMono : ∀ ax, StrictMono (map ax)

namespace Reparameterization

/-- [definition] Its action on a cost vector. -/
def onVector (φ : Reparameterization) (v : CostVector) : CostVector := fun ax => φ.map ax (v ax)

/-- [proved-derived; formal-checked] A reparameterization preserves and reflects dominance. -/
theorem le_iff (φ : Reparameterization) (u v : CostVector) :
    φ.onVector u ≤ φ.onVector v ↔ u ≤ v := by
  constructor
  · intro h ax; exact (φ.strictMono ax).le_iff_le.mp (h ax)
  · intro h ax; exact (φ.strictMono ax).le_iff_le.mpr (h ax)

/-- [proved-derived; formal-checked] And strict dominance. -/
theorem lt_iff (φ : Reparameterization) (u v : CostVector) :
    φ.onVector u < φ.onVector v ↔ u < v := by
  simp only [lt_iff_le_not_ge, φ.le_iff]

end Reparameterization

/-- [proved-derived; formal-checked] **The frontier is invariant under monotone reparameterization
of each coordinate.** It depends only on the order of each axis, not on the unit it is reported in.
-/
theorem frontier_reparameterization_invariant {ι : Type u} (φ : Reparameterization) (S : Finset ι)
    (w : ι → CostVector) (i : ι) :
    IsFrontierPoint S (fun j => φ.onVector (w j)) i ↔ IsFrontierPoint S w i := by
  constructor
  · rintro ⟨hi, h⟩
    exact ⟨hi, fun j hj hlt => h j hj ((φ.lt_iff (w j) (w i)).mpr hlt)⟩
  · rintro ⟨hi, h⟩
    exact ⟨hi, fun j hj hlt => h j hj ((φ.lt_iff (w j) (w i)).mp hlt)⟩

/-- [definition] Reporting decode work in operation-pairs: `n ↦ n * n` on that axis only. -/
def squareDecode : Reparameterization where
  map ax := match ax with
    | .decodeWork => fun n => n * n
    | _ => id
  strictMono ax := by
    cases ax
    · exact strictMono_id
    · exact fun a b hab => Nat.mul_self_lt_mul_self hab
    · exact strictMono_id
    · exact strictMono_id
    · exact strictMono_id

/-- [definition] The all-ones weighting. -/
def oneWeighting : Weighting := ⟨fun _ => 1, fun _ => zero_le_one⟩

/-- [definition] Two incomparable presentations, the second costlier under the all-ones weighting.
-/
def flatA : CostReceipt := witnessReceipt "flatA" 0 3 0 0 0
/-- [definition] The other one. -/
def flatB : CostReceipt := witnessReceipt "flatB" 2 2 0 0 0

/-- [counterexample; formal-checked] **The scalar minimizer is not reparameterization invariant.**
Under the all-ones weighting `flatA` scores lower than `flatB`; after reporting decode work in
operation-pairs — a strictly monotone change of unit on one axis, which by
`frontier_reparameterization_invariant` leaves the frontier exactly as it was — `flatB` scores
lower. The two presentations are incomparable throughout, so the flip is entirely an artefact of
the scalar reading. -/
theorem scalar_minimizer_not_reparameterization_invariant :
    oneWeighting.objective flatA.vector < oneWeighting.objective flatB.vector ∧
      oneWeighting.objective (squareDecode.onVector flatB.vector)
        < oneWeighting.objective (squareDecode.onVector flatA.vector) := by
  constructor
  · rw [Weighting.objective_eq, Weighting.objective_eq]
    simp [oneWeighting, flatA, flatB]
    norm_num
  · rw [Weighting.objective_eq, Weighting.objective_eq]
    simp [oneWeighting, flatA, flatB, Reparameterization.onVector, squareDecode]
    norm_num

/-- [proved-derived; formal-checked] And the two presentations really are incomparable, before and
after: the frontier is both of them in both units. -/
theorem flat_pair_incomparable :
    ¬ flatA.vector ≤ flatB.vector ∧ ¬ flatB.vector ≤ flatA.vector ∧
      ¬ squareDecode.onVector flatA.vector ≤ squareDecode.onVector flatB.vector ∧
      ¬ squareDecode.onVector flatB.vector ≤ squareDecode.onVector flatA.vector := by
  refine ⟨fun h => absurd (h Axis.decodeWork) (by decide),
          fun h => absurd (h Axis.bytes) (by decide), fun h => ?_, fun h => ?_⟩
  · exact absurd ((squareDecode.le_iff _ _).mp h Axis.decodeWork) (by decide)
  · exact absurd ((squareDecode.le_iff _ _).mp h Axis.bytes) (by decide)

/-! ## The residual coordinate behaves as the carrier's residual does -/

/-- [definition] The exact code size of a residual fibre of `n` values: `⌈log₂ n⌉`. This is the
coordinate `Axis.residual` carries. It is a count of bits, not an entropy and not a probability. -/
def codeBits (n : ℕ) : ℕ := Nat.clog 2 n

/-- [proved-derived; formal-checked] A residual that carries nothing owes no bits. -/
@[simp] theorem codeBits_one : codeBits 1 = 0 := by simp [codeBits]

/-- [proved-derived; formal-checked] Code size is subadditive over a product of residual fibres. -/
theorem codeBits_mul_le (a b : ℕ) : codeBits (a * b) ≤ codeBits a + codeBits b := by
  have htwo : (1 : ℕ) < 2 := by norm_num
  rw [codeBits, Nat.clog_le_iff_le_pow htwo, pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog htwo a) (Nat.le_pow_clog htwo b)

/-- [proved-derived; formal-checked] **Composing transitions composes residuals, and the residual
coordinate is subadditive.** `Foundation/ContinuingTower.lean`'s `Transition.comp` makes the
composite residual the *pair* of component residuals, so the residual fibre multiplies; its code
size therefore adds at worst. The pairing law is cited, not rebuilt. -/
theorem codeBits_residual_comp_le {Source : Type u} {Middle : Type v} {Target : Type w}
    (second : Transition Middle Target) (first : Transition Source Middle) :
    codeBits (Nat.card (Transition.comp second first).Residual)
      ≤ codeBits (Nat.card second.Residual) + codeBits (Nat.card first.Residual) := by
  have hcard : Nat.card (Transition.comp second first).Residual
      = Nat.card second.Residual * Nat.card first.Residual :=
    Nat.card_prod _ _
  rw [hcard]
  exact codeBits_mul_le _ _

/-- [definition] A transition that drops a declared factor: the residual is exactly that factor. -/
def dropFactor (m n : ℕ) : Transition (Fin m × Fin n) (Fin m) where
  Residual := Fin n
  apply x := x.1
  residual x := x.2
  reopen t r := (t, r)
  reopen_apply _ := rfl

/-- [definition] A transition that drops everything it is given. -/
def dropAll (m : ℕ) : Transition (Fin m) PUnit where
  Residual := Fin m
  apply _ := PUnit.unit
  residual x := x
  reopen _ r := r
  reopen_apply _ := rfl

/-- [counterexample; formal-checked] **The residual coordinate is strictly subadditive.** Composing
a transition with a five-valued residual after one with a three-valued residual gives a fifteen-
valued residual, which codes in four bits, while the two components code in three and two. The
composed *receipt* is therefore an honest upper bound and not the composite's true residual
coordinate — the extra bit is the joint constraint the pair carries and the two singles do not. -/
theorem codeBits_residual_comp_lt_witness :
    codeBits (Nat.card (Transition.comp (dropAll 5) (dropFactor 5 3)).Residual)
      < codeBits (Nat.card (dropAll 5).Residual) + codeBits (Nat.card (dropFactor 5 3).Residual) := by
  have htwo : (1 : ℕ) < 2 := by norm_num
  have hcard : Nat.card (Transition.comp (dropAll 5) (dropFactor 5 3)).Residual = 15 := by
    show Nat.card (Fin 5 × Fin 3) = 15
    simp [Nat.card_eq_fintype_card]
  have hsecond : Nat.card (dropAll 5).Residual = 5 := by
    show Nat.card (Fin 5) = 5
    simp [Nat.card_eq_fintype_card]
  have hfirst : Nat.card (dropFactor 5 3).Residual = 3 := by
    show Nat.card (Fin 3) = 3
    simp [Nat.card_eq_fintype_card]
  rw [hcard, hsecond, hfirst]
  have h15 : codeBits 15 ≤ 4 := (Nat.clog_le_iff_le_pow htwo).mpr (by norm_num)
  have h5 : 3 ≤ codeBits 5 := by
    unfold codeBits
    by_contra hcon
    push Not at hcon
    have hle : Nat.clog 2 5 ≤ 2 := by omega
    have hpow := (Nat.clog_le_iff_le_pow htwo).mp hle
    norm_num at hpow
  have h3 : 2 ≤ codeBits 3 := by
    unfold codeBits
    by_contra hcon
    push Not at hcon
    have hle : Nat.clog 2 3 ≤ 1 := by omega
    have hpow := (Nat.clog_le_iff_le_pow htwo).mp hle
    norm_num at hpow
  omega

/-- [proved-derived; formal-checked] An invertible chart map owes a zero residual coordinate:
`Transition.ofEquiv`'s residual is `PUnit`, which codes in no bits. `Transition`'s own
`ofEquiv_residual_subsingleton` is the owner of that fact; this only reads it off in the
coordinate. -/
theorem codeBits_residual_ofEquiv {Source : Type u} {Target : Type v} (e : Source ≃ Target) :
    codeBits (Nat.card (Transition.ofEquiv e).Residual) = 0 := by
  show codeBits (Nat.card PUnit) = 0
  simp [Nat.card_eq_fintype_card]

/-! ## `Migration.CostBoundedByRefinementRoute`, discharged and sharpened

[definition] `Foundation/ContinuingTower.lean:1864-1870` states the comparison between a migration
and the "refine to a common chart, then restrict back" route over an abstract ordered cost `W`, and
leaves it **open**, taking both cost functions as caller-supplied arguments. Three things are true
of it and are proved here.

1. `costBoundedByRefinementRoute_is_caller_decided` — **as stated it carries no content.** For one
   fixed migration and one fixed migration cost, the caller can make the statement true or false by
   choosing the route cost, because the route cost is an arbitrary supplied function. Its docstring
   says this; here it is a theorem.
2. `costBoundedByRefinementRoute_of_route` — **it is true, over the concrete `CostVector`, for
   every `CostedTower` and every migration that factors through refinement.** A `CostedTower`
   declares a receipt per restriction and one law, `route_dominates`: presenting the composite
   restriction directly never costs more, on any axis, than running the two steps. The theorem is
   that law and nothing else, so what makes it a statement rather than a hypothesis nobody meets is
   that instances exist. Two are constructed here — `padicCostedTower`, the `ZMod (p ^ n)` tower
   carrying the receipts its own restrictions determine, and `unitCostedTower`, the one-point tower
   — and their `route_dominates` is *derived* (`padicStepReceipt_route`,
   `unitCostedTower_route_equality`), not assumed. `costBoundedByRefinementRoute_padic` is the
   comparison discharged at `padicCostedTower` and `padicHalfMigration`, with no caller-supplied
   cost on either side.
3. `swapMigration_route_isEmpty` — **where the migration connects incomparable charts there is no
   route at all**, so nothing is being compared. This is `twoCharts_no_common_refinement`, cited.
4. `no_costedTower_with_squaredGapReceipt` — **`route_dominates` is a real condition.** The
   squared-gap receipt assignment `squaredGapReceipt` meets everything a `CostedTower` asks except
   that law, and `squaredGapReceipt_route_fails` refutes it at charts `0 ≤ 1 ≤ 2`. The field is
   therefore neither vacuous nor automatic.

Which law discharges `route_dominates` is axis-dependent, and this file says so where it proves it.
`serial_receipt_balance` supplies the right-hand *total*: the two declared readings add and the
middle chart's potential cancels, so the two-step cost is `CostReceipt.compose`
(`padicCostedTower_serial_balance`). Comparing the direct receipt against that total is a further
fact, proved axis by axis: exact additivity of the digit gap on `bytes`, `decodeWork` and
`updateWork` (`padicCostedTower_route_equality_on_step_axes`); one saved header on
`certificateWork`, where the inequality is strict at every triple
(`padicCostedTower_route_strict_at_certificateWork`); and on `residual` **not**
`serial_boundary_balance` at all but `codeBits` subadditivity — code sizes do not add — which at
these transitions is `codeBits_residual_comp_le` applied to the tower's own restriction transitions
(`padicCostedTower_residual_eq_comp`, `padicCostedTower_route_residual_is_codeBits_comp`), strict at
`padicCostedTower_route_strict_at_residual`.

The corrected form of the open item is therefore: the comparison is a *theorem* about a
`CostedTower` and a `Migration.FactorsThroughRefinement` — inhabited by `padicCostedTower` and
`unitCostedTower`, not met by `squaredGapReceipt` — and a *non-statement* about any other
migration. -/

/-- [definition] A **refinement route** from chart `source` to chart `target`: a common refinement
of both. Lifting to it is not a tower operation — that is what a retained residual is for — and
restricting back down is. Where no such chart exists there is no route and no comparison. -/
structure RefinementRoute {Index : Type u} [Preorder Index] (source target : Index) where
  /-- The chart that refines both. -/
  common : Index
  /-- It refines the source chart. -/
  sourceRefines : source ≤ common
  /-- It refines the target chart. -/
  targetRefines : target ≤ common

/-- [definition] A tower whose restrictions carry receipts, together with the one law that makes the
receipts a cost enrichment rather than a decoration: **the direct restriction never costs more than
the two-step route.** `serial_receipt_balance` supplies the right-hand side — the two-step total is
`CostReceipt.compose`, because the two declared readings add and the middle chart's potential
cancels — and `route_dominates` is the further claim that a direct presentation, which may share
work between the steps, never needs more of any axis than that total. It is a **condition on the
receipts and not a consequence of `serial_boundary_balance`**: `no_costedTower_with_squaredGapReceipt`
exhibits receipts that fail it. Two towers that satisfy it are built below, `padicCostedTower` and
`unitCostedTower`; for the first, the law is derived axis by axis in `padicStepReceipt_route`. -/
structure CostedTower (Index : Type u) [Preorder Index] extends Tower.{u, v} Index where
  /-- The receipt of restricting from the finer chart to the coarser one. -/
  receipt : ∀ {i j : Index}, i ≤ j → CostReceipt
  /-- Serial subadditivity along a composed restriction. -/
  route_dominates : ∀ {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k),
    (receipt (le_trans hij hjk)).vector ≤ ((receipt hjk).compose (receipt hij)).vector

/-- [proved-derived; formal-checked] **The open comparison, discharged where it holds.** For a
migration of a costed tower into itself that factors through refinement, and any intermediate chart
supplied per target chart, the migration's own receipt is dominated by the refinement route's
composed receipt on every axis. The proof is the tower's `route_dominates` and nothing else, so the
theorem is exactly as strong as the supply of costed towers: `padicCostedTower` and
`unitCostedTower` below are two of them, `costBoundedByRefinementRoute_padic` is this theorem at the
first, and `no_costedTower_with_squaredGapReceipt` is a receipt assignment that is not one. -/
theorem costBoundedByRefinementRoute_of_route {Index : Type u} [Preorder Index]
    (C : CostedTower.{u, v} Index) (M : Migration C.toTower C.toTower)
    (hM : M.FactorsThroughRefinement) (mid : Index → Index)
    (hlow : ∀ j, j ≤ mid j) (hhigh : ∀ j, mid j ≤ M.index j) :
    Migration.CostBoundedByRefinementRoute (W := CostVector) M
      (fun j _ => (C.receipt (hM.refines j)).vector)
      (fun j _ => ((C.receipt (hhigh j)).compose (C.receipt (hlow j))).vector) :=
  fun j _ => C.route_dominates (hlow j) (hhigh j)

/-- [counterexample; formal-checked] **As originally stated the comparison is caller-decided.** One
migration, one migration cost, and two route costs: with one the statement holds, with the other it
fails. The route cost is an arbitrary supplied function, so the `Prop` records a choice of the
caller, not a property of the migration. -/
theorem costBoundedByRefinementRoute_is_caller_decided :
    ∃ (M : Migration (twoChartTower ℕ) (twoChartTower ℕ))
      (migrationCost : ∀ j : TwoCharts, (twoChartTower ℕ).Face (M.index j) → ℕ),
      (∃ routeCost, Migration.CostBoundedByRefinementRoute M migrationCost routeCost) ∧
        (∃ routeCost, ¬ Migration.CostBoundedByRefinementRoute M migrationCost routeCost) := by
  refine ⟨Migration.identity (twoChartTower ℕ), fun _ _ => 1,
    ⟨fun _ _ => 1, fun _ _ => le_refl _⟩, ⟨fun _ _ => 0, ?_⟩⟩
  intro hcon
  have face : (twoChartTower ℕ).Face
      ((Migration.identity (twoChartTower ℕ)).index TwoCharts.left) := (0 : ℕ)
  exact absurd (hcon TwoCharts.left face) (by norm_num)

/-- [proved-derived; formal-checked] **Where the migration connects incomparable charts there is no
route to compare with.** `swapMigration`'s two charts have no common refinement, so the refinement
route type is empty at every chart. `twoCharts_no_common_refinement` is cited; nothing is rebuilt.
-/
theorem swapMigration_route_isEmpty (X : Type v) (j : TwoCharts) :
    IsEmpty (RefinementRoute ((swapMigration X).index j) j) := by
  cases j with
  | left =>
    exact ⟨fun route =>
      twoCharts_no_common_refinement ⟨route.common, route.targetRefines, route.sourceRefines⟩⟩
  | right =>
    exact ⟨fun route =>
      twoCharts_no_common_refinement ⟨route.common, route.sourceRefines, route.targetRefines⟩⟩

/-- [proved-derived; formal-checked] By contrast a migration that factors through refinement has a
route at every chart: the refinement it factors through is a common refinement of both charts. -/
def refinementRoute_of_factorsThroughRefinement {Index : Type u} [Preorder Index]
    {T : Tower.{u, v} Index} {M : Migration T T} (hM : M.FactorsThroughRefinement) (j : Index) :
    RefinementRoute (M.index j) j where
  common := M.index j
  sourceRefines := le_refl _
  targetRefines := hM.refines j

/-! ### Two costed towers, and one receipt assignment that is not one

[definition] `CostedTower.route_dominates` is a **field**, so `costBoundedByRefinementRoute_of_route`
is worth exactly as much as the supply of towers that satisfy it. Three things are exhibited here so
that the hypothesis is known satisfiable, known derivable from stated receipts, and known not to be
automatic.

* `padicCostedTower` — the `ℤ/p^n` tower of `Foundation/ContinuingTower.lean` carrying the receipt
  its **own** restrictions determine: the gap `j - i` in base-`p` digits, and the code size of the
  digit block `padicRestrictTransition` retains. Its `route_dominates` is derived
  (`padicStepReceipt_route`), not assumed, and the derivation is different on different axes —
  see the next paragraph.
* `unitCostedTower` — the minimal instance: the one-point tower, whose restriction presents nothing
  and whose fibre is a single point, so every coordinate is zero and `route_dominates` holds with
  equality (`unitCostedTower_route_equality`).
* `squaredGapReceipt` — a receipt assignment for which `route_dominates` **fails**
  (`squaredGapReceipt_route_fails`), so that no `CostedTower` on any `ℕ`-indexed tower can carry it
  (`no_costedTower_with_squaredGapReceipt`). The field is a real condition: neither vacuous, since
  the two instances above satisfy it, nor automatic, since this assignment does not.

[definition] **Where the law is `serial_receipt_balance` and where it is not.** The two-step route's
total *is* `CostReceipt.compose`, and that is `serial_receipt_balance` — the two declared readings
add and the middle chart's potential cancels (`padicCostedTower_serial_balance`). What
`route_dominates` adds is the comparison of the direct receipt with that total, and its proof is
axis-dependent: on `bytes`, `decodeWork` and `updateWork` it is the exact additivity of the digit
gap (`padicCostedTower_route_equality_on_step_axes`); on `certificateWork` the direct presentation
is strictly cheaper by the one header it does not repeat
(`padicCostedTower_route_strict_at_certificateWork`); and on `residual` it is **not**
`serial_receipt_balance` at all but `codeBits` subadditivity — code sizes do not add — which at
these transitions is exactly `codeBits_residual_comp_le` applied to the tower's own restriction
transitions (`padicCostedTower_residual_eq_comp`,
`padicCostedTower_route_residual_is_codeBits_comp`), strictly so at
`padicCostedTower_route_strict_at_residual`. -/

/-- [definition] The octets one base-`p` digit occupies when it is written out: `⌈codeBits p / 8⌉`.
Exact natural division; no float and no logarithm participates. -/
def digitOctets (p : ℕ) : ℕ := (codeBits p + 7) / 8

/-- [definition] The receipt of one `p`-adic restriction across a gap of `d` charts — the
`ℤ/p^(i+d) → ℤ/p^i` restriction of `Foundation/ContinuingTower.lean::padicRestrictTransition`.

Every coordinate is read off that transition and nothing is supplied by a caller: the presentation
writes the `d` dropped digits (`bytes`), decodes and re-presents them one Horner step each
(`decodeWork`, `updateWork`), is verified by comparing the `d` digits after one header check
(`certificateWork`), and does not carry the digit block itself, whose fibre `ZMod (p ^ d)` has
exactly `p ^ d` elements (`residual`, through `codeBits`; `padicFibre_card` is the owner of the
count). -/
def padicStepReceipt (p d : ℕ) : CostReceipt where
  bytes := ⟨d * digitOctets p, .derived "one digit-octet per dropped base-p digit"⟩
  decodeWork := ⟨d, .derived "one Horner step per dropped digit"⟩
  updateWork := ⟨d, .derived "one digit rewritten per dropped digit"⟩
  certificateWork := ⟨d + 1,
    .derived "one digit compared per dropped digit, after one header check per presentation"⟩
  residual := ⟨codeBits (p ^ d),
    .derived "codeBits of Nat.card of padicRestrictTransition's residual ZMod (p ^ d)"⟩

@[simp] theorem padicStepReceipt_vector (p d : ℕ) (ax : Axis) :
    (padicStepReceipt p d).vector ax =
      match ax with
      | .bytes => d * digitOctets p
      | .decodeWork => d
      | .updateWork => d
      | .certificateWork => d + 1
      | .residual => codeBits (p ^ d) := by
  cases ax <;> rfl

/-- [proved-derived; formal-checked] **The step receipt is subadditive in the chart gap, axis by
axis.** Crossing `d₁ + d₂` charts directly never costs more than crossing `d₁` and then `d₂`. The
first three axes are exact additivity of the gap, `certificateWork` saves one header, and `residual`
is `codeBits_mul_le` on `p ^ d₁ * p ^ d₂`. -/
theorem padicStepReceipt_route (p d₁ d₂ : ℕ) :
    (padicStepReceipt p (d₁ + d₂)).vector ≤
      ((padicStepReceipt p d₁).compose (padicStepReceipt p d₂)).vector := by
  intro ax
  cases ax with
  | bytes =>
    show (d₁ + d₂) * digitOctets p ≤ d₁ * digitOctets p + d₂ * digitOctets p
    exact le_of_eq (Nat.add_mul _ _ _)
  | decodeWork =>
    show d₁ + d₂ ≤ d₁ + d₂
    exact le_refl _
  | updateWork =>
    show d₁ + d₂ ≤ d₁ + d₂
    exact le_refl _
  | certificateWork =>
    show d₁ + d₂ + 1 ≤ d₁ + 1 + (d₂ + 1)
    omega
  | residual =>
    show codeBits (p ^ (d₁ + d₂)) ≤ codeBits (p ^ d₁) + codeBits (p ^ d₂)
    rw [pow_add]
    exact codeBits_mul_le _ _

/-- [proved-derived; formal-checked] **A costed tower on a real tower.** The `ℤ/p^n` tower with the
receipt its own restrictions determine. `route_dominates` is `padicStepReceipt_route` at the gap
decomposition `k - i = (k - j) + (j - i)`; it is proved, not posited. -/
def padicCostedTower (p : ℕ) [Fact p.Prime] : CostedTower.{0, 0} ℕ where
  toTower := padicTower p
  receipt := fun {i j} _ => padicStepReceipt p (j - i)
  route_dominates := by
    intro i j k hij hjk
    show (padicStepReceipt p (k - i)).vector ≤
      ((padicStepReceipt p (k - j)).compose (padicStepReceipt p (j - i))).vector
    rw [show k - i = (k - j) + (j - i) from by omega]
    exact padicStepReceipt_route p (k - j) (j - i)

@[simp] theorem padicCostedTower_toTower (p : ℕ) [Fact p.Prime] :
    (padicCostedTower p).toTower = padicTower p := rfl

@[simp] theorem padicCostedTower_receipt (p : ℕ) [Fact p.Prime] {i j : ℕ} (h : i ≤ j) :
    (padicCostedTower p).receipt h = padicStepReceipt p (j - i) := rfl

/-- [proved-derived; formal-checked] **The two-step route's total is `CostReceipt.compose`, and
that is `serial_receipt_balance`.** The declared readings of the two restrictions add, the middle
chart's potential cancels at the joined boundary, and what is left is the composed receipt's
coordinate. This is the additivity law read at the tower's own charts; the domination of the direct
receipt by this total is a separate matter and is proved axis by axis below. -/
theorem padicCostedTower_serial_balance (p : ℕ) [Fact p.Prime] (ax : Axis) (φ : ℕ → ℝ)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (declaredHigh declaredLow residualHigh residualLow : ℝ)
    (hHigh : declaredHigh
      = ((((padicCostedTower p).receipt hjk).vector ax : ℕ) : ℝ) + φ k - φ j + residualHigh)
    (hLow : declaredLow
      = ((((padicCostedTower p).receipt hij).vector ax : ℕ) : ℝ) + φ j - φ i + residualLow) :
    declaredHigh + declaredLow
      = (((((padicCostedTower p).receipt hjk).compose
            ((padicCostedTower p).receipt hij)).vector ax : ℕ) : ℝ)
        + φ k - φ i + (residualHigh + residualLow) :=
  serial_receipt_balance ax φ _ _ k j i declaredHigh declaredLow residualHigh residualLow hHigh hLow

/-- [proved-derived; formal-checked] On the three step-counting axes the direct restriction costs
**exactly** the two-step route: the dropped digits are the same digits either way. -/
theorem padicCostedTower_route_equality_on_step_axes (p : ℕ) [Fact p.Prime] {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) {ax : Axis}
    (hax : ax = Axis.bytes ∨ ax = Axis.decodeWork ∨ ax = Axis.updateWork) :
    ((padicCostedTower p).receipt (le_trans hij hjk)).vector ax
      = (((padicCostedTower p).receipt hjk).compose
          ((padicCostedTower p).receipt hij)).vector ax := by
  have hgap : k - i = (k - j) + (j - i) := by omega
  rcases hax with rfl | rfl | rfl
  · show (k - i) * digitOctets p = (k - j) * digitOctets p + (j - i) * digitOctets p
    rw [hgap, Nat.add_mul]
  · show k - i = (k - j) + (j - i)
    exact hgap
  · show k - i = (k - j) + (j - i)
    exact hgap

/-- [proved-derived; formal-checked] **On `certificateWork` the law is strict at every triple.** The
direct presentation is verified after one header check; the two-step route checks two headers. This
is the axis on which "a direct presentation may share work between the steps" is not a manner of
speaking. -/
theorem padicCostedTower_route_strict_at_certificateWork (p : ℕ) [Fact p.Prime] {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    ((padicCostedTower p).receipt (le_trans hij hjk)).vector Axis.certificateWork
      < (((padicCostedTower p).receipt hjk).compose
          ((padicCostedTower p).receipt hij)).vector Axis.certificateWork := by
  show k - i + 1 < k - j + 1 + (j - i + 1)
  omega

/-- [proved-derived; formal-checked] **The residual coordinate is the composite transition's own.**
Written at additively presented charts, where `Transition.comp` of the two restriction transitions
typechecks with no cast: the receipt of `i ≤ i + d₂ + d₁` carries exactly the code size of
`Nat.card` of the composite residual of `padicRestrictTransition p (i + d₂) d₁` followed by
`padicRestrictTransition p i d₂`. The residual axis of `route_dominates` is therefore
`codeBits_residual_comp_le` at the tower's own restrictions and not a separate postulate. -/
theorem padicCostedTower_residual_eq_comp (p : ℕ) [Fact p.Prime] (i d₂ d₁ : ℕ) :
    ((padicCostedTower p).receipt (show i ≤ i + d₂ + d₁ by omega)).vector Axis.residual
      = codeBits (Nat.card (Transition.comp (padicRestrictTransition p i d₂)
          (padicRestrictTransition p (i + d₂) d₁)).Residual) := by
  have hcard : Nat.card (Transition.comp (padicRestrictTransition p i d₂)
      (padicRestrictTransition p (i + d₂) d₁)).Residual = p ^ (d₂ + d₁) := by
    show Nat.card (ZMod (p ^ d₂) × ZMod (p ^ d₁)) = p ^ (d₂ + d₁)
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod, pow_add]
  rw [hcard]
  show codeBits (p ^ (i + d₂ + d₁ - i)) = codeBits (p ^ (d₂ + d₁))
  rw [show i + d₂ + d₁ - i = d₂ + d₁ from by omega]

/-- [proved-derived; formal-checked] **The residual axis of the law, obtained from
`codeBits_residual_comp_le` and nothing else.** -/
theorem padicCostedTower_route_residual_is_codeBits_comp (p : ℕ) [Fact p.Prime] (i d₂ d₁ : ℕ) :
    ((padicCostedTower p).receipt (show i ≤ i + d₂ + d₁ by omega)).vector Axis.residual
      ≤ ((padicCostedTower p).receipt (show i + d₂ ≤ i + d₂ + d₁ by omega)).vector Axis.residual
        + ((padicCostedTower p).receipt (show i ≤ i + d₂ by omega)).vector Axis.residual := by
  have h := codeBits_residual_comp_le (padicRestrictTransition p i d₂)
    (padicRestrictTransition p (i + d₂) d₁)
  have hsecond : Nat.card (padicRestrictTransition p i d₂).Residual = p ^ d₂ := by
    show Nat.card (ZMod (p ^ d₂)) = p ^ d₂
    rw [Nat.card_zmod]
  have hfirst : Nat.card (padicRestrictTransition p (i + d₂) d₁).Residual = p ^ d₁ := by
    show Nat.card (ZMod (p ^ d₁)) = p ^ d₁
    rw [Nat.card_zmod]
  rw [hsecond, hfirst] at h
  rw [padicCostedTower_residual_eq_comp]
  show _ ≤ codeBits (p ^ (i + d₂ + d₁ - (i + d₂))) + codeBits (p ^ (i + d₂ - i))
  rw [show i + d₂ + d₁ - (i + d₂) = d₁ from by omega, show i + d₂ - i = d₂ from by omega]
  exact h.trans (le_of_eq (Nat.add_comm _ _))

/-- [counterexample; formal-checked] **The residual axis is strictly subadditive at a real triple.**
At `p = 3` and charts `0 ≤ 1 ≤ 3` the direct restriction's residual codes in five bits and the
two-step route's in six: `27 ≤ 2^5` while the route pays `⌈log₂ 9⌉ + ⌈log₂ 3⌉ = 4 + 2`. Code sizes
do not add, which is why this axis is *not* `serial_receipt_balance`. -/
theorem padicCostedTower_route_strict_at_residual :
    ((padicCostedTower 3).receipt (show (0 : ℕ) ≤ 3 by omega)).vector Axis.residual
      < (((padicCostedTower 3).receipt (show (1 : ℕ) ≤ 3 by omega)).compose
          ((padicCostedTower 3).receipt (show (0 : ℕ) ≤ 1 by omega))).vector Axis.residual := by
  have htwo : (1 : ℕ) < 2 := by norm_num
  show codeBits (3 ^ (3 - 0)) < codeBits (3 ^ (3 - 1)) + codeBits (3 ^ (1 - 0))
  norm_num
  have h27 : codeBits 27 ≤ 5 := (Nat.clog_le_iff_le_pow htwo).mpr (by norm_num)
  have h9 : 4 ≤ codeBits 9 := by
    unfold codeBits
    by_contra hcon
    push Not at hcon
    have hle : Nat.clog 2 9 ≤ 3 := by omega
    have hpow := (Nat.clog_le_iff_le_pow htwo).mp hle
    norm_num at hpow
  have h3 : 2 ≤ codeBits 3 := by
    unfold codeBits
    by_contra hcon
    push Not at hcon
    have hle : Nat.clog 2 3 ≤ 1 := by omega
    have hpow := (Nat.clog_le_iff_le_pow htwo).mp hle
    norm_num at hpow
  omega

/-- [definition] The lossy schema migration of `Foundation/ContinuingTower.lean::padicHalfMigration`
read on the costed tower. The tower is the same tower; only the receipts are added. -/
def padicCostedMigration (p : ℕ) [Fact p.Prime] :
    Migration (padicCostedTower p).toTower (padicCostedTower p).toTower :=
  (padicHalfMigration p).toMigration

/-- [proved-derived; formal-checked] It factors through refinement, by `padicHalfMigration`'s own
proof. -/
theorem padicCostedMigration_factorsThroughRefinement (p : ℕ) [Fact p.Prime] :
    (padicCostedMigration p).FactorsThroughRefinement :=
  padicHalfMigration_factorsThroughRefinement p

/-- [proved-derived; formal-checked] **The open comparison, discharged at a concrete tower, a
concrete migration and concrete receipts.** No cost function is supplied by a caller: both sides are
the `ℤ/p^n` tower's own restriction receipts, the migration is the lossy halving migration, and the
intermediate chart is `j + j / 2`. This is `costBoundedByRefinementRoute_of_route` at
`padicCostedTower`, and it is the witness that the theorem's hypothesis is satisfiable. -/
theorem costBoundedByRefinementRoute_padic (p : ℕ) [Fact p.Prime] :
    Migration.CostBoundedByRefinementRoute (W := CostVector) (padicCostedMigration p)
      (fun j _ => ((padicCostedTower p).receipt
        ((padicCostedMigration_factorsThroughRefinement p).refines j)).vector)
      (fun j _ => (((padicCostedTower p).receipt
            (show j + j / 2 ≤ (padicCostedMigration p).index j from
              Nat.add_le_add_left (Nat.div_le_self j 2) j)).compose
          ((padicCostedTower p).receipt (Nat.le_add_right j (j / 2)))).vector) :=
  costBoundedByRefinementRoute_of_route (padicCostedTower p) (padicCostedMigration p)
    (padicCostedMigration_factorsThroughRefinement p) (fun j => j + j / 2)
    (fun j => Nat.le_add_right j (j / 2))
    (fun j => show j + j / 2 ≤ (padicCostedMigration p).index j from
      Nat.add_le_add_left (Nat.div_le_self j 2) j)

/-- [definition] The receipt of a restriction that presents nothing: `unitTower`'s one-point face.
No octet is written, no step is taken, and the fibre is the single point, whose code size is
`codeBits 1 = 0`. -/
def emptyStepReceipt : CostReceipt where
  bytes := ⟨0, .measured "the one-point face occupies no octets"⟩
  decodeWork := ⟨0, .measured "the one-point face decodes in no steps"⟩
  updateWork := ⟨0, .measured "the one-point face admits no change"⟩
  certificateWork := ⟨0, .measured "the one-point face verifies in no steps"⟩
  residual := ⟨codeBits 1, .derived "codeBits of the one-element fibre of unitTower's restriction"⟩

/-- [proved-derived; formal-checked] **The minimal costed tower.** `unitTower` with the empty
receipt. It is a genuine instance and not a degenerate one: the receipt is what its restriction
actually presents. -/
def unitCostedTower : CostedTower.{0, 0} ℕ where
  toTower := unitTower
  receipt := fun _ => emptyStepReceipt
  route_dominates := by
    intro i j k hij hjk ax
    cases ax <;> simp [emptyStepReceipt, CostReceipt.vector, CostReceipt.counted,
      CostReceipt.compose, codeBits]

/-- [proved-derived; formal-checked] Its law holds with equality on every axis: nothing is saved by
going directly because nothing is spent either way. -/
theorem unitCostedTower_route_equality {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (ax : Axis) :
    (unitCostedTower.receipt (le_trans hij hjk)).vector ax
      = ((unitCostedTower.receipt hjk).compose (unitCostedTower.receipt hij)).vector ax := by
  cases ax <;> simp [unitCostedTower, emptyStepReceipt, CostReceipt.vector, CostReceipt.counted,
    CostReceipt.compose, codeBits]

/-- [definition] A receipt assignment that bills the **square** of the number of charts crossed. It
is a perfectly well-formed family of receipts on any `ℕ`-indexed tower — every coordinate is a
declared count with its declarer — and it is not the receipt family of a `CostedTower`. -/
def squaredGapReceipt (i j : ℕ) : CostReceipt where
  bytes := ⟨(j - i) * (j - i), .declared "a receiver billing the square of the chart gap"⟩
  decodeWork := ⟨0, .declared "a receiver billing the square of the chart gap"⟩
  updateWork := ⟨0, .declared "a receiver billing the square of the chart gap"⟩
  certificateWork := ⟨0, .declared "a receiver billing the square of the chart gap"⟩
  residual := ⟨0, .declared "a receiver billing the square of the chart gap"⟩

/-- [counterexample; formal-checked] **`route_dominates` fails for it, at charts `0 ≤ 1 ≤ 2`.** The
direct restriction is billed `2² = 4` octets and the two-step route `1² + 1² = 2`. -/
theorem squaredGapReceipt_route_fails :
    ¬ (squaredGapReceipt 0 2).vector ≤
        ((squaredGapReceipt 1 2).compose (squaredGapReceipt 0 1)).vector := by
  intro hcon
  have hbytes := hcon Axis.bytes
  simp [squaredGapReceipt, CostReceipt.vector, CostReceipt.counted, CostReceipt.compose] at hbytes

/-- [counterexample; formal-checked] **So the field is a real condition.** No `CostedTower` over any
`ℕ`-indexed tower — `padicTower` and `unitTower` included — can carry the squared-gap receipts: its
own `route_dominates` at `0 ≤ 1 ≤ 2` would say `4 ≤ 2`. Together with `padicCostedTower` and
`unitCostedTower` this places `route_dominates` strictly between "vacuous" and "automatic". -/
theorem no_costedTower_with_squaredGapReceipt (C : CostedTower.{0, v} ℕ)
    (h : ∀ (i j : ℕ) (hij : i ≤ j), C.receipt hij = squaredGapReceipt i j) : False := by
  have hlaw := C.route_dominates (show (0 : ℕ) ≤ 1 by omega) (show (1 : ℕ) ≤ 2 by omega)
  rw [h 0 2, h 1 2, h 0 1] at hlaw
  exact squaredGapReceipt_route_fails hlaw

/-- [proved-derived; formal-checked] **The failure is the assignment's and not the charts'.** At the
very charts `0 ≤ 1 ≤ 2` where `squaredGapReceipt` breaks the law, the `ℤ/p^n` tower's own receipts
satisfy it. So `route_dominates` separates receipt assignments over one and the same index, which is
what it means for it to be a condition on the receipts. -/
theorem padicCostedTower_route_holds_where_squaredGapReceipt_fails (p : ℕ) [Fact p.Prime] :
    ((padicCostedTower p).receipt (show (0 : ℕ) ≤ 2 by omega)).vector ≤
      (((padicCostedTower p).receipt (show (1 : ℕ) ≤ 2 by omega)).compose
        ((padicCostedTower p).receipt (show (0 : ℕ) ≤ 1 by omega))).vector :=
  (padicCostedTower p).route_dominates (show (0 : ℕ) ≤ 1 by omega) (show (1 : ℕ) ≤ 2 by omega)

#print axioms sum_axis
#print axioms serial_receipt_balance
#print axioms dominates_antisymm_vector
#print axioms dominates_antisymm_fails_on_receipts
#print axioms exists_frontier_dominating
#print axioms frontier_nonempty
#print axioms frontier_isAntichain
#print axioms minimizer_isFrontierPoint
#print axioms unsupported_isFrontierPoint
#print axioms unsupported_not_minimizer
#print axioms frontier_has_no_least_point
#print axioms frontier_reparameterization_invariant
#print axioms scalar_minimizer_not_reparameterization_invariant
#print axioms flat_pair_incomparable
#print axioms codeBits_mul_le
#print axioms codeBits_residual_comp_le
#print axioms codeBits_residual_comp_lt_witness
#print axioms costBoundedByRefinementRoute_of_route
#print axioms costBoundedByRefinementRoute_is_caller_decided
#print axioms swapMigration_route_isEmpty
#print axioms padicStepReceipt_route
#print axioms padicCostedTower
#print axioms padicCostedTower_serial_balance
#print axioms padicCostedTower_route_equality_on_step_axes
#print axioms padicCostedTower_route_strict_at_certificateWork
#print axioms padicCostedTower_residual_eq_comp
#print axioms padicCostedTower_route_residual_is_codeBits_comp
#print axioms padicCostedTower_route_strict_at_residual
#print axioms costBoundedByRefinementRoute_padic
#print axioms unitCostedTower
#print axioms unitCostedTower_route_equality
#print axioms squaredGapReceipt_route_fails
#print axioms no_costedTower_with_squaredGapReceipt
#print axioms padicCostedTower_route_holds_where_squaredGapReceipt_fails

end Holonics.Foundation.PresentationCost
