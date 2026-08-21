import ElementaryHolonics.Millennium.Gluing
import ElementaryHolonics.Millennium.Seam
import ElementaryHolonics.Millennium.Hand

/-!
# The lines — the named questions, their shared shape, and what a barrier actually says

Two things live here.

**First, the barrier frame.**  A *receiver family* is a declared set of readings.  It is **blind**
to a property when two objects differ in that property and no reading in the family separates
them.  The theorem `blindFamilyCarriesNoVerdict` says that a blind family carries no verdict:
nothing computed from its readings decides the property.  That is the general form of every
modern barrier result — relativization, the large-and-constructive barrier, the sieve's parity
obstruction, and the averaged-equation construction are all instances, and none of them is a
statement that a question is hard.  They are statements that a declared aperture is blind.

**Second, the index of lines.**  Each named question is recorded with its composed name, its
classical aside, the shape it instantiates, and whether an obstruction group is known for it.
The index is data, so a claim about the family can be checked rather than asserted, and
`theIndexCountsFourOpenLinesWithNoObstructionGroup` does exactly that.

Every `theorem` here is discharged.  Nothing here formalizes any named conjecture; the shapes are
faithful and the mathematics is not present, which is stated on each declaration.

**Cold-audit scope (2026-08-21).** `theLines` is a finite documentation index, not a theorem
database. The `composed` strings are receiver-relative paraphrases and the `aside` strings are
classical labels; neither field proves the named result. Four rows were corrected against their
classical referents: Poincare's “round” metric was removed, the function-field row now names
nontrivial zeros rather than “no place at infinity,” Hodge now names rational `(p,p)` classes,
and P versus NP now names polynomial-time verification/search. BSD and the remaining open rows
are still paraphrases, not formalizations.
-/

namespace Soma.Holonics.Millennium.Lines

/-! ## 1. A declared receiver family, and what its blindness costs -/

universe u v w

/-- A **receiver family**: an indexed set of readings of a type. -/
structure ReceiverFamily (X : Type u) (V : Type v) where
  /-- What readings are available. -/
  Index : Type w
  /-- Taking one. -/
  read : Index → X → V

namespace ReceiverFamily

variable {X : Type u} {V : Type v} (R : ReceiverFamily.{u, v, w} X V)

/-- Two objects are **separated** when some reading in the family distinguishes them. -/
def Separates (a b : X) : Prop := ∃ i : R.Index, R.read i a ≠ R.read i b

/-- The family is **blind** to a property when the property differs across a pair that no
reading separates. -/
def Blind (P : X → Prop) : Prop :=
  ∃ a b : X, P a ∧ ¬ P b ∧ ∀ i : R.Index, R.read i a = R.read i b

/-- **A blind family carries no verdict.**

If no reading in the declared family separates a pair that the property distinguishes, then no
function whatsoever of that family's readings decides the property.  The obstruction is the
aperture, not the difficulty.

This is the shape shared by every barrier theorem in the index below.  It is what makes a null
search informative: a search that returns nothing returns *nothing at all* unless it can state
the family it exhausted, and with that statement it becomes this theorem. -/
theorem blindFamilyCarriesNoVerdict (P : X → Prop) (h : R.Blind P) :
    ¬ ∃ verdict : (R.Index → V) → Prop, ∀ x : X, P x ↔ verdict (fun i => R.read i x) := by
  rintro ⟨verdict, hv⟩
  obtain ⟨a, b, hPa, hPb, hsame⟩ := h
  refine hPb ((hv b).mpr ?_)
  have : (fun i => R.read i b) = (fun i => R.read i a) := funext fun i => (hsame i).symm
  rw [this]
  exact (hv a).mp hPa

/-- Conversely, **a family that separates every distinguished pair is not the obstruction.**
Stated so that "the aperture is blind" is a claim someone has to earn. -/
theorem separatingFamilyIsNotBlind (P : X → Prop)
    (h : ∀ a b : X, P a → ¬ P b → R.Separates a b) : ¬ R.Blind P := by
  rintro ⟨a, b, hPa, hPb, hsame⟩
  obtain ⟨i, hi⟩ := h a b hPa hPb
  exact hi (hsame i)

/-- **Breaking a barrier is adding a reading.**  A family blind to a property stops being blind
exactly when a reading is adjoined that separates the offending pair. -/
theorem adjoiningAReadingCanBreakBlindness
    (P : X → Prop) (f : X → V)
    (h : ∀ a b : X, P a → ¬ P b → f a ≠ f b) :
    ¬ (ReceiverFamily.mk (Option R.Index)
        (fun i => match i with | none => f | some j => R.read j)).Blind P := by
  rintro ⟨a, b, hPa, hPb, hsame⟩
  exact h a b hPa hPb (hsame none)

end ReceiverFamily

/-! ## 1b. The frame is not vacuous — a witnessed blind family

An abstract predicate with no instance is an untested gauge.  This section exhibits the smallest
witness: a declared family of readings, and a pair the property distinguishes that no reading in
it separates. -/

/-- The residue reading modulo two — one reading, declared. -/
def residueFamily : ReceiverFamily ℕ ℕ where
  Index := Unit
  read := fun _ n => n % 2

/-- **The residue family is blind to the hand.**

Two and four are congruent modulo two and carry opposite hands.  So no function whatsoever of
that reading decides the hand, by `blindFamilyCarriesNoVerdict`.  The witness is small on purpose:
it shows the frame bites without needing the sieve-theoretic obstruction, which is the same shape
at a scale nothing here formalizes. -/
theorem theResidueFamilyIsBlindToTheHand :
    residueFamily.Blind (fun n => Hand.hand n = 1) := by
  have h4 : Hand.factorDepth 4 = 2 := by
    simpa using ArithmeticFunction.cardFactors_apply_prime_pow (p := 2) (k := 2) Nat.prime_two
  have h2 : Hand.factorDepth 2 = 1 := ArithmeticFunction.cardFactors_apply_prime Nat.prime_two
  refine ⟨4, 2, ?_, ?_, fun _ => rfl⟩
  · simp [Hand.hand, h4]
  · simp [Hand.hand, h2]

/-- **Therefore the residue reading carries no verdict about the hand.**  The abstract theorem,
applied to the witness. -/
theorem theResidueReadingCarriesNoVerdictAboutTheHand :
    ¬ ∃ verdict : (residueFamily.Index → ℕ) → Prop,
        ∀ n : ℕ, Hand.hand n = 1 ↔ verdict (fun i => residueFamily.read i n) :=
  residueFamily.blindFamilyCarriesNoVerdict _ theResidueFamilyIsBlindToTheHand

/-! ## 2. The index of named lines

Each row is data.  The composed name states the mechanism; the aside carries the classical
label, which is an address and never the name. -/

/-- What is known about a line. -/
inductive LineStatus where
  /-- A realizer was built and the line closed. -/
  | closedByBuildingTheRealizer
  /-- Closed in the case where the shape degenerates — typically because a place is absent. -/
  | closedWhereTheShapeDegenerates
  /-- No realizer; the obstruction population is uninhabited only conjecturally. -/
  | openForWantOfARealizer
  deriving DecidableEq, Repr

/-- One named line. -/
structure NamedLine where
  /-- The composed name: the mechanism, readable and rebuildable from its parts. -/
  composed : String
  /-- The classical label, as an aside. -/
  aside : String
  /-- What plays the part of a realizer. -/
  realizer : String
  /-- Whether a group measuring the failure to glue is known. -/
  obstructionGroupKnown : Bool
  /-- Where it stands. -/
  status : LineStatus
  deriving Repr

/-- **The index.**  Every row is a gluing passage: local data, a realizer population, and the
question of whether local admissibility already forces a realizer. -/
def theLines : List NamedLine :=
  [ { composed := "every closed simply-connected 3-manifold is the 3-sphere"
    , aside := "Poincaré conjecture"
    , realizer := "a flow with surgery, exhibiting what it cut"
    , obstructionGroupKnown := true
    , status := .closedByBuildingTheRealizer }
  , { composed := "every nontrivial zero of a function-field zeta function sits on the seam"
    , aside := "the Riemann Hypothesis over a function field"
    , realizer := "an ample class, whose pairing has a one-point null cone"
    , obstructionGroupKnown := true
    , status := .closedWhereTheShapeDegenerates }
  , { composed := "every mode sits on the self-conjugate seam"
    , aside := "the Riemann Hypothesis"
    , realizer := "a positive realizer at the place at infinity — not built"
    , obstructionGroupKnown := false
    , status := .openForWantOfARealizer }
  , { composed := "every rational (p,p)-class is carried by an algebraic cycle"
    , aside := "the Hodge conjecture"
    , realizer := "an algebraic cycle"
    , obstructionGroupKnown := true
    , status := .openForWantOfARealizer }
  , { composed := "the analytic order counts the realizers"
    , aside := "Birch and Swinnerton-Dyer"
    , realizer := "a rational point, with its height pairing"
    , obstructionGroupKnown := true
    , status := .openForWantOfARealizer }
  , { composed := "the flow never leaves the grain its conserved reading can see"
    , aside := "Navier-Stokes existence and smoothness"
    , realizer := "a monotone quantity at the critical grain"
    , obstructionGroupKnown := false
    , status := .openForWantOfARealizer }
  , { composed := "the return closes above zero"
    , aside := "the Yang-Mills existence and mass gap"
    , realizer := "the constructed theory, and a positive spectral bound"
    , obstructionGroupKnown := false
    , status := .openForWantOfARealizer }
  , { composed := "every polynomial-time verifiable decision language is polynomial-time decidable"
    , aside := "P versus NP"
    , realizer := "a search that meets the checker's budget"
    , obstructionGroupKnown := false
    , status := .openForWantOfARealizer } ]

/-- The open lines. -/
def theOpenLines : List NamedLine :=
  theLines.filter (fun l => l.status = LineStatus.openForWantOfARealizer)

/-- The open lines for which no obstruction group is known. -/
def theOpenLinesWithNoObstructionGroup : List NamedLine :=
  theOpenLines.filter (fun l => !l.obstructionGroupKnown)

/-- **Six lines are open, and four of them have no obstruction group in this index.**

Checked against the index rather than asserted.  The four without a group are the Riemann,
Navier–Stokes, Yang–Mills, and verify-to-search rows in this index: exactly the rows for which
"how much does the gluing fail" is not a question this documentation can currently pose, only
"does it". This is a count of declared booleans, not a mathematical classification.

That is the difference the framework is pointing at.  Where a group exists, the question is
plural and can be chipped at; where none does, the question is binary and there is nothing to
chip. -/
theorem theIndexCountsFourOpenLinesWithNoObstructionGroup :
    theOpenLines.length = 6 ∧ theOpenLinesWithNoObstructionGroup.length = 4 := by
  constructor <;> decide

/-- **Every line in the index is stated as a gluing passage.**  Recorded as a property of the
index so a later row cannot be added in another shape without this failing. -/
theorem everyLineNamesARealizer : ∀ l ∈ theLines, l.realizer ≠ "" := by
  decide

/-! ## 3. What is here and what is not

The receiver-family theorems in section 1 are real and discharged.  The index in section 2 is
data about the lines and carries no mathematics about any of them.

**No named conjecture is formalized here.**  `Seam.lean` carries the only line whose statement is
the genuine one, because mathlib supplies the comb; the other seven rows name shapes.  A row is
not evidence, and nothing in this file may be cited as movement on any question in it.

The next thing owed is the bridge in `Seam.lean`: the classical equivalence between the placement
of the modes and the cancellation of the hand.  It is a real theorem, it is not formalized in
mathlib, and formalizing it would make the two charts of that object one object here. -/

end Soma.Holonics.Millennium.Lines
