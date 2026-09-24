import ElementaryHolonics.Millennium.PVersusNP

/-!
# AdviceBar: a lengthwise table separates nothing

The same species of theorem as `CokernelCalculus`'s rational bar, on the complexity
side.  A construction that *looks* like it witnesses a universal statement, and does
not.

The tempting move is: for each input length there is a finite table deciding the
language on that length, so the language has "circuits", so it is in `P/poly`.  The
move fails, and it fails for a reason worth having as a theorem: **the lengthwise
table predicate holds of every language whatsoever**, including undecidable ones.  A
predicate true of everything separates nothing.

* **`theLengthwiseTableExistsForEveryLanguage`** — for every language and every
  length there is a decider correct on that length.  No computability, no bound, no
  content.
* **`thePredicateTrueOfEveryLanguageSeparatesNothing`** — and a predicate holding of
  every language cannot distinguish any two.
* **`theLengthwiseTableRouteCannotEstablishAnything`** — so the route cannot establish
  membership in `P`, in `NP`, or any other class: if it could, every language would be
  in that class.

What `P/poly` actually asks for is a **size bound polynomial in the length, uniform
over lengths**, and a full truth table is normally exponential.  `PolynomiallyBounded`
below is that predicate, and nothing here proves it vacuous — the difference between
the two is exactly the content.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.AdviceBar

open Soma.Holonics.Millennium.PVersusNP

/-! ## 1. The vacuous predicate -/

/-- **The lengthwise table predicate**: for each input length, some decider is correct
on every word of that length.  No bound on the decider, no uniformity across lengths. -/
def LengthwiseTable (language : DecisionLanguage) : Prop :=
  ∀ n : ℕ, ∃ decider : Word → Bool,
    ∀ w : Word, w.length = n → (decider w = true ↔ w ∈ language)

/-- **THE LENGTHWISE TABLE EXISTS FOR EVERY LANGUAGE**: take the indicator.  This
holds for undecidable languages exactly as it holds for trivial ones. -/
theorem theLengthwiseTableExistsForEveryLanguage (language : DecisionLanguage) :
    LengthwiseTable language := by
  intro n
  classical
  refine ⟨fun w => decide (w ∈ language), fun w _ => ?_⟩
  simp

/-! ## 2. The bar -/

/-- **A PREDICATE TRUE OF EVERY LANGUAGE SEPARATES NOTHING**. -/
theorem thePredicateTrueOfEveryLanguageSeparatesNothing
    (P : DecisionLanguage → Prop) (h : ∀ L, P L) (L₁ L₂ : DecisionLanguage) :
    P L₁ ↔ P L₂ :=
  ⟨fun _ => h L₂, fun _ => h L₁⟩

/-- **THE LENGTHWISE TABLE ROUTE CANNOT ESTABLISH ANYTHING**: if having a table at
every length sufficed for membership in a class, every language would be in it.  So
the route establishes no inclusion — not `NP ⊆ P/poly`, not anything. -/
theorem theLengthwiseTableRouteCannotEstablishAnything
    (Class : DecisionLanguage → Prop)
    (hroute : ∀ L, LengthwiseTable L → Class L) : ∀ L, Class L :=
  fun L => hroute L (theLengthwiseTableExistsForEveryLanguage L)

/-- The lengthwise table is therefore equivalent to the trivially true predicate, and
carries exactly its information. -/
theorem theLengthwiseTableIsTheTriviallyTruePredicate (L : DecisionLanguage) :
    LengthwiseTable L ↔ True :=
  ⟨fun _ => trivial, fun _ => theLengthwiseTableExistsForEveryLanguage L⟩

/-! ## 3. What the advice model actually asks -/

/-- **The predicate `P/poly` actually carries**: a decider for each length **together
with a size bound polynomial in the length**, uniform over lengths.  Nothing above
proves this vacuous, and the gap between it and `LengthwiseTable` is precisely the
whole content of the advice model. -/
def PolynomiallyBounded (size : (Word → Bool) → ℕ) (language : DecisionLanguage) :
    Prop :=
  ∃ (c k : ℕ), ∀ n : ℕ, ∃ decider : Word → Bool,
    size decider ≤ c * (n + 1) ^ k ∧
      ∀ w : Word, w.length = n → (decider w = true ↔ w ∈ language)

/-- **THE BOUND IS THE WHOLE DIFFERENCE**: the bounded predicate implies the vacuous
one and never conversely by anything proved here.  Dropping the bound is what turns a
statement with content into a statement about every language. -/
theorem theBoundIsTheWholeDifference (size : (Word → Bool) → ℕ)
    (language : DecisionLanguage) (h : PolynomiallyBounded size language) :
    LengthwiseTable language := by
  intro n
  obtain ⟨c, k, hck⟩ := h
  obtain ⟨decider, -, hcorrect⟩ := hck n
  exact ⟨decider, hcorrect⟩

end Soma.Holonics.Millennium.AdviceBar
