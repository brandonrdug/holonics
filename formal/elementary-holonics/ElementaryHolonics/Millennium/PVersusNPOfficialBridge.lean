import ElementaryHolonics.Millennium.PVersusNP

/-!
# Constructive finish lines for P versus NP

**[definition]** The terminal propositions remain the TM2-language definitions in `PVersusNP`.
This module presents two construction targets.  Equality uses a uniform compiler which turns the
verifier, certificate bound, and correctness receipt of an NP presentation into an actual
polynomial-time decider.  Separation requires one actual language with an NP presentation and a
proof that no polynomial-time decider exists.

**[open]** `P ⊆ NP` is an explicit hypothesis throughout: the repository has not yet assembled
the routine TM2 closure proof needed to construct it.
-/

noncomputable section

namespace Soma.Holonics.Millennium.PVersusNPOfficialBridge

open Computability
open Soma.Holonics.Millennium.PVersusNP

/-- [definition] The data hidden behind one occurrence of `InNP`, retained as a reusable source
presentation rather than destructed into an existential and forgotten. -/
structure NPPresentation (language : DecisionLanguage) where
  verifier : Word × Word → Bool
  verifierPolynomial : VerifierInPolynomialTime verifier
  certificateBound : Polynomial ℕ
  correct : ∀ input,
    input ∈ language ↔
      ∃ certificate : Word,
        certificate.length ≤ certificateBound.eval input.length ∧
          verifier (input, certificate) = true

/-- [proved-derived; formal-checked] A retained NP presentation returns the repository's exact
`InNP` proposition. -/
theorem NPPresentation.inNP {language : DecisionLanguage}
    (presentation : NPPresentation language) : InNP language := by
  exact ⟨presentation.verifier, presentation.verifierPolynomial,
    presentation.certificateBound, presentation.correct⟩

/-- [proved-derived; formal-checked] Every proof of `InNP` can be opened into the retained
presentation required by a uniform construction. -/
def NPPresentation.ofInNP {language : DecisionLanguage} (h : InNP language) :
    NPPresentation language :=
  let verifier := Classical.choose h
  let verifierReceipt := Classical.choose_spec h
  let bound := Classical.choose verifierReceipt.2
  {
    verifier := verifier
    verifierPolynomial := verifierReceipt.1
    certificateBound := bound
    correct := Classical.choose_spec verifierReceipt.2
  }

/-- [project-postulate] The constructive `P = NP` finish line.  A single compiler consumes every
NP presentation and returns both a decider and its polynomial-time machine receipt.  It does not
store `PEqualsNP` or the reverse class inclusion as a field. -/
structure UniformVerifierCompiler where
  decider : ∀ (language : DecisionLanguage), NPPresentation language → Word → Bool
  correct : ∀ (language : DecisionLanguage) (presentation : NPPresentation language),
    Decides (decider language presentation) language
  polynomial : ∀ (language : DecisionLanguage) (presentation : NPPresentation language),
    BooleanFunctionInPolynomialTime (decider language presentation)

/-- [proved-derived; formal-checked] A uniform verifier compiler closes the hard inclusion
`NP ⊆ P`. -/
theorem inP_of_uniformVerifierCompiler (compiler : UniformVerifierCompiler)
    {language : DecisionLanguage} (hNP : InNP language) : InP language := by
  let presentation := NPPresentation.ofInNP hNP
  exact ⟨compiler.decider language presentation,
    compiler.correct language presentation,
    compiler.polynomial language presentation⟩

/-- [proved-derived; formal-checked] With the separately owed standard inclusion `P ⊆ NP`, a
uniform verifier compiler returns the literal `PEqualsNP` terminal proposition. -/
theorem pEqualsNP_of_uniformVerifierCompiler
    (hPSubsetNP : PSubsetNP) (compiler : UniformVerifierCompiler) : PEqualsNP := by
  exact (pEqualsNP_iff_bothInclusions).2
    ⟨hPSubsetNP, fun language hNP ↦ inP_of_uniformVerifierCompiler compiler hNP⟩

/-- [project-postulate] The constructive `P ≠ NP` finish line: one named decision language,
its complete NP presentation, and the impossibility of every polynomial-time decider. -/
structure ConcreteSeparator where
  language : DecisionLanguage
  npPresentation : NPPresentation language
  notInP : ¬ InP language

/-- [proved-derived; formal-checked] A concrete separator returns the literal `PNotEqualsNP`
terminal proposition, without any model-independent slogan standing in for the TM2 proof. -/
theorem pNotEqualsNP_of_concreteSeparator (separator : ConcreteSeparator) : PNotEqualsNP := by
  intro hEquality
  exact separator.notInP
    ((hEquality separator.language).mpr separator.npPresentation.inNP)

/-- [proved-derived; formal-checked] Once `P ⊆ NP` is supplied, inequality is exactly the
existence of an NP language outside P.  This is the logical finish-line normal form. -/
theorem pNotEqualsNP_iff_exists_np_not_p (hPSubsetNP : PSubsetNP) :
    PNotEqualsNP ↔ ∃ language : DecisionLanguage, InNP language ∧ ¬ InP language := by
  classical
  constructor
  · intro hne
    by_contra hseparator
    apply hne
    apply (pEqualsNP_iff_bothInclusions).2
    refine ⟨hPSubsetNP, ?_⟩
    intro language hNP
    by_contra hnotP
    exact hseparator ⟨language, hNP, hnotP⟩
  · rintro ⟨language, hNP, hnotP⟩ hEquality
    exact hnotP ((hEquality language).mpr hNP)

/-- [project-postulate] The missing closure theorem for the chosen TM2 encoding: a
polynomial-time many-one pullback of a P language is again in P. -/
structure HasPolynomialReductionPullback : Prop where
  pullback : ∀ {source target : DecisionLanguage},
    PolynomialManyOneReduces source target → InP target → InP source

/-- [proved-derived; formal-checked] Under the explicit pullback port, hardness transports
forward across a polynomial many-one reduction. -/
theorem notInP_of_reduces_of_notInP
    (closure : HasPolynomialReductionPullback)
    {source target : DecisionLanguage}
    (reduction : PolynomialManyOneReduces source target)
    (sourceNotInP : ¬ InP source) : ¬ InP target := by
  intro targetInP
  exact sourceNotInP (closure.pullback reduction targetInP)

/-- [proved-derived; formal-checked] Bidirectional polynomial reductions preserve P-membership
once the TM2 pullback closure is supplied. -/
theorem inP_iff_of_polynomiallyEquivalent
    (closure : HasPolynomialReductionPullback)
    {left right : DecisionLanguage}
    (leftToRight : PolynomialManyOneReduces left right)
    (rightToLeft : PolynomialManyOneReduces right left) :
    InP left ↔ InP right :=
  ⟨closure.pullback rightToLeft, closure.pullback leftToRight⟩

section Audit

#print axioms pEqualsNP_of_uniformVerifierCompiler
#print axioms pNotEqualsNP_of_concreteSeparator
#print axioms pNotEqualsNP_iff_exists_np_not_p
#print axioms inP_iff_of_polynomiallyEquivalent

end Audit

end Soma.Holonics.Millennium.PVersusNPOfficialBridge
