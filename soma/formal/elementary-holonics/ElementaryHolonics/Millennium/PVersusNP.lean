import Mathlib.Computability.Language
import Mathlib.Computability.TMComputable

/-!
# P versus NP — the actual decision-language and polynomial-time object

`ChainRule.lean` and `Border.lean` carry exact finite algebraic mechanisms which may later serve
as receivers for complexity questions. They do not define `P`, `NP`, or the statement `P = NP`.
This file imports the missing classical object using mathlib's finite multi-tape Turing machines
and its step-counted polynomial-time predicate.

The alphabet is binary. `InP` asks for a polynomial-time decider. `InNP` asks for a
polynomial-time verifier together with a polynomial bound on certificate length. The proposition
`PEqualsNP` is the open equality itself; no theorem below asserts it or its negation.
-/

noncomputable section

namespace Soma.Holonics.Millennium.PVersusNP

open Computability

/-- A binary input or certificate word. -/
abbrev Word := List Bool

/-- A decision language over binary words. -/
abbrev DecisionLanguage := Language Bool

/-- The fixed identity encoding of a binary word. The encoding is part of the complexity receipt;
it is not selected by a later existential or an arbitrary default. -/
def wordEncoding : FinEncoding Word where
  Γ := Bool
  encode := id
  decode := some
  decode_encode := by intro input; rfl
  ΓFin := Bool.fintype

private def leftBit : Bool ⊕ Bool → Option Bool
  | .inl bit => some bit
  | .inr _ => none

private def rightBit : Bool ⊕ Bool → Option Bool
  | .inl _ => none
  | .inr bit => some bit

/-- The fixed tagged encoding of an instance/certificate pair. -/
def instanceCertificateEncoding : FinEncoding (Word × Word) where
  Γ := Bool ⊕ Bool
  encode := fun pair => pair.1.map Sum.inl ++ pair.2.map Sum.inr
  decode := fun encoded => some (encoded.filterMap leftBit, encoded.filterMap rightBit)
  decode_encode := by
    rintro ⟨input, certificate⟩
    simp only [List.filterMap_append, List.filterMap_map]
    simp [Function.comp_def, leftBit, rightBit]
  ΓFin := inferInstance

/-- The tagged pair encoding charges exactly the input and certificate populations. -/
theorem instanceCertificateEncoding_length (input certificate : Word) :
    (instanceCertificateEncoding.encode (input, certificate)).length =
      input.length + certificate.length := by
  simp [instanceCertificateEncoding]

/-- A Boolean function decides a language when its `true` fibre is exactly that language. -/
def Decides (decider : Word → Bool) (language : DecisionLanguage) : Prop :=
  ∀ input, decider input = true ↔ input ∈ language

/-- A function on binary words is computed in polynomial time by mathlib's finite TM2 model. -/
def WordFunctionInPolynomialTime (f : Word → Word) : Prop :=
  Nonempty
    (Turing.TM2ComputableInPolyTime
      wordEncoding wordEncoding f)

/-- A Boolean-valued function on binary words is computed in polynomial time. -/
def BooleanFunctionInPolynomialTime (f : Word → Bool) : Prop :=
  Nonempty
    (Turing.TM2ComputableInPolyTime
      wordEncoding finEncodingBoolBool f)

/-- A verifier on an input/certificate pair is computed in polynomial time. -/
def VerifierInPolynomialTime (verify : Word × Word → Bool) : Prop :=
  Nonempty
    (Turing.TM2ComputableInPolyTime
      instanceCertificateEncoding finEncodingBoolBool verify)

/-- **The class P.** Membership has a polynomial-time decider. -/
def InP (language : DecisionLanguage) : Prop :=
  ∃ decider : Word → Bool,
    Decides decider language ∧ BooleanFunctionInPolynomialTime decider

/-- **The class NP.** Positive membership has a polynomially bounded certificate checked by a
polynomial-time verifier. -/
def InNP (language : DecisionLanguage) : Prop :=
  ∃ verify : Word × Word → Bool,
    VerifierInPolynomialTime verify ∧
      ∃ certificateBound : Polynomial ℕ,
        ∀ input,
          input ∈ language ↔
            ∃ certificate : Word,
              certificate.length ≤ certificateBound.eval input.length ∧
                verify (input, certificate) = true

/-- Polynomial-time many-one reduction between decision languages. -/
def PolynomialManyOneReduces (source target : DecisionLanguage) : Prop :=
  ∃ transport : Word → Word,
    WordFunctionInPolynomialTime transport ∧
      ∀ input, input ∈ source ↔ transport input ∈ target

/-- The inclusion `P ⊆ NP`, stated independently of whether its routine machine-level closure
lemmas have been assembled in this repository. -/
def PSubsetNP : Prop := ∀ language : DecisionLanguage, InP language → InNP language

/-- **The official equality questioned by P versus NP.** -/
def PEqualsNP : Prop :=
  ∀ language : DecisionLanguage, InP language ↔ InNP language

/-- The separating alternative. -/
def PNotEqualsNP : Prop := ¬ PEqualsNP

/-- Equality is precisely the two class inclusions. -/
theorem pEqualsNP_iff_bothInclusions :
    PEqualsNP ↔
      (PSubsetNP ∧ ∀ language : DecisionLanguage, InNP language → InP language) := by
  constructor
  · intro h
    constructor
    · intro language hP
      exact (h language).mp hP
    · intro language hNP
      exact (h language).mpr hNP
  · rintro ⟨hPNP, hNPP⟩ language
    exact ⟨hPNP language, hNPP language⟩

end Soma.Holonics.Millennium.PVersusNP
