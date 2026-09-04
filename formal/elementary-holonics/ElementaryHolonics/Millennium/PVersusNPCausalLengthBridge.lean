import ElementaryHolonics.Millennium.PVersusNPOfficialBridge
import ElementaryHolonics.Millennium.ReceiverIndexedCausalLengthTower

/-!
# Encoding-anchored causal length for P versus NP

This file connects causal passage length to the repository's literal finite-TM2 polynomial-time
receiver.  A bound on an abstract schedule, observer clock, critical path, or resource current does
not construct a Turing-machine receipt.  The bridge therefore retains one fixed finite TM2, its
exact encoded input and output configurations, the actual `EvalsTo.steps` population, and equalities
identifying that population with the declared causal passage extent.

Boundary extent and passage extent remain distinct.  The polynomial is evaluated on the fixed
encoding's boundary length.  A uniform upper certificate then constructs mathlib's exact
`TM2ComputableInPolyTime` object rather than storing the already-collapsed proposition.

All introduced carriers are `[definition]`.  Every theorem is
`[proved-derived; formal-checked]` unless its statement says otherwise.
-/

noncomputable section

namespace Soma.Holonics.Millennium.PVersusNPCausalLengthBridge

open Computability
open Soma.Holonics.Millennium.PVersusNP
open Soma.Holonics.Millennium.PVersusNPOfficialBridge
open Soma.Holonics.Millennium.ReceiverIndexedCausalLengthTower

/-! ## One fixed encoding, machine, and exact causal passage population -/

/-- [definition] An encoding-anchored causal-length family.  Mathlib's finite TM2 definitions live
in universe zero, so the encoded carriers are deliberately `Type` rather than arbitrary `Type*`.
`outputComputation_steps` and `passageExtent_outputStep` are the non-vacuity joint: they identify
the declared causal passage with the actual machine evaluation length. -/
structure EncodingAnchoredCausalLengthFamily
    {Input Output InputAlphabet OutputAlphabet : Type}
    (inputEncoding : Input → List InputAlphabet)
    (outputEncoding : Output → List OutputAlphabet)
    (function : Input → Output) where
  machine : Turing.TM2ComputableAux InputAlphabet OutputAlphabet
  boundaryExtent : Input → ℕ
  boundaryExtent_encode : ∀ input, boundaryExtent input = (inputEncoding input).length
  lowerExtent : Input → ℕ
  passageExtent : Input → ℕ
  lowerExtent_le : ∀ input, lowerExtent input ≤ passageExtent input
  outputStep : Input → ℕ
  passageExtent_outputStep : ∀ input, passageExtent input = outputStep input
  outputComputation : ∀ input,
    Turing.TM2Outputs machine.tm
      (List.map machine.inputAlphabet.invFun (inputEncoding input))
      (Option.some
        (List.map machine.outputAlphabet.invFun (outputEncoding (function input))))
  outputComputation_steps : ∀ input,
    (outputComputation input).steps = outputStep input

/-- [definition] One polynomial uniformly bounds the same causal family on every encoded input. -/
structure UniformCausalLengthUpperBound
    {Input Output InputAlphabet OutputAlphabet : Type}
    {inputEncoding : Input → List InputAlphabet}
    {outputEncoding : Output → List OutputAlphabet}
    {function : Input → Output}
    (family : EncodingAnchoredCausalLengthFamily inputEncoding outputEncoding function) where
  polynomial : Polynomial ℕ
  passageExtent_le : ∀ input,
    family.passageExtent input ≤ polynomial.eval (family.boundaryExtent input)

namespace EncodingAnchoredCausalLengthFamily

variable
    {Input Output InputAlphabet OutputAlphabet : Type}
    {inputEncoding : Input → List InputAlphabet}
    {outputEncoding : Output → List OutputAlphabet}
    {function : Input → Output}

/-- [proved-derived; formal-checked] The causal upper certificate constructs the literal mathlib
polynomial-time TM2 object.  The proof reuses the exact machine evaluation and changes only its
upper-bound field. -/
def toTM2ComputableInPolyTime
    (family : EncodingAnchoredCausalLengthFamily inputEncoding outputEncoding function)
    (upper : UniformCausalLengthUpperBound family) :
    Turing.TM2ComputableInPolyTime inputEncoding outputEncoding function where
  toTM2ComputableAux := family.machine
  time := upper.polynomial
  outputsFun input :=
    { toEvalsTo := family.outputComputation input
      steps_le_m := by
        rw [family.outputComputation_steps input]
        rw [← family.passageExtent_outputStep input]
        simpa [family.boundaryExtent_encode input] using upper.passageExtent_le input }

/-- [proved-derived; formal-checked] The lower causal certificate applies to the actual TM2 step
population, not merely to a schedule shadow. -/
theorem lowerExtent_le_outputSteps
    (family : EncodingAnchoredCausalLengthFamily inputEncoding outputEncoding function)
    (input : Input) :
    family.lowerExtent input ≤ (family.outputComputation input).steps := by
  rw [family.outputComputation_steps input, ← family.passageExtent_outputStep input]
  exact family.lowerExtent_le input

end EncodingAnchoredCausalLengthFamily

/-! ## Exact anchoring into one causal length tower -/

/-- [definition] A source boundary and an enacted history connect a general causal-length tower to
the fixed TM2 family.  The equalities prevent input size or machine steps from being replaced by a
different convenient count. -/
structure TowerTM2Anchor
    {History State BoundaryAddress ClockAddress RulerAddress Receiver Resource : Type*}
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    {Input Output InputAlphabet OutputAlphabet : Type}
    {inputEncoding : Input → List InputAlphabet}
    {outputEncoding : Output → List OutputAlphabet}
    {function : Input → Output}
    (family : EncodingAnchoredCausalLengthFamily inputEncoding outputEncoding function) where
  boundaryState : Input → State
  outputBoundary : Output → State
  outputFace : Output → Receiver
  executionHistory : Input → History
  execution_starts_at_boundary : ∀ input,
    tower.history.source (executionHistory input) = boundaryState input
  boundary_exact : ∀ input,
    tower.boundaryLength (boundaryState input) = family.boundaryExtent input
  passage_exact : ∀ input,
    tower.clockLength (executionHistory input) = family.passageExtent input
  execution_ends_at_output : ∀ input,
    tower.history.target (executionHistory input) = outputBoundary (function input)
  receiver_exact : ∀ input,
    tower.history.receive (executionHistory input) = outputFace (function input)

namespace TowerTM2Anchor

variable
    {History State BoundaryAddress ClockAddress RulerAddress Receiver Resource : Type*}
    {tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource}
    {Input Output InputAlphabet OutputAlphabet : Type}
    {inputEncoding : Input → List InputAlphabet}
    {outputEncoding : Output → List OutputAlphabet}
    {function : Input → Output}
    {family : EncodingAnchoredCausalLengthFamily inputEncoding outputEncoding function}

/-- [proved-derived; formal-checked] Tower clock length is exactly the actual TM2 step population. -/
theorem towerClockLength_eq_outputSteps (anchor : TowerTM2Anchor tower family)
    (input : Input) :
    tower.clockLength (anchor.executionHistory input) =
      (family.outputComputation input).steps := by
  rw [anchor.passage_exact, family.outputComputation_steps,
    ← family.passageExtent_outputStep]

/-- [proved-derived; formal-checked] Tower boundary length is exactly fixed encoded input length. -/
theorem towerBoundaryLength_eq_encodedLength (anchor : TowerTM2Anchor tower family)
    (input : Input) :
    tower.boundaryLength (anchor.boundaryState input) = (inputEncoding input).length := by
  rw [anchor.boundary_exact, family.boundaryExtent_encode]

/-- [definition] Every exterior output whose declared receiver face equals one returned face. -/
def OutputPreimageFibre (anchor : TowerTM2Anchor tower family)
    (face : Receiver) : Type :=
  Soma.Holonics.Foundation.Lift.TransportLift anchor.outputFace face

/-- [proved-derived; formal-checked] The computed function output inhabits the complete exterior
output fibre behind the tower's returned receiver face. -/
def outputReconstructionLift (anchor : TowerTM2Anchor tower family) (input : Input) :
    anchor.OutputPreimageFibre
      (tower.history.receive (anchor.executionHistory input)) :=
  ⟨function input, (anchor.receiver_exact input).symm⟩

end TowerTM2Anchor

/-! ## Official Boolean, verifier, P, and uniform-compiler receivers -/

/-- [proved-derived; formal-checked] A Boolean causal family and uniform upper certificate return
the repository's literal polynomial-time Boolean receiver. -/
theorem booleanFunctionInPolynomialTime_of_uniformCausalLengthUpperBound
    {decider : Word → Bool}
    (family : EncodingAnchoredCausalLengthFamily
      wordEncoding.encode encodingBoolBool.encode decider)
    (upper : UniformCausalLengthUpperBound family) :
    BooleanFunctionInPolynomialTime decider :=
  ⟨family.toTM2ComputableInPolyTime upper⟩

/-- [proved-derived; formal-checked] The same construction at the fixed tagged pair encoding returns
the official verifier-time receiver. -/
theorem verifierInPolynomialTime_of_uniformCausalLengthUpperBound
    {verify : Word × Word → Bool}
    (family : EncodingAnchoredCausalLengthFamily
      instanceCertificateEncoding.encode encodingBoolBool.encode verify)
    (upper : UniformCausalLengthUpperBound family) :
    VerifierInPolynomialTime verify :=
  ⟨family.toTM2ComputableInPolyTime upper⟩

/-- [definition] A complete encoding-anchored proof that one language is in `P`. -/
structure EncodingAnchoredPDecision (language : DecisionLanguage) where
  decider : Word → Bool
  correct : Decides decider language
  family : EncodingAnchoredCausalLengthFamily
    wordEncoding.encode encodingBoolBool.encode decider
  upper : UniformCausalLengthUpperBound family

/-- [proved-derived; formal-checked] The anchored decision object reaches the literal `InP`
finish-line receiver. -/
theorem EncodingAnchoredPDecision.inP {language : DecisionLanguage}
    (decision : EncodingAnchoredPDecision language) : InP language :=
  ⟨decision.decider, decision.correct,
    booleanFunctionInPolynomialTime_of_uniformCausalLengthUpperBound
      decision.family decision.upper⟩

/-- [definition] The constructive equality route expressed entirely through encoding-anchored
causal-length families.  It remains an open construction obligation; no field stores `P = NP`. -/
structure UniformEncodingAnchoredVerifierCompiler where
  decider : ∀ (language : DecisionLanguage), NPPresentation language → Word → Bool
  correct : ∀ (language : DecisionLanguage) (presentation : NPPresentation language),
    Decides (decider language presentation) language
  family : ∀ (language : DecisionLanguage) (presentation : NPPresentation language),
    EncodingAnchoredCausalLengthFamily wordEncoding.encode encodingBoolBool.encode
      (decider language presentation)
  upper : ∀ (language : DecisionLanguage) (presentation : NPPresentation language),
    UniformCausalLengthUpperBound (family language presentation)

/-- [proved-derived; formal-checked] An encoding-anchored causal compiler returns the existing
official uniform-verifier compiler without weakening its quantifiers. -/
def UniformEncodingAnchoredVerifierCompiler.toOfficial
    (compiler : UniformEncodingAnchoredVerifierCompiler) : UniformVerifierCompiler where
  decider := compiler.decider
  correct := compiler.correct
  polynomial := fun language presentation =>
    booleanFunctionInPolynomialTime_of_uniformCausalLengthUpperBound
      (compiler.family language presentation) (compiler.upper language presentation)

/-- [proved-derived; formal-checked] With the separately owed standard inclusion, the anchored
compiler reaches the literal equality proposition. -/
theorem pEqualsNP_of_uniformEncodingAnchoredVerifierCompiler
    (hPSubsetNP : PSubsetNP) (compiler : UniformEncodingAnchoredVerifierCompiler) :
    PEqualsNP :=
  pEqualsNP_of_uniformVerifierCompiler hPSubsetNP compiler.toOfficial

section Audit

#print axioms EncodingAnchoredCausalLengthFamily.toTM2ComputableInPolyTime
#print axioms EncodingAnchoredCausalLengthFamily.lowerExtent_le_outputSteps
#print axioms TowerTM2Anchor.towerClockLength_eq_outputSteps
#print axioms TowerTM2Anchor.towerBoundaryLength_eq_encodedLength
#print axioms TowerTM2Anchor.outputReconstructionLift
#print axioms booleanFunctionInPolynomialTime_of_uniformCausalLengthUpperBound
#print axioms verifierInPolynomialTime_of_uniformCausalLengthUpperBound
#print axioms EncodingAnchoredPDecision.inP
#print axioms UniformEncodingAnchoredVerifierCompiler.toOfficial
#print axioms pEqualsNP_of_uniformEncodingAnchoredVerifierCompiler

end Audit

end Soma.Holonics.Millennium.PVersusNPCausalLengthBridge
