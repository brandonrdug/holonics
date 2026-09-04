import ElementaryHolonics.Foundation.Holon
import ElementaryHolonics.Millennium.HodgeSmoothProjectiveReceiver

/-!
# The Hodge primitive cut as an elementary holonic interaction

`CycleLiftFibre` already retains every algebraic-cycle source over one rational Hodge receiver
face.  This file identifies that fibre with the preimage fibre of an actual `Holon`, then
uses the Hodge--Riemann sign as a polarized axis rather than storing reflexivity and
nondegeneracy as independent detector assumptions.

The resulting theorem is an exact cut, not a new surrogate conjecture: on every primitive
Lefschetz step, occupation of every nonzero target fibre of the source-bearing interaction holon
is equivalent to `PrimitiveLiftable`.  Consequently the universal Hodge conclusion follows from
one holonic fibre-occupation law at each step.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeHolonicPrimitiveCut

open Soma.Holonics
open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver

universe u v

/-! ## The cycle-class receiver is already a holon -/

/-- [definition] Every rational algebraic cycle is one occurrence whose outgoing and received
face is its rational Hodge cycle class.  The source occurrence is retained exactly. -/
def cycleClassHolon (D : Datum) :
    Holon D.CycleSpace D.rationalHodgeClasses D.rationalHodgeClasses where
  Occurrence := D.CycleSpace
  source cycle := cycle
  target cycle :=
    ⟨D.cycleClass.hom cycle, D.cycleClassesAreHodge ⟨cycle, rfl⟩⟩
  receive cycle :=
    ⟨D.cycleClass.hom cycle, D.cycleClassesAreHodge ⟨cycle, rfl⟩⟩

/-- [proved-derived; formal-checked] A `CycleLiftFibre` is exactly the preimage fibre of
the cycle-class holon.  Thus algebraicity is occupation of a source-bearing receiver fibre, not
mere membership in a range shadow. -/
def cycleClassHolonPreimageFibreEquiv (D : Datum)
    (hodgeClass : D.rationalHodgeClasses) :
    (cycleClassHolon D).PreimageFibre hodgeClass ≃
      CycleLiftFibre D hodgeClass where
  toFun carried :=
    ⟨carried.1, congrArg Subtype.val carried.2⟩
  invFun lift :=
    ⟨lift.1, Subtype.ext lift.2⟩
  left_inv carried := by
    cases carried
    rfl
  right_inv lift := by
    cases lift
    rfl

/-! ## Hodge--Riemann polarity removes independent detector axioms -/

/-- [definition] The two orientations of the primitive intersection axis.  The parity-dependent
Hodge--Riemann sign chooses one orientation; neither orientation is privileged. -/
inductive IntersectionPolarity
  | positive
  | negative
  deriving DecidableEq

namespace IntersectionPolarity

/-- The receiver coordinate after orienting the intersection axis. -/
def orient : IntersectionPolarity → ℚ → ℚ
  | positive, value => value
  | negative, value => -value

@[simp]
theorem orient_zero (polarity : IntersectionPolarity) : polarity.orient 0 = 0 := by
  cases polarity <;> rfl

end IntersectionPolarity

/-- [definition] The exact primitive polarization data supplied by Hodge--Riemann.

Strict positivity is stated only after choosing the parity orientation.  It implies all
nullity, reflexivity, and restricted-nondegeneracy facts used by the algebraic detector, so those
facts are not repeated as unrelated assumptions. -/
structure SignedDefinitePrimitivePolarization {lower upper : Datum}
    (step : PrimitiveHodgeStep lower upper) where
  finiteDimensional : FiniteDimensional ℚ step.Primitive
  intersection : LinearMap.BilinForm ℚ step.Primitive
  symmetric : intersection.IsSymm
  polarity : IntersectionPolarity
  signedPositive : ∀ primitive : step.Primitive, primitive ≠ 0 →
    0 < polarity.orient (intersection primitive primitive)

namespace SignedDefinitePrimitivePolarization

variable {lower upper : Datum} {step : PrimitiveHodgeStep lower upper}

/-- [proved-derived; formal-checked] A nonzero primitive direction cannot have null self-
interaction.  This is the nullity-of-the-null consequence of polarized positivity. -/
theorem selfPairing_ne_zero
    (polarization : SignedDefinitePrimitivePolarization step)
    (primitive : step.Primitive) (hprimitive : primitive ≠ 0) :
    polarization.intersection primitive primitive ≠ 0 := by
  intro hzero
  have hpositive := polarization.signedPositive primitive hprimitive
  rw [hzero, IntersectionPolarity.orient_zero] at hpositive
  exact (lt_irrefl 0 hpositive)

/-- [proved-derived; formal-checked] Signed definiteness descends to every subspace.  In
particular, the algebraic primitive subspace has nondegenerate restricted intersection form; this
deletes `algebraicNondegenerate` as an independent Hodge obligation. -/
theorem restrict_nondegenerate
    (polarization : SignedDefinitePrimitivePolarization step)
    (subspace : Submodule ℚ step.Primitive) :
    (polarization.intersection.restrict subspace).Nondegenerate := by
  constructor
  · intro primitive horthogonal
    apply Subtype.ext
    by_contra hnonzero
    have hvalueNonzero : (primitive : step.Primitive) ≠ 0 := by
      intro hvalue
      apply hnonzero
      have hzero : ((0 : subspace) : step.Primitive) = 0 := rfl
      exact hvalue.trans hzero.symm
    apply polarization.selfPairing_ne_zero primitive hvalueNonzero
    have hself := horthogonal primitive
    change polarization.intersection (primitive : step.Primitive)
      (primitive : step.Primitive) = 0 at hself
    exact hself
  · intro primitive horthogonal
    apply Subtype.ext
    by_contra hnonzero
    have hvalueNonzero : (primitive : step.Primitive) ≠ 0 := by
      intro hvalue
      apply hnonzero
      have hzero : ((0 : subspace) : step.Primitive) = 0 := rfl
      exact hvalue.trans hzero.symm
    apply polarization.selfPairing_ne_zero primitive hvalueNonzero
    have hself := horthogonal primitive
    change polarization.intersection (primitive : step.Primitive)
      (primitive : step.Primitive) = 0 at hself
    exact hself

end SignedDefinitePrimitivePolarization

/-! ## The source-bearing primitive interaction holon -/

/-- [definition] One algebraic primitive source occurrence interacting nontrivially with one
target primitive direction.  The source includes the complete cycle-lift fibre occurrence. -/
structure PrimitiveDetectionOccurrence {lower upper : Datum}
    {step : PrimitiveHodgeStep lower upper}
    (polarization : SignedDefinitePrimitivePolarization step) where
  algebraicPrimitive : step.Primitive
  sourceLift : CycleLiftFibre upper
    (algebraicPrimitive : upper.rationalHodgeClasses)
  targetPrimitive : step.Primitive
  interacts :
    polarization.intersection algebraicPrimitive targetPrimitive ≠ 0

/-- [definition] The primitive interaction as an elementary holon.  Its target reconstruction
fibre is the complete population of actual algebraic cycle sources which detect that primitive
receiver direction. -/
def primitiveDetectionHolon {lower upper : Datum}
    {step : PrimitiveHodgeStep lower upper}
    (polarization : SignedDefinitePrimitivePolarization step) :
    Holon upper.CycleSpace step.Primitive step.Primitive where
  Occurrence := PrimitiveDetectionOccurrence polarization
  source occurrence := occurrence.sourceLift.1
  target occurrence := occurrence.targetPrimitive
  receive occurrence := occurrence.targetPrimitive

/-- [definition] The exact conjectural interaction law: every nonzero primitive receiver face
has at least one source-bearing algebraic detection occurrence. -/
def DetectsEveryNonzero {lower upper : Datum}
    {step : PrimitiveHodgeStep lower upper}
    (polarization : SignedDefinitePrimitivePolarization step) : Prop :=
  ∀ primitive : step.Primitive, primitive ≠ 0 →
    Nonempty ((primitiveDetectionHolon polarization).PreimageFibre primitive)

namespace SignedDefinitePrimitivePolarization

variable {lower upper : Datum} {step : PrimitiveHodgeStep lower upper}

/-- [proved-derived; formal-checked] Holonic detection supplies the earlier source interaction
receiver.  Reflexivity and algebraic restricted nondegeneracy are derived from the single signed
polarization law. -/
def sourcePrimitiveAlgebraicInteraction
    (polarization : SignedDefinitePrimitivePolarization step)
    (detects : DetectsEveryNonzero polarization) :
    SourcePrimitiveAlgebraicInteraction step where
  finiteDimensional := polarization.finiteDimensional
  intersection := polarization.intersection
  reflexive := polarization.symmetric.isRefl
  algebraicNondegenerate :=
    polarization.restrict_nondegenerate (primitiveAlgebraicClasses step)
  detects := by
    intro primitive hprimitive
    obtain ⟨carried⟩ := detects primitive hprimitive
    refine ⟨carried.1.algebraicPrimitive, ⟨carried.1.sourceLift⟩, ?_⟩
    have htarget : carried.1.targetPrimitive = primitive := carried.2
    simpa only [htarget] using carried.1.interacts

/-- [proved-derived; formal-checked] Every occupied nonzero detector fibre constructs all
primitive algebraic cycle lifts. -/
theorem primitiveLiftable_of_detectsEveryNonzero
    (polarization : SignedDefinitePrimitivePolarization step)
    (detects : DetectsEveryNonzero polarization) :
    step.PrimitiveLiftable :=
  (polarization.sourcePrimitiveAlgebraicInteraction detects).primitiveLiftable

/-- [proved-derived; formal-checked] Conversely, a primitive cycle lift occupies its own
interaction fibre: signed definiteness makes its self-interaction nonzero. -/
theorem detectsEveryNonzero_of_primitiveLiftable
    (polarization : SignedDefinitePrimitivePolarization step)
    (primitiveLiftable : step.PrimitiveLiftable) :
    DetectsEveryNonzero polarization := by
  intro primitive hprimitive
  obtain ⟨sourceLift⟩ := primitiveLiftable primitive
  refine ⟨⟨⟨primitive, sourceLift, primitive,
    polarization.selfPairing_ne_zero primitive hprimitive⟩, rfl⟩⟩

/-- [proved-derived; formal-checked] The holonic detector law is exactly the primitive Hodge
algebraicity law under the standard signed-definite polarization.  No weaker proxy is introduced. -/
theorem detectsEveryNonzero_iff_primitiveLiftable
    (polarization : SignedDefinitePrimitivePolarization step) :
    DetectsEveryNonzero polarization ↔ step.PrimitiveLiftable :=
  ⟨polarization.primitiveLiftable_of_detectsEveryNonzero,
    polarization.detectsEveryNonzero_of_primitiveLiftable⟩

end SignedDefinitePrimitivePolarization

/-! ## Universal primitive-to-global composition -/

/-- [definition] The staircase reconstructed from source-indexed injective Lefschetz transports. -/
noncomputable def injectiveStaircase
    (Canonical : Realization → Prop)
    (baseConclusion : ∀ (R : Realization), Canonical R → (R.datum 0).Conclusion)
    (steps : ∀ (R : Realization), Canonical R → ∀ p : ℕ, InjectiveLefschetzStep R p)
    (R : Realization) (hR : Canonical R) : PrimitiveLefschetzStaircase R :=
  PrimitiveLefschetzStaircase.ofInjectiveSteps (baseConclusion R hR) (steps R hR)

/-- [proved-derived; formal-checked] Once the codimension-zero source and the injective
cycle/Hodge Lefschetz transports are supplied, the classical Hodge statement is exactly the
occupation of every nonzero primitive interaction fibre.

This is the official receiver cut in both directions.  The forward implication reconstructs a
detector occurrence from each algebraic primitive lift.  The reverse implication uses the same
source-bearing occurrences to return genuine rational algebraic cycles and then glues them through
the derived Lefschetz decomposition. -/
theorem hodge_iff_primitiveDetection
    (Canonical : Realization → Prop)
    (baseConclusion : ∀ (R : Realization), Canonical R → (R.datum 0).Conclusion)
    (steps : ∀ (R : Realization), Canonical R → ∀ p : ℕ,
      InjectiveLefschetzStep R p)
    (polarization : ∀ (R : Realization) (hR : Canonical R) (p : ℕ),
      SignedDefinitePrimitivePolarization
        (((injectiveStaircase Canonical baseConclusion steps R hR).step p))) :
    TheHodgeConjecture Canonical ↔
      ∀ (R : Realization) (hR : Canonical R) (p : ℕ),
        DetectsEveryNonzero (polarization R hR p) := by
  constructor
  · intro hodge R hR p
    let staircaseR := injectiveStaircase Canonical baseConclusion steps R hR
    apply (polarization R hR p).detectsEveryNonzero_of_primitiveLiftable
    exact (staircaseR.allConclusions_iff_allPrimitiveLiftable.mp (hodge R hR)) p
  · intro detects R hR
    let staircaseR := injectiveStaircase Canonical baseConclusion steps R hR
    apply staircaseR.allConclusions_iff_allPrimitiveLiftable.mpr
    intro p
    exact (polarization R hR p).primitiveLiftable_of_detectsEveryNonzero (detects R hR p)

/-- [proved-derived; formal-checked] A signed Hodge--Riemann polarization and occupation of every
nonzero primitive interaction fibre close the genuine smooth-projective Hodge receiver.  The
conjectural argument is now one exact holonic fibre law; all polarity and nondegeneracy machinery
is derived. -/
theorem theHodgeConjecture_of_holonicPrimitiveDetection
    (Canonical : Realization → Prop)
    (staircase : ∀ (R : Realization), Canonical R → PrimitiveLefschetzStaircase R)
    (polarization : ∀ (R : Realization) (hR : Canonical R) (p : ℕ),
      SignedDefinitePrimitivePolarization (((staircase R hR).step p)))
    (detects : ∀ (R : Realization) (hR : Canonical R) (p : ℕ),
      DetectsEveryNonzero (polarization R hR p)) :
    TheHodgeConjecture Canonical := by
  apply theHodgeConjecture_of_sourcePrimitiveAlgebraicInteractions Canonical staircase
  intro R hR p
  exact (polarization R hR p).sourcePrimitiveAlgebraicInteraction (detects R hR p)

section Audit

#print axioms cycleClassHolonPreimageFibreEquiv
#print axioms SignedDefinitePrimitivePolarization.selfPairing_ne_zero
#print axioms SignedDefinitePrimitivePolarization.restrict_nondegenerate
#print axioms SignedDefinitePrimitivePolarization.sourcePrimitiveAlgebraicInteraction
#print axioms SignedDefinitePrimitivePolarization.primitiveLiftable_of_detectsEveryNonzero
#print axioms SignedDefinitePrimitivePolarization.detectsEveryNonzero_of_primitiveLiftable
#print axioms SignedDefinitePrimitivePolarization.detectsEveryNonzero_iff_primitiveLiftable
#print axioms hodge_iff_primitiveDetection
#print axioms theHodgeConjecture_of_holonicPrimitiveDetection

end Audit

end Soma.Holonics.Millennium.HodgeHolonicPrimitiveCut
