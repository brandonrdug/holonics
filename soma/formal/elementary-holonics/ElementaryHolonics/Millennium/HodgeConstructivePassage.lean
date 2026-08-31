import ElementaryHolonics.Foundation.TransportLift
import ElementaryHolonics.Geometry.DivisorAtlas
import ElementaryHolonics.Millennium.HodgeConjecture
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# A constructive Hodge passage: quotient nullity returns an actual cycle fibre

The official Hodge receiver asks whether every rational Hodge class lies in the rational range of
the cycle-class map.  Membership in that range is still only an existential shadow unless the
source population is retained.  This file returns the complete population explicitly:

* `CycleLiftFibre D h` contains every rational algebraic cycle combination whose class is `h`;
* `hodgeConclusion_iff_every_cycleLiftFibre_nonempty` replaces range equality by exact source
  reconstruction for every rational Hodge occurrence;
* every inhabited fibre is a translate of the kernel of the cycle-class map, so rational
  equivalence of cycles is retained rather than silently inverted;
* `RankOneCodimensionOneRealization` closes the Hodge conclusion from a nonzero algebraic
  generator and rank one of the rational Hodge carrier.  Surjectivity is derived, not assumed.

The last theorem applies in particular to any *officially admitted* codimension-one realization
whose rational `(1,1)` carrier has rank one and whose declared nonzero generator is supplied by a
divisor cycle.  This file does not pretend that an arbitrary `Datum` is a smooth projective complex
surface; that source-specific geometric admission remains a separate port.

Every theorem is exact.  No numerical approximation or chosen inverse is used.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeConstructivePassage

open Soma.Holonics.Foundation
open Soma.Holonics.Millennium.HodgeConjecture

universe u v

/-- [definition] All cycle combinations returning one addressed rational Hodge class. -/
abbrev CycleLiftFibre (D : Datum) (hodgeClass : D.rationalHodgeClasses) :=
  Lift.ReconstructionFibre D.cycleClass.hom.toAddMonoidHom (hodgeClass : D.Cohomology)

/-- [proved-derived; formal-checked] A cycle lift exists exactly when the class is algebraic.
The left side retains the antecedent population; the right side is its range receiver. -/
theorem cycleLiftFibre_nonempty_iff_mem_algebraicSpan
    (D : Datum) (hodgeClass : D.rationalHodgeClasses) :
    Nonempty (CycleLiftFibre D hodgeClass) ↔
      (hodgeClass : D.Cohomology) ∈ D.algebraicSpan := by
  rw [Lift.nonempty_iff_mem_range]
  rfl

/-- [proved-derived; formal-checked] The Hodge conclusion is equivalent to constructing an exact
cycle antecedent for every rational Hodge occurrence.  This is the local-to-global target in a
form that returns sources rather than merely zero in a quotient. -/
theorem hodgeConclusion_iff_every_cycleLiftFibre_nonempty (D : Datum) :
    D.Conclusion ↔ ∀ hodgeClass : D.rationalHodgeClasses,
      Nonempty (CycleLiftFibre D hodgeClass) := by
  constructor
  · intro hConclusion hodgeClass
    rw [cycleLiftFibre_nonempty_iff_mem_algebraicSpan]
    rw [← hConclusion]
    exact hodgeClass.property
  · intro hLifts
    apply le_antisymm
    · intro cohomologyClass hHodge
      obtain ⟨lift⟩ := hLifts ⟨cohomologyClass, hHodge⟩
      exact ⟨lift.1, lift.2⟩
    · exact D.cycleClassesAreHodge

/-- [proved-derived; formal-checked] Once one algebraic antecedent is known, the complete family
of antecedents is exactly the kernel of the cycle-class receiver.  This is the retained ambiguity
that an inverse or one selected divisor would delete. -/
def cycleLiftFibreEquivCycleKernel (D : Datum)
    {hodgeClass : D.rationalHodgeClasses} (base : CycleLiftFibre D hodgeClass) :
    CycleLiftFibre D hodgeClass ≃ D.cycleClass.hom.toAddMonoidHom.ker :=
  Lift.fibreEquivKernel D.cycleClass.hom.toAddMonoidHom base

/-- [definition] The exact data that close an admitted rank-one codimension-one Hodge carrier.
The generator is a source cycle, not a cohomology class asserted to be algebraic after the fact. -/
structure RankOneCodimensionOneRealization (D : Datum) where
  codimension_one : D.codimension = 1
  generatorCycle : D.CycleSpace
  generatorClass_ne_zero : D.cycleClass.hom generatorCycle ≠ 0
  rationalHodgeRank : Module.finrank ℚ D.rationalHodgeClasses = 1

namespace RankOneCodimensionOneRealization

variable {D : Datum}

/-- The class of the declared generator, situated in the rational Hodge carrier by the easy
direction of the cycle-class theorem. -/
def generatorHodgeClass (R : RankOneCodimensionOneRealization D) :
    D.rationalHodgeClasses :=
  ⟨D.cycleClass.hom R.generatorCycle,
    D.cycleClassesAreHodge ⟨R.generatorCycle, rfl⟩⟩

theorem generatorHodgeClass_ne_zero (R : RankOneCodimensionOneRealization D) :
    R.generatorHodgeClass ≠ 0 := by
  intro hzero
  apply R.generatorClass_ne_zero
  exact congrArg Subtype.val hzero

/-- [proved-derived; formal-checked] Every rational Hodge class is a scalar multiple of the
returned nonzero algebraic generator. -/
theorem everyHodgeClass_is_smul_generator
    (R : RankOneCodimensionOneRealization D)
    (hodgeClass : D.rationalHodgeClasses) :
    ∃ coefficient : ℚ, coefficient • R.generatorHodgeClass = hodgeClass :=
  exists_smul_eq_of_finrank_eq_one R.rationalHodgeRank
    R.generatorHodgeClass_ne_zero hodgeClass

/-- One exact coefficient witnessing the rank-one decomposition.  Choosing a coordinate is an
additional construction; the complete cycle fibre below still records every alternative source. -/
noncomputable def generatorCoefficient
    (R : RankOneCodimensionOneRealization D)
    (hodgeClass : D.rationalHodgeClasses) : ℚ :=
  (R.everyHodgeClass_is_smul_generator hodgeClass).choose

theorem generatorCoefficient_spec
    (R : RankOneCodimensionOneRealization D)
    (hodgeClass : D.rationalHodgeClasses) :
    R.generatorCoefficient hodgeClass • R.generatorHodgeClass = hodgeClass :=
  (R.everyHodgeClass_is_smul_generator hodgeClass).choose_spec

/-- [proved-derived; formal-checked] The scalar multiple is reconstructed by the same scalar
multiple of the source cycle, giving an explicit inhabitant of the cycle lift fibre. -/
def cycleLift (R : RankOneCodimensionOneRealization D)
    (hodgeClass : D.rationalHodgeClasses) : CycleLiftFibre D hodgeClass := by
  refine ⟨R.generatorCoefficient hodgeClass • R.generatorCycle, ?_⟩
  have hvalues := congrArg Subtype.val (R.generatorCoefficient_spec hodgeClass)
  simpa [generatorHodgeClass] using hvalues

/-- [proved-derived; formal-checked] A rank-one codimension-one realization with one nonzero
algebraic cycle satisfies the Hodge conclusion.  The proof constructs a source cycle for every
rational Hodge class; it does not assume surjectivity of the cycle-class map. -/
theorem hodgeConclusion (R : RankOneCodimensionOneRealization D) : D.Conclusion := by
  rw [hodgeConclusion_iff_every_cycleLiftFibre_nonempty]
  intro hodgeClass
  exact ⟨R.cycleLift hodgeClass⟩

/-- [proved-derived; formal-checked] Any declared official family restricted to these rank-one
codimension-one realizations is already inhabited at the official Hodge receiver. -/
theorem officialConclusion (Official : Datum → Prop)
    (R : RankOneCodimensionOneRealization D) (hOfficial : Official D) :
    Official D ∧ D.Conclusion :=
  ⟨hOfficial, R.hodgeConclusion⟩

end RankOneCodimensionOneRealization

/-- [proved-derived; formal-checked] The official Hodge statement is proved on the complete
subfamily of admitted rank-one codimension-one realizations.  This is a genuine quantified family
theorem; it does not assert that every official Hodge datum belongs to that subfamily. -/
theorem theHodgeConjectureIn_rankOneCodimensionOne
    (Official : Datum → Prop) :
    TheHodgeConjectureIn
      (fun D ↦ Official D ∧ Nonempty (RankOneCodimensionOneRealization D)) := by
  intro D admitted
  exact admitted.2.some.hodgeConclusion

/-! ## Finite local-to-global cycle reconstruction -/

/-- [definition] A finite basis of rational Hodge occurrences, each accompanied by an addressed
source cycle returning it.  No global surjectivity field is included. -/
structure FiniteHodgeBasisRealization (D : Datum) (Index : Type*) [Fintype Index] where
  basis : Module.Basis Index ℚ D.rationalHodgeClasses
  basisCycle : Index → D.CycleSpace
  basisCycle_returns : ∀ index,
    D.cycleClass.hom (basisCycle index) = (basis index : D.Cohomology)

namespace FiniteHodgeBasisRealization

variable {D : Datum} {Index : Type*} [Fintype Index]

/-- [proved-derived; formal-checked] Local basis-cycle occurrences glue by the exact rational
coefficients of a Hodge occurrence.  This is the constructed global source cycle. -/
noncomputable def reconstructedCycle
    (R : FiniteHodgeBasisRealization D Index)
    (hodgeClass : D.rationalHodgeClasses) : D.CycleSpace :=
  ∑ index, (R.basis.repr hodgeClass index) • R.basisCycle index

/-- [proved-derived; formal-checked] Applying the cycle-class receiver after reconstruction
returns the original Hodge occurrence.  This is the local-to-global commuting square. -/
theorem reconstructedCycle_returns
    (R : FiniteHodgeBasisRealization D Index)
    (hodgeClass : D.rationalHodgeClasses) :
    D.cycleClass.hom (R.reconstructedCycle hodgeClass) =
      (hodgeClass : D.Cohomology) := by
  rw [reconstructedCycle, map_sum]
  simp_rw [map_smul, R.basisCycle_returns]
  calc
    (∑ index, (R.basis.repr hodgeClass index) •
        (R.basis index : D.Cohomology)) =
        D.rationalHodgeClasses.subtype
          (∑ index, (R.basis.repr hodgeClass index) • R.basis index) := by
            rw [map_sum]
            simp only [map_smul]
            apply Finset.sum_congr rfl
            intro index _
            rfl
    _ = (hodgeClass : D.Cohomology) := by
      rw [R.basis.sum_repr]
      rfl

/-- [proved-derived; formal-checked] The reconstructed global cycle inhabits the complete lift
fibre. -/
noncomputable def cycleLift
    (R : FiniteHodgeBasisRealization D Index)
    (hodgeClass : D.rationalHodgeClasses) : CycleLiftFibre D hodgeClass :=
  ⟨R.reconstructedCycle hodgeClass, R.reconstructedCycle_returns hodgeClass⟩

/-- [proved-derived; formal-checked] Finitely many source cycles on a Hodge basis close the full
Hodge conclusion.  The theorem is not dimension-specific: rank one above is its one-pivot case. -/
theorem hodgeConclusion (R : FiniteHodgeBasisRealization D Index) : D.Conclusion := by
  rw [hodgeConclusion_iff_every_cycleLiftFibre_nonempty]
  intro hodgeClass
  exact ⟨R.cycleLift hodgeClass⟩

/-- [proved-derived; formal-checked] The official receiver is inhabited for every admitted datum
carrying such a returned cycle basis. -/
theorem officialConclusion (Official : Datum → Prop)
    (R : FiniteHodgeBasisRealization D Index) (hOfficial : Official D) :
    Official D ∧ D.Conclusion :=
  ⟨hOfficial, R.hodgeConclusion⟩

end FiniteHodgeBasisRealization

/-! ## Primitive-to-global Hodge transport

The finite carriers above prove the conjectural conclusion once a complete algebraic basis has
already been returned.  The following passage removes that global-basis obligation.  It is the
algebraic skeleton of a Lefschetz staircase: an upper Hodge occurrence is split into a primitive
remainder and the transport of one lower occurrence.  If lower occurrences and primitive
remainders have cycle antecedents, their sum is an upper antecedent.  No choice of global basis and
no dimension count enters.

For an actual smooth projective variety, `cycleTransport` is to be realized by intersection or cup
product with a hyperplane class, `hodgeTransport` is its restriction to rational Hodge classes, and
`Primitive` is the kernel selected by the complementary Lefschetz operator.  Constructing those
source-specific maps and proving primitive liftability remain visible obligations; this structure
does not assert them.
-/

/-- [definition] One exact primitive decomposition step between two Hodge data.

The commuting square says that transporting a source cycle and then taking its cycle class agrees
with transporting the lower Hodge class.  `decompose` is deliberately a returned population rather
than a dimension equality: every upper occurrence comes with a primitive remainder and a lower
occurrence whose transported sum reconstructs it. -/
structure PrimitiveHodgeStep (lower upper : Datum) where
  cycleTransport : lower.CycleSpace →ₗ[ℚ] upper.CycleSpace
  hodgeTransport : lower.rationalHodgeClasses →ₗ[ℚ] upper.rationalHodgeClasses
  cycleClass_commutes : ∀ cycle : lower.CycleSpace,
    upper.cycleClass.hom (cycleTransport cycle) =
      (hodgeTransport
        ⟨lower.cycleClass.hom cycle,
          lower.cycleClassesAreHodge ⟨cycle, rfl⟩⟩ : upper.Cohomology)
  Primitive : Submodule ℚ upper.rationalHodgeClasses
  decompose : ∀ hodgeClass : upper.rationalHodgeClasses,
    ∃ primitive : Primitive, ∃ lowerClass : lower.rationalHodgeClasses,
      (primitive : upper.rationalHodgeClasses) + hodgeTransport lowerClass = hodgeClass

namespace PrimitiveHodgeStep

variable {lower upper : Datum}

/-- [definition] The exact source-specific residue left by a primitive decomposition step: every
primitive Hodge occurrence must return an algebraic cycle antecedent. -/
def PrimitiveLiftable (step : PrimitiveHodgeStep lower upper) : Prop :=
  ∀ primitive : step.Primitive,
    Nonempty (CycleLiftFibre upper (primitive : upper.rationalHodgeClasses))

/-- [definition] The upper Hodge directions already supplied by the lower staircase current.
This is the exact receiver shadow of coarse transport; it contains no new primitive source. -/
def transportedLowerClasses (step : PrimitiveHodgeStep lower upper) :
    Submodule ℚ upper.rationalHodgeClasses :=
  LinearMap.range step.hodgeTransport

/-- [proved-derived; formal-checked] When the primitive and transported-lower directions meet
only at zero, no nonzero primitive occurrence can be manufactured by repeating the lower
transport.  This is the universal stop condition for degree-by-degree Lefschetz churn: a new
algebraic source current is necessary exactly on the primitive side of the cut. -/
theorem primitive_mem_transportedLowerClasses_iff_eq_zero
    (step : PrimitiveHodgeStep lower upper)
    (transverse : step.Primitive ⊓ step.transportedLowerClasses = ⊥)
    (primitive : step.Primitive) :
    (primitive : upper.rationalHodgeClasses) ∈ step.transportedLowerClasses ↔
      primitive = 0 := by
  constructor
  · intro transported
    have inIntersection :
        (primitive : upper.rationalHodgeClasses) ∈
          step.Primitive ⊓ step.transportedLowerClasses :=
      ⟨primitive.property, transported⟩
    rw [transverse] at inIntersection
    apply Subtype.ext
    simpa using inIntersection
  · rintro rfl
    exact Submodule.zero_mem _

/-- [proved-derived; formal-checked] The corresponding nonmembership form makes the obstruction
directly consumable by route audits. -/
theorem nonzero_primitive_not_mem_transportedLowerClasses
    (step : PrimitiveHodgeStep lower upper)
    (transverse : step.Primitive ⊓ step.transportedLowerClasses = ⊥)
    (primitive : step.Primitive) (nonzero : primitive ≠ 0) :
    (primitive : upper.rationalHodgeClasses) ∉ step.transportedLowerClasses := by
  intro transported
  exact nonzero
    ((step.primitive_mem_transportedLowerClasses_iff_eq_zero transverse primitive).mp
      transported)

/-- [proved-derived; formal-checked] A lower Hodge conclusion and algebraic liftability of every
primitive remainder construct the upper Hodge conclusion.

This is the universal local-to-global cut: the proof returns the upper source cycle as the sum of
the primitive source and the transported lower source.  The conclusion is not assumed as a
surjectivity field, and no finite basis is selected. -/
theorem hodgeConclusion_of_lower_of_primitiveLiftable
    (step : PrimitiveHodgeStep lower upper)
    (lowerConclusion : lower.Conclusion)
    (primitiveLiftable : step.PrimitiveLiftable) :
    upper.Conclusion := by
  rw [hodgeConclusion_iff_every_cycleLiftFibre_nonempty]
  intro upperClass
  obtain ⟨primitive, lowerClass, decomposition⟩ := step.decompose upperClass
  obtain ⟨primitiveLift⟩ := primitiveLiftable primitive
  obtain ⟨lowerLift⟩ :=
    (hodgeConclusion_iff_every_cycleLiftFibre_nonempty lower).mp lowerConclusion lowerClass
  refine ⟨⟨primitiveLift.1 + step.cycleTransport lowerLift.1, ?_⟩⟩
  have lowerClassIdentity :
      (⟨lower.cycleClass.hom lowerLift.1,
          lower.cycleClassesAreHodge ⟨lowerLift.1, rfl⟩⟩ :
        lower.rationalHodgeClasses) = lowerClass := by
    apply Subtype.ext
    exact lowerLift.2
  have transportedLowerReturns :
      upper.cycleClass.hom (step.cycleTransport lowerLift.1) =
        (step.hodgeTransport lowerClass : upper.Cohomology) := by
    rw [step.cycleClass_commutes]
    rw [lowerClassIdentity]
  have primitiveReturns :
      upper.cycleClass.hom primitiveLift.1 =
        ((primitive : upper.rationalHodgeClasses) : upper.Cohomology) := by
    exact primitiveLift.2
  calc
    upper.cycleClass.hom (primitiveLift.1 + step.cycleTransport lowerLift.1) =
        upper.cycleClass.hom primitiveLift.1 +
          upper.cycleClass.hom (step.cycleTransport lowerLift.1) := by
            rw [map_add]
    _ = ((primitive : step.Primitive) : upper.rationalHodgeClasses) +
          step.hodgeTransport lowerClass := by
            rw [primitiveReturns, transportedLowerReturns]
    _ = (upperClass : upper.Cohomology) := by
      exact congrArg Subtype.val decomposition

/-- [proved-derived; formal-checked] Primitive liftability is the only new source obligation in a
primitive Hodge step once the lower conclusion is known.  This equivalence prevents the staircase
composition from being mistaken for the unresolved primitive algebraicity theorem. -/
theorem hodgeConclusion_iff_primitiveLiftable_of_lower
    (step : PrimitiveHodgeStep lower upper)
    (lowerConclusion : lower.Conclusion) :
    upper.Conclusion ↔ step.PrimitiveLiftable := by
  constructor
  · intro upperConclusion primitive
    exact
      (hodgeConclusion_iff_every_cycleLiftFibre_nonempty upper).mp upperConclusion
        (primitive : upper.rationalHodgeClasses)
  · exact step.hodgeConclusion_of_lower_of_primitiveLiftable lowerConclusion

end PrimitiveHodgeStep

/-- [proved-derived; formal-checked] Exact primitive lifts propagate through every finite prefix of
a Hodge staircase.  The induction composes actual cycle-producing steps; it does not re-enumerate
an upper basis or assume a final surjectivity statement. -/
theorem primitiveHodgeStaircaseConclusion
    (datum : ℕ → Datum)
    (step : ∀ codimension,
      PrimitiveHodgeStep (datum codimension) (datum (codimension + 1)))
    (baseConclusion : (datum 0).Conclusion)
    (primitiveLiftable : ∀ codimension, (step codimension).PrimitiveLiftable) :
    ∀ codimension, (datum codimension).Conclusion := by
  intro codimension
  induction codimension with
  | zero => exact baseConclusion
  | succ codimension lowerConclusion =>
      exact (step codimension).hodgeConclusion_of_lower_of_primitiveLiftable
        lowerConclusion (primitiveLiftable codimension)

/-! ## The intersection detector cut

Primitive decomposition isolates the new source class, but a direct cycle antecedent is not the
only exact receiver which can close it.  Under the source-specific polarized intersection form,
the Hodge conclusion is equivalent to the absence of a nonzero Hodge direction invisible to every
algebraic cycle.  This is the interaction form of the conjecture: a returned difference is zero
exactly when the complete algebraic population cannot distinguish it.
-/

/-- [definition] Algebraic cycle classes regarded inside the rational Hodge carrier.  The comap
retains the proof that the same cohomology occurrence lies in both submodules. -/
def algebraicHodgeClasses (D : Datum) : Submodule ℚ D.rationalHodgeClasses :=
  D.algebraicSpan.comap D.rationalHodgeClasses.subtype

/-- [proved-derived; formal-checked] Filling the algebraic Hodge submodule is exactly the Hodge
conclusion; no dimension comparison is used. -/
theorem algebraicHodgeClasses_eq_top_iff_hodgeConclusion (D : Datum) :
    algebraicHodgeClasses D = ⊤ ↔ D.Conclusion := by
  constructor
  · intro htop
    apply le_antisymm
    · intro cohomologyClass hHodge
      have hmember :
          (⟨cohomologyClass, hHodge⟩ : D.rationalHodgeClasses) ∈
            algebraicHodgeClasses D := by
        rw [htop]
        exact Submodule.mem_top
      exact hmember
    · exact D.cycleClassesAreHodge
  · intro hConclusion
    apply top_unique
    intro hodgeClass _
    change (hodgeClass : D.Cohomology) ∈ D.algebraicSpan
    rw [← hConclusion]
    exact hodgeClass.property

/-- [definition] The source-specific polarized intersection receiver needed for the detector cut.

`algebraicNondegenerate` is not silently inferred from a bare bilinear form.  In a classical
smooth-projective realization it is supplied by the polarized Hodge structure on the algebraic
substructure. -/
structure PolarizedHodgeReceiver (D : Datum) where
  finiteDimensional : FiniteDimensional ℚ D.rationalHodgeClasses
  intersection : LinearMap.BilinForm ℚ D.rationalHodgeClasses
  reflexive : intersection.IsRefl
  nondegenerate : intersection.Nondegenerate
  algebraicNondegenerate :
    (intersection.restrict (algebraicHodgeClasses D)).Nondegenerate

namespace PolarizedHodgeReceiver

variable {D : Datum}

/-- [definition] Every nonzero rational Hodge occurrence is detected by interaction with an
actual algebraic cycle class.  The witness remains an addressed member of the algebraic Hodge
submodule rather than an untyped scalar pairing. -/
def AlgebraicallyDetected (receiver : PolarizedHodgeReceiver D) : Prop :=
  ∀ hodgeClass : D.rationalHodgeClasses, hodgeClass ≠ 0 →
    ∃ algebraicClass : algebraicHodgeClasses D,
      receiver.intersection algebraicClass hodgeClass ≠ 0

/-- [proved-derived; formal-checked] Complete algebraic detection is exactly nullity of the
algebraic orthogonal receiver. -/
theorem algebraicallyDetected_iff_orthogonal_eq_bot
    (receiver : PolarizedHodgeReceiver D) :
    receiver.AlgebraicallyDetected ↔
      receiver.intersection.orthogonal (algebraicHodgeClasses D) = ⊥ := by
  constructor
  · intro detected
    apply eq_bot_iff.mpr
    intro hodgeClass horthogonal
    by_contra hnonzero
    obtain ⟨algebraicClass, detectedPairing⟩ := detected hodgeClass hnonzero
    exact detectedPairing (horthogonal algebraicClass algebraicClass.property)
  · intro horthogonal hodgeClass hnonzero
    by_contra hundetected
    have hmember :
        hodgeClass ∈ receiver.intersection.orthogonal (algebraicHodgeClasses D) := by
      intro algebraicClass halgebraic
      by_contra hpairing
      exact hundetected ⟨⟨algebraicClass, halgebraic⟩, hpairing⟩
    rw [horthogonal] at hmember
    exact hnonzero hmember

/-- [proved-derived; formal-checked] For a polarized finite Hodge receiver, the Hodge conjectural
conclusion is equivalent to the exact interaction law that every nonzero Hodge direction meets an
algebraic cycle class nontrivially.

This theorem turns the primitive residual into a firing target for the holonic interaction and
positivity arsenal: constructing one such algebraic detector for every nonzero primitive class
closes the cycle-source conclusion, while an undetected nonzero class is an exact obstruction. -/
theorem hodgeConclusion_iff_algebraicallyDetected
    (receiver : PolarizedHodgeReceiver D) :
    D.Conclusion ↔ receiver.AlgebraicallyDetected := by
  letI := receiver.finiteDimensional
  rw [← algebraicHodgeClasses_eq_top_iff_hodgeConclusion]
  rw [receiver.algebraicallyDetected_iff_orthogonal_eq_bot]
  constructor
  · intro htop
    rw [htop]
    exact receiver.intersection.orthogonal_top_eq_bot receiver.nondegenerate
  · intro horthogonal
    exact receiver.intersection.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
      receiver.reflexive receiver.algebraicNondegenerate horthogonal

end PolarizedHodgeReceiver

/-! ## Primitive algebraic interaction closes one staircase step -/

/-- [definition] Algebraic classes which also occupy the primitive remainder of one Hodge step,
retained as a submodule of the primitive carrier itself. -/
def primitiveAlgebraicClasses {lower upper : Datum}
    (step : PrimitiveHodgeStep lower upper) : Submodule ℚ step.Primitive :=
  (algebraicHodgeClasses upper).comap step.Primitive.subtype

/-- [definition] The polarized interaction receiver on the actual primitive remainder.  This is
strictly smaller than asking for cycles representing every upper Hodge class. -/
structure PrimitiveAlgebraicInteraction {lower upper : Datum}
    (step : PrimitiveHodgeStep lower upper) where
  finiteDimensional : FiniteDimensional ℚ step.Primitive
  intersection : LinearMap.BilinForm ℚ step.Primitive
  reflexive : intersection.IsRefl
  algebraicNondegenerate :
    (intersection.restrict (primitiveAlgebraicClasses step)).Nondegenerate
  detects : ∀ primitive : step.Primitive, primitive ≠ 0 →
    ∃ algebraicPrimitive : primitiveAlgebraicClasses step,
      intersection algebraicPrimitive primitive ≠ 0

namespace PrimitiveAlgebraicInteraction

variable {lower upper : Datum} {step : PrimitiveHodgeStep lower upper}

/-- [proved-derived; formal-checked] Complete nonzero interaction makes the algebraic primitive
population fill the primitive carrier.  The proof is the exact nullity-of-the-null step: an
undetected occurrence lies in the orthogonal kernel; detection makes that kernel zero; polarized
nondegeneracy then forces the algebraic population to be the whole primitive space. -/
theorem primitiveAlgebraicClasses_eq_top
    (interaction : PrimitiveAlgebraicInteraction step) :
    primitiveAlgebraicClasses step = ⊤ := by
  letI := interaction.finiteDimensional
  have horthogonal :
      interaction.intersection.orthogonal (primitiveAlgebraicClasses step) = ⊥ := by
    apply eq_bot_iff.mpr
    intro primitive horthogonal
    by_contra hnonzero
    obtain ⟨algebraicPrimitive, detectedPairing⟩ := interaction.detects primitive hnonzero
    exact detectedPairing
      (horthogonal algebraicPrimitive algebraicPrimitive.property)
  exact interaction.intersection.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
    interaction.reflexive interaction.algebraicNondegenerate horthogonal

/-- [proved-derived; formal-checked] The interaction receiver constructs a cycle lift for every
primitive remainder.  No cycle lift is stored in the receiver: it is derived from the fact that
the primitive occurrence has been forced into the actual cycle-class range. -/
theorem primitiveLiftable
    (interaction : PrimitiveAlgebraicInteraction step) :
    step.PrimitiveLiftable := by
  intro primitive
  rw [cycleLiftFibre_nonempty_iff_mem_algebraicSpan]
  have hmember : primitive ∈ primitiveAlgebraicClasses step := by
    rw [interaction.primitiveAlgebraicClasses_eq_top]
    exact Submodule.mem_top
  exact hmember

/-- [proved-derived; formal-checked] One polarized primitive interaction law, together with the
lower Hodge conclusion, closes the upper Hodge conclusion and returns its source cycles through
the primitive transport theorem. -/
theorem hodgeConclusion
    (interaction : PrimitiveAlgebraicInteraction step)
    (lowerConclusion : lower.Conclusion) :
    upper.Conclusion :=
  step.hodgeConclusion_of_lower_of_primitiveLiftable
    lowerConclusion interaction.primitiveLiftable

end PrimitiveAlgebraicInteraction

section Audit

#print axioms cycleLiftFibre_nonempty_iff_mem_algebraicSpan
#print axioms hodgeConclusion_iff_every_cycleLiftFibre_nonempty
#print axioms cycleLiftFibreEquivCycleKernel
#print axioms RankOneCodimensionOneRealization.everyHodgeClass_is_smul_generator
#print axioms RankOneCodimensionOneRealization.generatorCoefficient
#print axioms RankOneCodimensionOneRealization.generatorCoefficient_spec
#print axioms RankOneCodimensionOneRealization.cycleLift
#print axioms RankOneCodimensionOneRealization.hodgeConclusion
#print axioms RankOneCodimensionOneRealization.officialConclusion
#print axioms theHodgeConjectureIn_rankOneCodimensionOne
#print axioms FiniteHodgeBasisRealization.reconstructedCycle
#print axioms FiniteHodgeBasisRealization.reconstructedCycle_returns
#print axioms FiniteHodgeBasisRealization.cycleLift
#print axioms FiniteHodgeBasisRealization.hodgeConclusion
#print axioms FiniteHodgeBasisRealization.officialConclusion
#print axioms PrimitiveHodgeStep.hodgeConclusion_of_lower_of_primitiveLiftable
#print axioms PrimitiveHodgeStep.hodgeConclusion_iff_primitiveLiftable_of_lower
#print axioms PrimitiveHodgeStep.primitive_mem_transportedLowerClasses_iff_eq_zero
#print axioms PrimitiveHodgeStep.nonzero_primitive_not_mem_transportedLowerClasses
#print axioms primitiveHodgeStaircaseConclusion
#print axioms algebraicHodgeClasses_eq_top_iff_hodgeConclusion
#print axioms PolarizedHodgeReceiver.algebraicallyDetected_iff_orthogonal_eq_bot
#print axioms PolarizedHodgeReceiver.hodgeConclusion_iff_algebraicallyDetected
#print axioms PrimitiveAlgebraicInteraction.primitiveAlgebraicClasses_eq_top
#print axioms PrimitiveAlgebraicInteraction.primitiveLiftable
#print axioms PrimitiveAlgebraicInteraction.hodgeConclusion

end Audit

end Soma.Holonics.Millennium.HodgeConstructivePassage
