import ElementaryHolonics.Millennium.HodgeHolonicPrimitiveCut
import Mathlib.RepresentationTheory.Irreducible

/-!
# Monodromy propagation across one primitive Hodge block

The pointwise primitive detector in `HodgeHolonicPrimitiveCut` is exact but expensive: it asks for
one source-bearing algebraic interaction at every nonzero primitive receiver occurrence.  A
geometric family carries more structure.  Parallel transport around its loops acts on primitive
cohomology, and transported algebraic cycles remain algebraic.

This file proves the resulting local-to-global law for an explicitly Hodge-preserving source
action.  Ordinary Gauss--Manin monodromy need not preserve a fixed Hodge subspace, so the structure
does not infer such an action from the word "monodromy."  It retains group actions both on the
primitive Hodge receiver and on actual algebraic-cycle sources, plus their cycle-class square.  If
the primitive action is irreducible and one nonzero primitive class has an actual algebraic-cycle
source, then the orbit-generated algebraic population is the entire primitive carrier.  Thus one
occupied seed fibre replaces pointwise detector occupation on that irreducible block.

The theorem does not assume the Hodge conclusion.  It returns `PrimitiveLiftable`, then composes
with the existing signed-polarization and Lefschetz staircase passages.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeMonodromyPrimitivePropagation

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver
open Soma.Holonics.Millennium.HodgeHolonicPrimitiveCut

universe u uLowerCycle uLowerCohomology uUpperCycle uUpperCohomology

/-- [definition] One source-bearing monodromy system on a primitive Hodge step.

`cycleAction` and `cycleClass_commutes` are the geometric transport law: continuation around any
admitted Hodge-preserving loop acts on actual cycle sources and commutes with their primitive
receiver.  `source_transport` is derived from that square.  `seed` retains an actual algebraic-
cycle reconstruction fibre, not merely a nonzero vector or a range-membership shadow. -/
structure PrimitiveMonodromySystem {lower upper : Datum}
    (step : PrimitiveHodgeStep lower upper) where
  Monodromy : Type u
  [group : Group Monodromy]
  /-- The admitted loops act on the primitive Hodge receiver.  For geometric variation this
  explicitly restricts to loops which preserve the addressed Hodge locus; ordinary ambient
  Gauss--Manin monodromy does not supply this field automatically. -/
  action : Representation ℚ Monodromy step.Primitive
  irreducible : Representation.IsIrreducible action
  /-- The same loops act on actual algebraic-cycle sources. -/
  cycleAction : Representation ℚ Monodromy upper.CycleSpace
  /-- The source action and primitive Hodge action meet in the genuine cycle-class receiver. -/
  cycleClass_commutes : ∀ loop (primitive : step.Primitive)
    (sourceLift : CycleLiftFibre upper
      (primitive : upper.rationalHodgeClasses)),
    upper.cycleClass.hom (cycleAction loop sourceLift.1) =
      (((action loop primitive : step.Primitive) :
        upper.rationalHodgeClasses) : upper.Cohomology)
  seed : ∃ primitive : step.Primitive, primitive ≠ 0 ∧
    Nonempty (CycleLiftFibre upper
      (primitive : upper.rationalHodgeClasses))

attribute [instance] PrimitiveMonodromySystem.group

/-- [definition] A source-bearing orbit cover of a primitive Hodge step.

This is the reducible counterpart of `PrimitiveMonodromySystem`.  It does not ask the complete
primitive representation to be irreducible.  Instead it retains a population of algebraic seeds,
one actual cycle-source action with its commuting cycle-class square, and the exact statement that
the transported occurrences linearly generate the receiver.

The seed type is intentionally not assumed finite: finiteness, block multiplicity, and a chosen
decomposition are receiver data, not part of the local-to-global law. -/
structure PrimitiveOrbitSourceCover {lower upper : Datum}
    (step : PrimitiveHodgeStep lower upper) where
  Monodromy : Type u
  [group : Group Monodromy]
  action : Representation ℚ Monodromy step.Primitive
  cycleAction : Representation ℚ Monodromy upper.CycleSpace
  Seed : Type u
  seed : Seed → step.Primitive
  seedLift : ∀ index, CycleLiftFibre upper
    (seed index : upper.rationalHodgeClasses)
  cycleClass_commutes : ∀ loop (primitive : step.Primitive)
    (sourceLift : CycleLiftFibre upper
      (primitive : upper.rationalHodgeClasses)),
    upper.cycleClass.hom (cycleAction loop sourceLift.1) =
      (((action loop primitive : step.Primitive) :
        upper.rationalHodgeClasses) : upper.Cohomology)
  spans : Submodule.span ℚ
    {primitive | ∃ (index : Seed) (loop : Monodromy),
      primitive = action loop (seed index)} = ⊤

attribute [instance] PrimitiveOrbitSourceCover.group

namespace PrimitiveMonodromySystem

variable {lower upper : Datum} {step : PrimitiveHodgeStep lower upper}

/-- [proved-derived; formal-checked] The commuting source action transports the complete
cycle-lift occurrence.  Fibre transport is therefore a consequence of a typed cycle current,
not an independent field. -/
def source_transport (system : PrimitiveMonodromySystem step)
    (loop : system.Monodromy) (primitive : step.Primitive)
    (sourceLift : CycleLiftFibre upper
      (primitive : upper.rationalHodgeClasses)) :
    CycleLiftFibre upper
      ((system.action loop primitive : step.Primitive) :
        upper.rationalHodgeClasses) :=
  ⟨system.cycleAction loop sourceLift.1,
    system.cycleClass_commutes loop primitive sourceLift⟩

/-- [proved-derived; formal-checked] A monodromy loop transports the complete algebraic-cycle
reconstruction fibre by an exact equivalence.  The inverse is the oppositely oriented loop, and
the group laws reconstruct both source occurrences rather than merely their receiver faces. -/
def sourceTransportEquiv (system : PrimitiveMonodromySystem step)
    (loop : system.Monodromy) (primitive : step.Primitive) :
    CycleLiftFibre upper (primitive : upper.rationalHodgeClasses) ≃
      CycleLiftFibre upper
        ((system.action loop primitive : step.Primitive) :
          upper.rationalHodgeClasses) where
  toFun := system.source_transport loop primitive
  invFun targetLift :=
    ⟨system.cycleAction loop⁻¹ targetLift.1, by
      simpa using system.cycleClass_commutes loop⁻¹
        (system.action loop primitive) targetLift⟩
  left_inv sourceLift := by
    apply Subtype.ext
    simp [source_transport]
  right_inv targetLift := by
    apply Subtype.ext
    simp [source_transport]

/-- [proved-derived; formal-checked] Transport of complete algebraic-cycle reconstruction fibres
implies invariance of the algebraic primitive receiver.  The range shadow is derived from the
source-bearing passage rather than accepted as the transport law. -/
theorem algebraic_stable (system : PrimitiveMonodromySystem step)
    (loop : system.Monodromy) (primitive : step.Primitive)
    (primitive_mem : primitive ∈ primitiveAlgebraicClasses step) :
    system.action loop primitive ∈ primitiveAlgebraicClasses step := by
  have sourceLift : Nonempty
      (CycleLiftFibre upper (primitive : upper.rationalHodgeClasses)) := by
    rw [cycleLiftFibre_nonempty_iff_mem_algebraicSpan]
    exact primitive_mem
  change ((((system.action loop primitive : step.Primitive) :
      upper.rationalHodgeClasses) : upper.Cohomology) ∈ upper.algebraicSpan)
  rw [← cycleLiftFibre_nonempty_iff_mem_algebraicSpan]
  obtain ⟨lift⟩ := sourceLift
  exact ⟨system.source_transport loop primitive lift⟩

/-- [definition] The actual algebraic primitive population, now retained with its complete
monodromy action. -/
def algebraicSubrepresentation (system : PrimitiveMonodromySystem step) :
    Subrepresentation system.action where
  toSubmodule := primitiveAlgebraicClasses step
  apply_mem_toSubmodule loop primitive hprimitive :=
    system.algebraic_stable loop primitive hprimitive

/-- [proved-derived; formal-checked] The source-bearing seed makes the invariant algebraic
subrepresentation nonzero. -/
theorem algebraicSubrepresentation_ne_bot
    (system : PrimitiveMonodromySystem step) :
    system.algebraicSubrepresentation ≠ ⊥ := by
  obtain ⟨primitive, primitive_ne_zero, sourceLift⟩ := system.seed
  have primitive_mem : primitive ∈ primitiveAlgebraicClasses step := by
    rw [cycleLiftFibre_nonempty_iff_mem_algebraicSpan] at sourceLift
    exact sourceLift
  intro algebraic_eq_bot
  have primitive_mem_bot : primitive ∈
      (⊥ : Subrepresentation system.action) := by
    rw [← algebraic_eq_bot]
    exact primitive_mem
  change primitive ∈ (⊥ : Submodule ℚ step.Primitive) at primitive_mem_bot
  exact primitive_ne_zero primitive_mem_bot

/-- [proved-derived; formal-checked] Irreducible monodromy propagates one algebraic seed through
the whole primitive block.  The conclusion is equality of the actual cycle-class source range
with the complete primitive carrier. -/
theorem primitiveAlgebraicClasses_eq_top
    (system : PrimitiveMonodromySystem step) :
    primitiveAlgebraicClasses step = ⊤ := by
  letI : Representation.IsIrreducible system.action := system.irreducible
  have invariant_eq_top : system.algebraicSubrepresentation = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top system.algebraicSubrepresentation).resolve_left
      system.algebraicSubrepresentation_ne_bot
  have underlying_eq_top :=
    congrArg Subrepresentation.toSubmodule invariant_eq_top
  change primitiveAlgebraicClasses step =
    (⊤ : Subrepresentation system.action).toSubmodule
  exact underlying_eq_top

/-- [proved-derived; formal-checked] Every primitive Hodge occurrence now has an actual rational
algebraic-cycle antecedent. -/
theorem primitiveLiftable (system : PrimitiveMonodromySystem step) :
    step.PrimitiveLiftable := by
  intro primitive
  rw [cycleLiftFibre_nonempty_iff_mem_algebraicSpan]
  have primitive_mem : primitive ∈ primitiveAlgebraicClasses step := by
    rw [system.primitiveAlgebraicClasses_eq_top]
    exact Submodule.mem_top
  exact primitive_mem

/-- [proved-derived; formal-checked] Under the signed Hodge--Riemann polarization, monodromy
propagation occupies every nonzero primitive interaction fibre. -/
theorem detectsEveryNonzero
    (system : PrimitiveMonodromySystem step)
    (polarization : SignedDefinitePrimitivePolarization step) :
    DetectsEveryNonzero polarization :=
  polarization.detectsEveryNonzero_of_primitiveLiftable system.primitiveLiftable

end PrimitiveMonodromySystem

namespace PrimitiveOrbitSourceCover

variable {lower upper : Datum} {step : PrimitiveHodgeStep lower upper}

/-- [proved-derived; formal-checked] One orbit occurrence carries the actual transported cycle
source returned by the commuting cycle action. -/
def source_transport (cover : PrimitiveOrbitSourceCover step)
    (loop : cover.Monodromy) (primitive : step.Primitive)
    (sourceLift : CycleLiftFibre upper
      (primitive : upper.rationalHodgeClasses)) :
    CycleLiftFibre upper
      ((cover.action loop primitive : step.Primitive) :
        upper.rationalHodgeClasses) :=
  ⟨cover.cycleAction loop sourceLift.1,
    cover.cycleClass_commutes loop primitive sourceLift⟩

/-- [definition] The primitive receiver occurrences reached by transported algebraic seeds. -/
def orbit (cover : PrimitiveOrbitSourceCover step) : Set step.Primitive :=
  {primitive | ∃ (index : cover.Seed) (loop : cover.Monodromy),
    primitive = cover.action loop (cover.seed index)}

/-- [proved-derived; formal-checked] Every orbit occurrence retains an actual algebraic-cycle
antecedent.  This is the source-bearing transport statement before taking a linear span. -/
theorem orbit_subset_algebraic (cover : PrimitiveOrbitSourceCover step) :
    cover.orbit ⊆ primitiveAlgebraicClasses step := by
  intro primitive hprimitive
  obtain ⟨index, loop, rfl⟩ := hprimitive
  change ((((cover.action loop (cover.seed index) : step.Primitive) :
      upper.rationalHodgeClasses) : upper.Cohomology) ∈ upper.algebraicSpan)
  rw [← cycleLiftFibre_nonempty_iff_mem_algebraicSpan]
  exact ⟨cover.source_transport loop (cover.seed index) (cover.seedLift index)⟩

/-- [proved-derived; formal-checked] Exact orbit generation propagates the retained seed sources
through a reducible primitive receiver.  No irreducibility theorem or block enumeration is needed:
the cover's spanning equality is precisely the gluing certificate. -/
theorem primitiveAlgebraicClasses_eq_top
    (cover : PrimitiveOrbitSourceCover step) :
    primitiveAlgebraicClasses step = ⊤ := by
  apply top_unique
  rw [← cover.spans]
  exact Submodule.span_le.mpr cover.orbit_subset_algebraic

/-- [proved-derived; formal-checked] A source-bearing orbit cover reconstructs an algebraic cycle
over every primitive Hodge receiver occurrence. -/
theorem primitiveLiftable (cover : PrimitiveOrbitSourceCover step) :
    step.PrimitiveLiftable := by
  intro primitive
  rw [cycleLiftFibre_nonempty_iff_mem_algebraicSpan]
  have primitive_mem : primitive ∈ primitiveAlgebraicClasses step := by
    rw [cover.primitiveAlgebraicClasses_eq_top]
    exact Submodule.mem_top
  exact primitive_mem

/-! ## Exact audit of the unrestricted orbit-cover aperture -/

/-- [proved-derived; formal-checked] Primitive liftability itself can populate the unrestricted
orbit-cover interface: take every primitive occurrence as a seed and use the identity action.

This construction is an audit, not a proposed Hodge proof.  It shows that `Seed`, `seedLift`, and
`spans` do not compress the universal conjectural obligation unless geometry independently
restricts the seed family and supplies its source transport. -/
noncomputable def ofPrimitiveLiftable
    (primitiveLiftable : step.PrimitiveLiftable) :
    PrimitiveOrbitSourceCover step where
  Monodromy := PUnit
  group := inferInstance
  action := Representation.trivial ℚ PUnit step.Primitive
  cycleAction := Representation.trivial ℚ PUnit upper.CycleSpace
  Seed := step.Primitive
  seed := id
  seedLift primitive := Classical.choice (primitiveLiftable primitive)
  cycleClass_commutes := by
    intro loop primitive sourceLift
    simpa using sourceLift.2
  spans := by
    apply top_unique
    intro primitive _
    apply Submodule.subset_span
    exact ⟨primitive, PUnit.unit, by simp⟩

/-- [proved-derived; formal-checked] Existence of an unrestricted source-bearing orbit cover is
exactly primitive algebraicity, not a weaker universal local-to-global law.  Consequently a future
Hodge argument may use an orbit cover only after proving an independent restriction such as a
source family fixed before the target primitive class, a proper parameter space, or a bounded
generator law whose transported orbit spans. -/
theorem nonempty_iff_primitiveLiftable
    {lower : Datum.{uLowerCycle, uLowerCohomology}}
    {upper : Datum.{uUpperCycle, uUpperCohomology}}
    {step : PrimitiveHodgeStep lower upper} :
    Nonempty (PrimitiveOrbitSourceCover.{uUpperCohomology} step) ↔
      step.PrimitiveLiftable := by
  constructor
  · rintro ⟨cover⟩
    exact cover.primitiveLiftable
  · intro primitiveLiftable
    exact ⟨ofPrimitiveLiftable primitiveLiftable⟩

/-- [proved-derived; formal-checked] Signed Hodge--Riemann polarization turns the orbit cover into
occupation of every nonzero holonic primitive interaction fibre. -/
theorem detectsEveryNonzero
    (cover : PrimitiveOrbitSourceCover step)
    (polarization : SignedDefinitePrimitivePolarization step) :
    DetectsEveryNonzero polarization :=
  polarization.detectsEveryNonzero_of_primitiveLiftable cover.primitiveLiftable

end PrimitiveOrbitSourceCover

/-! ## Universal composition -/

/-- [proved-derived; formal-checked] A source-indexed Lefschetz staircase closes the admitted
Hodge receiver when every primitive block has irreducible algebraicity-preserving monodromy and
one nonzero source-bearing algebraic seed.

Compared with the pointwise detector theorem, the conjectural obligation is compressed from one
witness per nonzero primitive vector to one witness per irreducible monodromy block, plus the
geometric invariance and irreducibility laws. -/
theorem theHodgeConjecture_of_irreducibleMonodromySeeds
    (Canonical : Realization → Prop)
    (staircase : ∀ (R : Realization), Canonical R → PrimitiveLefschetzStaircase R)
    (monodromy : ∀ (R : Realization) (hR : Canonical R) (p : ℕ),
      PrimitiveMonodromySystem ((staircase R hR).step p)) :
    TheHodgeConjecture Canonical := by
  intro R hR
  apply (staircase R hR).allConclusions_iff_allPrimitiveLiftable.mpr
  intro p
  exact (monodromy R hR p).primitiveLiftable

/-- [proved-derived; formal-checked] The admitted Hodge receiver closes when every primitive step
is generated by transported algebraic seed occurrences.  This is the decomposition-free form of
the monodromy squeeze: an irreducible block with one nonzero seed is one way to construct such a
cover, but not the only one. -/
theorem theHodgeConjecture_of_monodromyOrbitCovers
    (Canonical : Realization → Prop)
    (staircase : ∀ (R : Realization), Canonical R → PrimitiveLefschetzStaircase R)
    (covers : ∀ (R : Realization) (hR : Canonical R) (p : ℕ),
      PrimitiveOrbitSourceCover ((staircase R hR).step p)) :
    TheHodgeConjecture Canonical := by
  intro R hR
  apply (staircase R hR).allConclusions_iff_allPrimitiveLiftable.mpr
  intro p
  exact (covers R hR p).primitiveLiftable

section Audit

#print axioms PrimitiveMonodromySystem.algebraicSubrepresentation_ne_bot
#print axioms PrimitiveMonodromySystem.source_transport
#print axioms PrimitiveMonodromySystem.sourceTransportEquiv
#print axioms PrimitiveMonodromySystem.algebraic_stable
#print axioms PrimitiveMonodromySystem.primitiveAlgebraicClasses_eq_top
#print axioms PrimitiveMonodromySystem.primitiveLiftable
#print axioms PrimitiveMonodromySystem.detectsEveryNonzero
#print axioms theHodgeConjecture_of_irreducibleMonodromySeeds
#print axioms PrimitiveOrbitSourceCover.orbit_subset_algebraic
#print axioms PrimitiveOrbitSourceCover.source_transport
#print axioms PrimitiveOrbitSourceCover.primitiveAlgebraicClasses_eq_top
#print axioms PrimitiveOrbitSourceCover.primitiveLiftable
#print axioms PrimitiveOrbitSourceCover.ofPrimitiveLiftable
#print axioms PrimitiveOrbitSourceCover.nonempty_iff_primitiveLiftable
#print axioms PrimitiveOrbitSourceCover.detectsEveryNonzero
#print axioms theHodgeConjecture_of_monodromyOrbitCovers

end Audit

end Soma.Holonics.Millennium.HodgeMonodromyPrimitivePropagation
