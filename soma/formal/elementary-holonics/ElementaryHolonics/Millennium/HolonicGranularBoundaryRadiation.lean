import ElementaryHolonics.Millennium.ReceiverHistory
import ElementaryHolonics.Millennium.HolonicPortResolvedBoundaryTransport
import ElementaryHolonics.Millennium.HolonicTorusEntropyParametronEquivalence
import ElementaryHolonics.Foundation.BoundaryScalePassage
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Granular interior current radiates through a scale-natural boundary complex

**[proved-derived]** This file closes the algebraic part of the seam exposed by the MEM6
counterexample.  A finite particle population carries a constitutive interior current.  An oriented
incidence matrix takes its boundary; an outer incidence takes the boundary once more.  Requiring
the two incidence matrices to compose to zero makes every radiated section a cycle.  The transpose
incidence is the reflected pullback of a boundary receiver, and the finite Stokes identity proves
that integrating the outward current is the same operation as pulling that receiver inward.

Addressed boundary ports act only after the complete boundary section exists.  Equal port faces
mean precisely that the complete action difference lies in the joint port kernel; they never
identify the source actions.  A surface which separates two actions in one coarser fibre therefore
cannot factor through that coarse fibre.  This is the exact obstruction returned by the standing
word/clause renderer.

`BoundaryScalePassage` then states the naturality square required between arbitrary adjacent
grains and proves that these passages compose.  No field names a character, morpheme, word, token,
language, modality, force species, or fixed scale population.  Particle identity is supplied by
the already formalized complete receiver-history quotient, not by exterior spelling.

This is the common kinematic carrier.  A physical electromagnetic, weak, strong, gravitational,
optical, acoustic, or linguistic realization still owes its own typed constitutive matrix, ports,
calibration, and receiver family.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation

open scoped BigOperators
open Soma.Holonics.Millennium.ReceiverHistory

/-! ## One exact finite interior/boundary body -/

/-- A finite granular body with an interior constitutive response, two successive oriented
boundaries, and a resolved exterior port family.  The indices are particles/cells at the declared
receiver grain; the structure assigns them no semantic species. -/
structure GranularBoundaryBody
    (Scalar Cell Face Ridge Port : Type*)
    [CommRing Scalar] [Fintype Cell] [Fintype Face] [Fintype Ridge] [Fintype Port] where
  constitutive : Matrix Cell Cell Scalar
  innerBoundary : Matrix Face Cell Scalar
  outerBoundary : Matrix Ridge Face Scalar
  portTrace : Matrix Port Face Scalar
  boundary_boundary : outerBoundary * innerBoundary = 0

namespace GranularBoundaryBody

variable
    {Scalar Cell Face Ridge Port : Type*}
    [CommRing Scalar] [Fintype Cell] [Fintype Face] [Fintype Ridge] [Fintype Port]

/-- The complete constitutive current before any boundary receiver acts. -/
def interiorCurrent
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (action : Cell → Scalar) : Cell → Scalar :=
  body.constitutive.mulVec action

/-- The oriented boundary radiation of the complete constitutive current. -/
def boundaryRadiation
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (action : Cell → Scalar) : Face → Scalar :=
  body.innerBoundary.mulVec (body.interiorCurrent action)

/-- The boundary of the returned boundary section. -/
def outerReturn
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (action : Cell → Scalar) : Ridge → Scalar :=
  body.outerBoundary.mulVec (body.boundaryRadiation action)

/-- Every complete boundary radiation is a cycle: the boundary of the boundary is exactly null. -/
theorem outerReturn_eq_zero
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (action : Cell → Scalar) :
    body.outerReturn action = 0 := by
  unfold outerReturn boundaryRadiation
  calc
    body.outerBoundary.mulVec
        (body.innerBoundary.mulVec (body.interiorCurrent action)) =
      (body.outerBoundary * body.innerBoundary).mulVec
        (body.interiorCurrent action) :=
          Matrix.mulVec_mulVec (body.interiorCurrent action)
            body.outerBoundary body.innerBoundary
    _ = 0 := by simp only [body.boundary_boundary, Matrix.zero_mulVec]

/-- Pull a boundary receiver into the interior by the transpose incidence.  This is the algebraic
reflection used by the finite Stokes identity below. -/
def reflectedBoundaryPotential
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (potential : Face → Scalar) : Cell → Scalar :=
  body.innerBoundary.transpose.mulVec potential

/-- Continue the reflected boundary receiver through the constitutive form to the entering action.
This is the complete finite causal adjoint of `action ↦ innerBoundary (constitutive action)`. -/
def reflectedActionPotential
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (potential : Face → Scalar) : Cell → Scalar :=
  body.constitutive.transpose.mulVec (body.reflectedBoundaryPotential potential)

/-- The exact finite integration-by-reflection/Stokes law. -/
theorem boundary_pairing_eq_reflected_interior_pairing
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (potential : Face → Scalar) (current : Cell → Scalar) :
    dotProduct potential (body.innerBoundary.mulVec current) =
      dotProduct (body.reflectedBoundaryPotential potential) current := by
  rw [Matrix.dotProduct_mulVec, reflectedBoundaryPotential,
    Matrix.mulVec_transpose]

/-- Stokes after the constitutive response: outward integration is the reflected receiver acting
on the complete interior current, not a choice of one exterior token or cell. -/
theorem boundaryRadiation_pairing_eq_reflected_interiorCurrent_pairing
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (potential : Face → Scalar) (action : Cell → Scalar) :
    dotProduct potential (body.boundaryRadiation action) =
      dotProduct (body.reflectedBoundaryPotential potential) (body.interiorCurrent action) := by
  exact body.boundary_pairing_eq_reflected_interior_pairing potential
    (body.interiorCurrent action)

/-- Complete integration by reflection: the exterior potential pulled through both the boundary
and constitutive passages returns the same pairing against the entering action. -/
theorem boundaryRadiation_pairing_eq_reflected_action_pairing
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (potential : Face → Scalar) (action : Cell → Scalar) :
    dotProduct potential (body.boundaryRadiation action) =
      dotProduct (body.reflectedActionPotential potential) action := by
  rw [body.boundaryRadiation_pairing_eq_reflected_interiorCurrent_pairing,
    interiorCurrent, Matrix.dotProduct_mulVec, reflectedActionPotential,
    Matrix.mulVec_transpose]

/-- The complete port-resolved exterior reading, formed only after boundary radiation. -/
def portRadiation
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (action : Cell → Scalar) : Port → Scalar :=
  body.portTrace.mulVec (body.boundaryRadiation action)

/-- Constitutive interior current is additive in the entering action. -/
theorem interiorCurrent_sub
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (left right : Cell → Scalar) :
    body.interiorCurrent (left - right) =
      body.interiorCurrent left - body.interiorCurrent right := by
  simpa only [interiorCurrent] using Matrix.mulVec_sub body.constitutive left right

/-- Boundary radiation preserves the complete oriented action difference. -/
theorem boundaryRadiation_sub
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (left right : Cell → Scalar) :
    body.boundaryRadiation (left - right) =
      body.boundaryRadiation left - body.boundaryRadiation right := by
  simp only [boundaryRadiation, interiorCurrent, Matrix.mulVec_sub]

/-- Port radiation preserves the complete oriented action difference. -/
theorem portRadiation_sub
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (left right : Cell → Scalar) :
    body.portRadiation (left - right) =
      body.portRadiation left - body.portRadiation right := by
  simp only [portRadiation, boundaryRadiation, interiorCurrent, Matrix.mulVec_sub]

/-- The complete action population invisible to every addressed exterior port. -/
def jointPortKernel
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port) :
    Set (Cell → Scalar) :=
  {action | body.portRadiation action = 0}

/-- Equal resolved exterior port faces are exactly membership of the complete action difference in
the joint port kernel.  The source actions remain plural in that fibre. -/
theorem same_portRadiation_iff_difference_mem_jointPortKernel
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (left right : Cell → Scalar) :
    body.portRadiation left = body.portRadiation right ↔
      left - right ∈ body.jointPortKernel := by
  rw [jointPortKernel, Set.mem_setOf_eq, body.portRadiation_sub, sub_eq_zero]

/-- If the declared complete port family is faithful, equal exterior radiation reconstructs the
entering particle section.  Faithfulness is an explicit hypothesis, never inferred from a count. -/
theorem action_eq_of_portRadiation_eq
    (body : GranularBoundaryBody Scalar Cell Face Ridge Port)
    (faithful : Function.Injective body.portRadiation)
    {left right : Cell → Scalar}
    (equalRadiation : body.portRadiation left = body.portRadiation right) :
    left = right :=
  faithful equalRadiation

end GranularBoundaryBody

/-! ## The exact coarse-receiver obstruction -/

/-- The complete population collapsed by one exterior receiver face. -/
def reconstructionFiber {Source Face : Type*}
    (receiver : Source → Face) (face : Face) : Set Source :=
  {source | receiver source = face}

/-- A later surface which separates two members of one coarse fibre cannot factor through that
coarse receiver.  Adding prose to the factor cannot repair the missing transport. -/
theorem separated_surface_cannot_factor_through_coarse_receiver
    {Source Coarse Surface : Type*}
    (coarse : Source → Coarse) (surface : Source → Surface)
    {left right : Source}
    (sameCoarse : coarse left = coarse right)
    (surfaceSeparates : surface left ≠ surface right) :
    ¬ ∃ factor : Coarse → Surface, ∀ source, surface source = factor (coarse source) := by
  rintro ⟨factor, factors⟩
  apply surfaceSeparates
  calc
    surface left = factor (coarse left) := factors left
    _ = factor (coarse right) := congrArg factor sameCoarse
    _ = surface right := (factors right).symm

/-! ## Particle identity comes from complete causal signatures -/

/-- At any founded grain, equality of native particle faces is equality of every admitted future
receiver/history consequence.  Exterior spelling is absent from this criterion. -/
theorem particleFace_eq_iff_complete_causalSignature_eq
    {Generator Receiver Source Quotient Face : Type*}
    (compression : CompleteReceiverHistoryQuotient
      Generator Receiver Source Quotient Face)
    {left right : Source} :
    compression.present.quotient left = compression.present.quotient right ↔
      compression.causalSignature left = compression.causalSignature right :=
  compression.quotientEq_iff_causalSignatureEq

/-- Unequal particle faces return a concrete future receiver/history separator rather than a
semantic label or guessed unit boundary. -/
theorem particleFace_ne_returns_separator
    {Generator Receiver Source Quotient Face : Type*}
    (compression : CompleteReceiverHistoryQuotient
      Generator Receiver Source Quotient Face)
    {left right : Source}
    (unequal : compression.present.quotient left ≠ compression.present.quotient right) :
    ∃ receiver word,
      compression.causalSignature left receiver word ≠
        compression.causalSignature right receiver word :=
  compression.quotientNe_returnsSeparatingReceiverHistory unequal

/-! ## The grain is derived from causal signature, not selected from a codec -/

/-- A receiver grain is only a family of observable future consequences over one source
population.  `Index` may contain a receiver and an ordered generator word, but this definition
does not privilege that presentation. -/
structure CausalGrain (Source Index Face : Type*) where
  signature : Source → Index → Face

namespace CausalGrain

variable {Source FineIndex FineFace MiddleIndex MiddleFace CoarseIndex CoarseFace : Type*}

/-- Two source occurrences occupy one particle exactly when the declared grain cannot separate
their complete consequence sections. -/
def signatureSetoid (grain : CausalGrain Source FineIndex FineFace) : Setoid Source where
  r left right := grain.signature left = grain.signature right
  iseqv := {
    refl := fun _ => rfl
    symm := fun equality => equality.symm
    trans := fun leftMiddle middleRight => leftMiddle.trans middleRight
  }

/-- The native particle population founded by one receiver grain.  This quotient is canonical:
it has no token population, chosen state width, clustering score, or authored scale. -/
abbrev Particle (grain : CausalGrain Source FineIndex FineFace) :=
  Quotient grain.signatureSetoid

/-- Present one situated source occurrence at the grain. -/
def particle (grain : CausalGrain Source FineIndex FineFace) (source : Source) : grain.Particle :=
  Quotient.mk grain.signatureSetoid source

/-- Equality at a grain is exactly equality of its full consequence section. -/
theorem particle_eq_iff_signature_eq
    (grain : CausalGrain Source FineIndex FineFace) {left right : Source} :
    grain.particle left = grain.particle right ↔
      grain.signature left = grain.signature right := by
  constructor
  · exact Quotient.exact
  · intro equality
    apply Quotient.sound
    change grain.signature left = grain.signature right
    exact equality

/-- Every particle retains the complete source population which the receiver identified. -/
def reconstructionFiber
    (grain : CausalGrain Source FineIndex FineFace) (face : grain.Particle) : Set Source :=
  {source | grain.particle source = face}

/-- A passage to a coarser grain exists only when equality of every fine consequence forces
equality of every coarse consequence.  This is the factorization law which an authored tokenizer
or renderer would owe and cannot obtain from matching spellings alone. -/
structure Passage
    (fine : CausalGrain Source FineIndex FineFace)
    (coarse : CausalGrain Source CoarseIndex CoarseFace) where
  respects : ∀ {left right},
    fine.signature left = fine.signature right →
      coarse.signature left = coarse.signature right

namespace Passage

variable
    {fine : CausalGrain Source FineIndex FineFace}
    {middle : CausalGrain Source MiddleIndex MiddleFace}
    {coarse : CausalGrain Source CoarseIndex CoarseFace}

/-- Descend a native fine particle through a proved causal quotient. -/
def map (passage : Passage fine coarse) : fine.Particle → coarse.Particle :=
  Quotient.map id (fun _ _ equality => passage.respects equality)

/-- Source presentation commutes with causal condensation. -/
theorem map_particle (passage : Passage fine coarse) (source : Source) :
    passage.map (fine.particle source) = coarse.particle source := rfl

/-- Causal grain passages compose by implication of complete consequence equality. -/
def comp (fineToMiddle : Passage fine middle) (middleToCoarse : Passage middle coarse) :
    Passage fine coarse where
  respects equality := middleToCoarse.respects (fineToMiddle.respects equality)

/-- Condensing through two lawful grains is the same map as their composite. -/
theorem map_comp
    (fineToMiddle : Passage fine middle) (middleToCoarse : Passage middle coarse)
    (particle : fine.Particle) :
    (fineToMiddle.comp middleToCoarse).map particle =
      middleToCoarse.map (fineToMiddle.map particle) := by
  refine Quotient.inductionOn particle ?_
  intro source
  rfl

end Passage

end CausalGrain

/-! ### The complete receiver/history family founds the canonical native grain -/

variable
    {Generator Receiver Source Quotient Face CoarseReceiver CoarseFace : Type*}

/-- Uncurry the complete receiver/history signature into one canonical grain. -/
def completeReceiverHistoryGrain
    (compression : CompleteReceiverHistoryQuotient
      Generator Receiver Source Quotient Face) :
    CausalGrain Source (Receiver × List Generator) Face where
  signature source receiverWord :=
    compression.causalSignature source receiverWord.1 receiverWord.2

/-- The canonical grain and the admitted complete quotient induce exactly the same source
equivalence relation. -/
theorem completeReceiverHistoryGrain_particle_eq_iff_present_quotient_eq
    (compression : CompleteReceiverHistoryQuotient
      Generator Receiver Source Quotient Face)
    {left right : Source} :
    (completeReceiverHistoryGrain compression).particle left =
        (completeReceiverHistoryGrain compression).particle right ↔
      compression.present.quotient left = compression.present.quotient right := by
  rw [CausalGrain.particle_eq_iff_signature_eq,
    compression.quotientEq_iff_causalSignatureEq]
  constructor
  · intro uncurried
    funext receiver word
    exact congrFun uncurried (receiver, word)
  · intro curried
    funext receiverWord
    exact congrFun (congrFun curried receiverWord.1) receiverWord.2

/-- A selected receiver subfamily and a later receiver reading define a coarser grain.  They do
not alter the source population or install a semantic unit. -/
def restrictedReceiverHistoryGrain
    (compression : CompleteReceiverHistoryQuotient
      Generator Receiver Source Quotient Face)
    (select : CoarseReceiver → Receiver) (read : Face → CoarseFace) :
    CausalGrain Source (CoarseReceiver × List Generator) CoarseFace where
  signature source receiverWord :=
    read (compression.causalSignature source (select receiverWord.1) receiverWord.2)

/-- Restricting the receiver family is automatically a lawful fine-to-coarse causal passage. -/
def completeToRestrictedPassage
    (compression : CompleteReceiverHistoryQuotient
      Generator Receiver Source Quotient Face)
    (select : CoarseReceiver → Receiver) (read : Face → CoarseFace) :
    CausalGrain.Passage (completeReceiverHistoryGrain compression)
      (restrictedReceiverHistoryGrain compression select read) where
  respects := by
    intro left right completeEquality
    funext receiverWord
    exact congrArg read (congrFun completeEquality (select receiverWord.1, receiverWord.2))

/-- If a coarse grain identifies two sources which the complete grain separates, the exact
reconstruction fibre has reopened.  No cold decoder may invent the missing distinction. -/
theorem coarse_grain_equality_with_fine_separation_returns_reconstructionFiber
    (compression : CompleteReceiverHistoryQuotient
      Generator Receiver Source Quotient Face)
    (select : CoarseReceiver → Receiver) (read : Face → CoarseFace)
    {left right : Source}
    (coarseEqual :
      (restrictedReceiverHistoryGrain compression select read).particle left =
        (restrictedReceiverHistoryGrain compression select read).particle right)
    (fineDifferent :
      (completeReceiverHistoryGrain compression).particle left ≠
        (completeReceiverHistoryGrain compression).particle right) :
    left ∈ (restrictedReceiverHistoryGrain compression select read).reconstructionFiber
        ((restrictedReceiverHistoryGrain compression select read).particle left) ∧
      right ∈ (restrictedReceiverHistoryGrain compression select read).reconstructionFiber
        ((restrictedReceiverHistoryGrain compression select read).particle left) ∧
      (completeReceiverHistoryGrain compression).particle left ≠
        (completeReceiverHistoryGrain compression).particle right := by
  exact ⟨rfl, coarseEqual.symm, fineDifferent⟩

/-! ### A causal quotient and its physical boundary passage must commute together -/

/-- One granulation step carries both the canonical causal particle quotient and the physical
interior/boundary current.  The realization square forbids a codec quotient from changing the
physical section silently. -/
structure CausalBoundaryGranulation
    (Scalar Source FineIndex FineFace CoarseIndex CoarseFace
      FineInterior FineBoundary CoarseInterior CoarseBoundary : Type*)
    [Semiring Scalar]
    [AddCommMonoid FineInterior] [Module Scalar FineInterior]
    [AddCommMonoid FineBoundary] [Module Scalar FineBoundary]
    [AddCommMonoid CoarseInterior] [Module Scalar CoarseInterior]
    [AddCommMonoid CoarseBoundary] [Module Scalar CoarseBoundary]
    (fine : CausalGrain Source FineIndex FineFace)
    (coarse : CausalGrain Source CoarseIndex CoarseFace) where
  causal : CausalGrain.Passage fine coarse
  boundary : BoundaryScalePassage Scalar FineInterior FineBoundary
    CoarseInterior CoarseBoundary
  realizeFine : fine.Particle → FineInterior
  realizeCoarse : coarse.Particle → CoarseInterior
  realization_natural : ∀ particle,
    boundary.interiorTransport (realizeFine particle) =
      realizeCoarse (causal.map particle)

namespace CausalBoundaryGranulation

variable
    {Scalar Source FineIndex FineFace CoarseIndex CoarseFace
      FineInterior FineBoundary CoarseInterior CoarseBoundary : Type*}
    [Semiring Scalar]
    [AddCommMonoid FineInterior] [Module Scalar FineInterior]
    [AddCommMonoid FineBoundary] [Module Scalar FineBoundary]
    [AddCommMonoid CoarseInterior] [Module Scalar CoarseInterior]
    [AddCommMonoid CoarseBoundary] [Module Scalar CoarseBoundary]
    {fine : CausalGrain Source FineIndex FineFace}
    {coarse : CausalGrain Source CoarseIndex CoarseFace}

/-- Boundary radiation may be formed before or after a causally founded granulation step. -/
theorem radiation_natural
    (granulation : CausalBoundaryGranulation Scalar Source FineIndex FineFace
      CoarseIndex CoarseFace FineInterior FineBoundary CoarseInterior CoarseBoundary fine coarse)
    (particle : fine.Particle) :
    granulation.boundary.coarseBoundary
        (granulation.realizeCoarse (granulation.causal.map particle)) =
      granulation.boundary.boundaryTransport
        (granulation.boundary.fineBoundary (granulation.realizeFine particle)) := by
  rw [← granulation.realization_natural particle]
  exact granulation.boundary.transport_boundary (granulation.realizeFine particle)

end CausalBoundaryGranulation

section Audit

#print axioms GranularBoundaryBody.outerReturn_eq_zero
#print axioms GranularBoundaryBody.boundary_pairing_eq_reflected_interior_pairing
#print axioms GranularBoundaryBody.boundaryRadiation_pairing_eq_reflected_interiorCurrent_pairing
#print axioms GranularBoundaryBody.boundaryRadiation_pairing_eq_reflected_action_pairing
#print axioms GranularBoundaryBody.same_portRadiation_iff_difference_mem_jointPortKernel
#print axioms separated_surface_cannot_factor_through_coarse_receiver
#print axioms particleFace_eq_iff_complete_causalSignature_eq
#print axioms particleFace_ne_returns_separator
#print axioms CausalGrain.particle_eq_iff_signature_eq
#print axioms CausalGrain.Passage.map_comp
#print axioms completeReceiverHistoryGrain_particle_eq_iff_present_quotient_eq
#print axioms coarse_grain_equality_with_fine_separation_returns_reconstructionFiber
#print axioms CausalBoundaryGranulation.radiation_natural

end Audit

end Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation
