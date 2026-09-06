import ElementaryHolonics.Foundation.Holon
import ElementaryHolonics.Foundation.Receiver
import Mathlib.CategoryTheory.Category.Basic

/-!
# Causal-natural holon families

This file strengthens the elementary occurrence-bearing `Holon` only when an admitted parameter
category has been supplied.  Occurrences, addressed source and target ports, and receiver faces all
vary functorially, while the three structure maps are natural transformations.  A tensor carrier
alone supplies none of this structure.

An arbitrary parameter arrow maps a preimage fibre forward.  It need not return an equivalence:
that stronger conclusion requires an isomorphism of complete holon diagrams, represented by
`Holon.Rebase`.  This is a strict `Type`-valued first presentation; it does not claim the still-open
pseudofunctor coherence of the complete receiver-decorated span bicategory.
-/

namespace Soma.Holonics

open CategoryTheory

universe uParameter vParameter uCarrier

/--
A family of complete holons natural under one declared parameter category. The common carrier
universe is a presentation choice, not an identification of the four roles.
-/
structure NaturalHolonFamily
    (Parameter : Type uParameter) [Category.{vParameter} Parameter] where
  occurrence : Parameter ⥤ Type uCarrier
  sourceFace : Parameter ⥤ Type uCarrier
  targetFace : Parameter ⥤ Type uCarrier
  receiverFace : Parameter ⥤ Type uCarrier
  source : occurrence ⟶ sourceFace
  target : occurrence ⟶ targetFace
  receive : occurrence ⟶ receiverFace

/--
A natural holon family whose parameter arrows are realized by addressed occurrence passages.
Every source occurrence crosses each declared arrow; the passage target is the functorial transport
of that source, and its receiver is the transported occurrence's face.
-/
structure CausalNaturalHolon
    (Parameter : Type uParameter) [Category.{vParameter} Parameter]
    extends NaturalHolonFamily Parameter where
  parameterPassage : ∀ {before after : Parameter}, (step : before ⟶ after) →
    Holon.{uCarrier, uCarrier, uCarrier, uCarrier}
      (occurrence.obj before) (occurrence.obj after) (receiverFace.obj after)
  source_complete : ∀ {before after : Parameter} (step : before ⟶ after)
    (source : occurrence.obj before),
    ∃ crossing : (parameterPassage step).Occurrence,
      (parameterPassage step).source crossing = source
  target_transport : ∀ {before after : Parameter} (step : before ⟶ after)
    (crossing : (parameterPassage step).Occurrence),
    (parameterPassage step).target crossing =
      occurrence.map step ((parameterPassage step).source crossing)
  receive_target : ∀ {before after : Parameter} (step : before ⟶ after)
    (crossing : (parameterPassage step).Occurrence),
    (parameterPassage step).receive crossing =
      receive.app after ((parameterPassage step).target crossing)

namespace CausalNaturalHolon

variable {Parameter : Type uParameter} [Category.{vParameter} Parameter]

/-- The elementary occurrence-bearing holon at one situated parameter. -/
def component (family : CausalNaturalHolon Parameter) (parameter : Parameter) :
    Holon (family.sourceFace.obj parameter) (family.targetFace.obj parameter)
      (family.receiverFace.obj parameter) where
  Occurrence := family.occurrence.obj parameter
  source := family.source.app parameter
  target := family.target.app parameter
  receive := family.receive.app parameter

/-- Naturality of the addressed source port. -/
theorem source_natural (family : CausalNaturalHolon Parameter)
    {before after : Parameter} (step : before ⟶ after)
    (occurrence : family.occurrence.obj before) :
    family.sourceFace.map step (family.source.app before occurrence) =
      family.source.app after (family.occurrence.map step occurrence) := by
  simpa using congrFun (family.source.naturality step) occurrence

/-- Naturality of the addressed target port. -/
theorem target_natural (family : CausalNaturalHolon Parameter)
    {before after : Parameter} (step : before ⟶ after)
    (occurrence : family.occurrence.obj before) :
    family.targetFace.map step (family.target.app before occurrence) =
      family.target.app after (family.occurrence.map step occurrence) := by
  simpa using congrFun (family.target.naturality step) occurrence

/-- Naturality of the receiver face. -/
theorem receive_natural (family : CausalNaturalHolon Parameter)
    {before after : Parameter} (step : before ⟶ after)
    (occurrence : family.occurrence.obj before) :
    family.receiverFace.map step (family.receive.app before occurrence) =
      family.receive.app after (family.occurrence.map step occurrence) := by
  simpa using congrFun (family.receive.naturality step) occurrence

/--
Every admitted parameter step transports the complete population behind a receiver face forward.
No inverse is fabricated for a noninvertible causal step.
-/
def mapPreimageFibre (family : CausalNaturalHolon Parameter)
    {before after : Parameter} (step : before ⟶ after)
    (face : family.receiverFace.obj before) :
    (family.component before).PreimageFibre face →
      (family.component after).PreimageFibre (family.receiverFace.map step face) :=
  fun occurrence ↦
    ⟨family.occurrence.map step occurrence.1, by
      calc
        family.receive.app after (family.occurrence.map step occurrence.1) =
            family.receiverFace.map step (family.receive.app before occurrence.1) :=
          (family.receive_natural step occurrence.1).symm
        _ = family.receiverFace.map step face := congrArg _ occurrence.2⟩

/-- Transport an actually presented source face along an admitted parameter arrow.

The codomain is again a `Set.range`: source naturality proves that the transported face is
presented by the mapped occurrence.  No value is assigned to an exterior source coordinate which
was not presented by this component.
-/
def mapSourceRange (family : CausalNaturalHolon Parameter)
    {before after : Parameter} (step : before ⟶ after) :
    Set.range (family.source.app before) → Set.range (family.source.app after) :=
  fun face ↦
    ⟨family.sourceFace.map step face.1, by
      rcases face.2 with ⟨occurrence, hsource⟩
      refine ⟨family.occurrence.map step occurrence, ?_⟩
      calc
        family.source.app after (family.occurrence.map step occurrence) =
            family.sourceFace.map step (family.source.app before occurrence) :=
          (family.source_natural step occurrence).symm
        _ = family.sourceFace.map step face.1 := congrArg _ hsource⟩

/-- A pair of exact local receiver transformers commutes with source-range transport.

Both transformers are defined only on the source faces that their own component actually presents;
the parameter arrow transports those ranges, while receiver naturality transports the returned face.
-/
theorem receiverTransformer_natural
    (family : CausalNaturalHolon Parameter)
    {before after : Parameter} (step : before ⟶ after)
    (beforeTransformer : ReceiverTransformer
      (family.source.app before) (family.receive.app before))
    (afterTransformer : ReceiverTransformer
      (family.source.app after) (family.receive.app after))
    (face : Set.range (family.source.app before)) :
    afterTransformer.transform (mapSourceRange family step face) =
      family.receiverFace.map step (beforeTransformer.transform face) := by
  rcases face.2 with ⟨occurrence, hsource⟩
  let entering : Set.range (family.source.app before) :=
    ⟨family.source.app before occurrence, ⟨occurrence, rfl⟩⟩
  have hentering : entering = face := Subtype.ext hsource
  have hmapped : mapSourceRange family step entering =
      (⟨family.source.app after (family.occurrence.map step occurrence),
        ⟨family.occurrence.map step occurrence, rfl⟩⟩ :
        Set.range (family.source.app after)) := by
    apply Subtype.ext
    exact family.source_natural step occurrence
  calc
    afterTransformer.transform (mapSourceRange family step face) =
        afterTransformer.transform (mapSourceRange family step entering) := by
          rw [hentering]
    _ = family.receive.app after (family.occurrence.map step occurrence) := by
          rw [hmapped]
          exact afterTransformer.exact _
    _ = family.receiverFace.map step (family.receive.app before occurrence) :=
          (family.receive_natural step occurrence).symm
    _ = family.receiverFace.map step (beforeTransformer.transform face) := by
          rw [← beforeTransformer.exact occurrence]
          congr 1
          exact congrArg beforeTransformer.transform hentering

/-- An actual addressed parameter-passage crossing obeys the local transformer square.

The crossing is retained explicitly; its target is not replaced by an unconditioned global map.
-/
theorem parameterPassage_crossing_receiverTransformer_natural
    (family : CausalNaturalHolon Parameter)
    {before after : Parameter} (step : before ⟶ after)
    (beforeTransformer : ReceiverTransformer
      (family.source.app before) (family.receive.app before))
    (afterTransformer : ReceiverTransformer
      (family.source.app after) (family.receive.app after))
    (crossing : (family.parameterPassage step).Occurrence) :
    afterTransformer.transform
        (⟨family.source.app after ((family.parameterPassage step).target crossing),
          ⟨(family.parameterPassage step).target crossing, rfl⟩⟩ :
          Set.range (family.source.app after)) =
      family.receiverFace.map step
        (beforeTransformer.transform
          (⟨family.source.app before ((family.parameterPassage step).source crossing),
            ⟨(family.parameterPassage step).source crossing, rfl⟩⟩ :
            Set.range (family.source.app before))) := by
  let entering : Set.range (family.source.app before) :=
    ⟨family.source.app before ((family.parameterPassage step).source crossing),
      ⟨(family.parameterPassage step).source crossing, rfl⟩⟩
  let target : Set.range (family.source.app after) :=
    ⟨family.source.app after ((family.parameterPassage step).target crossing),
      ⟨(family.parameterPassage step).target crossing, rfl⟩⟩
  have htarget : mapSourceRange family step entering = target := by
    apply Subtype.ext
    calc
      family.sourceFace.map step
          (family.source.app before ((family.parameterPassage step).source crossing)) =
          family.source.app after
            (family.occurrence.map step ((family.parameterPassage step).source crossing)) :=
        family.source_natural step ((family.parameterPassage step).source crossing)
      _ = family.source.app after ((family.parameterPassage step).target crossing) := by
        rw [← family.target_transport step crossing]
  have hcommutes := receiverTransformer_natural family step beforeTransformer afterTransformer entering
  rw [show (⟨family.source.app before ((family.parameterPassage step).source crossing),
      ⟨(family.parameterPassage step).source crossing, rfl⟩⟩ :
      Set.range (family.source.app before)) = entering by rfl]
  rw [show (⟨family.source.app after ((family.parameterPassage step).target crossing),
      ⟨(family.parameterPassage step).target crossing, rfl⟩⟩ :
      Set.range (family.source.app after)) = target by rfl]
  rw [← htarget]
  exact hcommutes

/-- An addressed crossing receives exactly the transported face of its entering occurrence. -/
theorem crossing_receive_eq_transported_source_receive
    (family : CausalNaturalHolon Parameter)
    {before after : Parameter} (step : before ⟶ after)
    (crossing : (family.parameterPassage step).Occurrence) :
    (family.parameterPassage step).receive crossing =
      family.receiverFace.map step
        (family.receive.app before ((family.parameterPassage step).source crossing)) := by
  rw [family.receive_target step crossing, family.target_transport step crossing]
  exact (family.receive_natural step _).symm

end CausalNaturalHolon

end Soma.Holonics

section Audit
open Soma.Holonics
#print axioms CausalNaturalHolon.source_natural
#print axioms CausalNaturalHolon.target_natural
#print axioms CausalNaturalHolon.receive_natural
#print axioms CausalNaturalHolon.mapPreimageFibre
#print axioms CausalNaturalHolon.mapSourceRange
#print axioms CausalNaturalHolon.receiverTransformer_natural
#print axioms CausalNaturalHolon.parameterPassage_crossing_receiverTransformer_natural
#print axioms CausalNaturalHolon.crossing_receive_eq_transported_source_receive
end Audit
