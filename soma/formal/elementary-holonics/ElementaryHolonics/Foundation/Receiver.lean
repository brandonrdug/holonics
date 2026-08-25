import Mathlib.Logic.Relation
import Mathlib.Data.Set.Operations

/-!
# Receivers and receiver-exact compression

This file formalizes only the elementary relational carrier.  It does not make
receiver dependence into an axiom of ordinary mathematics.
-/

namespace Soma.Holonics

universe u v w

/-- A typed relation from `α` to `β`. -/
abbrev Rel (α : Type u) (β : Type v) := α → β → Prop

namespace Rel

/-- Relational identity. -/
def id (α : Type u) : Rel α α := (· = ·)

/-- Relational composition, retaining existence but not the chosen witness. -/
def comp {α : Type u} {β : Type v} {γ : Type w}
    (s : Rel β γ) (r : Rel α β) : Rel α γ :=
  fun a c ↦ ∃ b, r a b ∧ s b c

theorem comp_assoc {α : Type u} {β : Type v} {γ : Type w} {δ : Type*}
    (t : Rel γ δ) (s : Rel β γ) (r : Rel α β) :
    comp t (comp s r) = comp (comp t s) r := by
  funext a d
  apply propext
  constructor
  · rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, c, hbc, hcd⟩
  · rintro ⟨b, hab, c, hbc, hcd⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩

theorem id_comp {α : Type u} {β : Type v} (r : Rel α β) :
    comp (id β) r = r := by
  funext a b
  apply propext
  constructor
  · rintro ⟨b', hab', rfl⟩
    exact hab'
  · intro hab
    exact ⟨b, hab, rfl⟩

theorem comp_id {α : Type u} {β : Type v} (r : Rel α β) :
    comp r (id α) = r := by
  funext a b
  apply propext
  constructor
  · rintro ⟨a', rfl, hab⟩
    exact hab
  · intro hab
    exact ⟨a, rfl, hab⟩

end Rel

/--
Two source occurrences are equivalent for a declared family of functional
receivers when every receiver returns the same face.
-/
def ReceiverEq {ι : Type*} {X : Type u} {Y : Type v}
    (ρ : ι → X → Y) (x y : X) : Prop :=
  ∀ i, ρ i x = ρ i y

theorem receiverEq_refl {ι : Type*} {X : Type u} {Y : Type v}
    (ρ : ι → X → Y) (x : X) :
    ReceiverEq ρ x x :=
  fun _ ↦ rfl

theorem receiverEq_symm {ι : Type*} {X : Type u} {Y : Type v}
    (ρ : ι → X → Y) {x y : X}
    (h : ReceiverEq ρ x y) :
    ReceiverEq ρ y x :=
  fun i ↦ (h i).symm

theorem receiverEq_trans {ι : Type*} {X : Type u} {Y : Type v}
    (ρ : ι → X → Y) {x y z : X}
    (hxy : ReceiverEq ρ x y) (hyz : ReceiverEq ρ y z) :
    ReceiverEq ρ x z :=
  fun i ↦ (hxy i).trans (hyz i)

/--
A compression is exact for its declared receiver family when every receiver
factors through the quotient map.
-/
structure Compression (ι : Type*) (X : Type u) (Q : Type v) (Y : Type w) where
  quotient : X → Q
  receiver : ι → X → Y
  factor : ι → Q → Y
  exact : ∀ i x, factor i (quotient x) = receiver i x

theorem Compression.receiver_eq_of_quotient_eq
    {ι : Type*} {X : Type u} {Q : Type v} {Y : Type w}
    (c : Compression ι X Q Y) {x y : X}
    (h : c.quotient x = c.quotient y) :
    ReceiverEq c.receiver x y := by
  intro i
  rw [← c.exact i x, ← c.exact i y, h]

/-! ## One receiver transforms into another only through its retained fibre -/

/--
The relation presented by two receivers over the same situated occurrence population.

It is deliberately a relation before any single-valuedness claim: one entering face may still
carry several returned faces when the entering receiver forgot a distinction needed later.
-/
def receiverToReceiverRelation {X : Type u} {Entering : Type v} {Returned : Type w}
    (entering : X → Entering) (returned : X → Returned) : Rel Entering Returned :=
  fun enteringFace returnedFace ↦
    ∃ occurrence, entering occurrence = enteringFace ∧ returned occurrence = returnedFace

/--
A functional receiver-to-receiver transformer on the actually presented entering face.

The domain is `Set.range entering`, not the whole exterior carrier: an unpresented foreign
coordinate owes no invented returned value.
-/
structure ReceiverTransformer {X : Type u} {Entering : Type v} {Returned : Type w}
    (entering : X → Entering) (returned : X → Returned) where
  transform : Set.range entering → Returned
  exact : ∀ occurrence,
    transform ⟨entering occurrence, ⟨occurrence, rfl⟩⟩ = returned occurrence

/-- The complete situated population behind one actually presented entering face. -/
def receiverReconstructionFibre {X : Type u} {Entering : Type v}
    (entering : X → Entering) (face : Set.range entering) : Type u :=
  { occurrence : X // entering occurrence = face.1 }

/--
The exact descent criterion: an entering receiver determines the returned receiver precisely when
every pair it identifies is also identified by the returned receiver.
-/
theorem receiverTransformer_exists_iff
    {X : Type u} {Entering : Type v} {Returned : Type w}
    (entering : X → Entering) (returned : X → Returned) :
    Nonempty (ReceiverTransformer entering returned) ↔
      ∀ left right, entering left = entering right → returned left = returned right := by
  constructor
  · rintro ⟨transformer⟩ left right sameEntering
    let leftFace : Set.range entering := ⟨entering left, ⟨left, rfl⟩⟩
    let rightFace : Set.range entering := ⟨entering right, ⟨right, rfl⟩⟩
    have sameFace : leftFace = rightFace := Subtype.ext sameEntering
    exact calc
      returned left = transformer.transform leftFace := (transformer.exact left).symm
      _ = transformer.transform rightFace := congrArg transformer.transform sameFace
      _ = returned right := transformer.exact right
  · intro identified
    classical
    refine ⟨{
      transform := fun face ↦ returned (Classical.choose face.property)
      exact := ?_
    }⟩
    intro occurrence
    exact identified _ occurrence (Classical.choose_spec
      (show entering occurrence ∈ Set.range entering from ⟨occurrence, rfl⟩))

/-- A returned distinction inside one entering fibre is an exact insufficiency witness. -/
structure ReceiverInsufficiency {X : Type u} {Entering : Type v} {Returned : Type w}
    (entering : X → Entering) (returned : X → Returned) where
  left : X
  right : X
  sameEntering : entering left = entering right
  differentReturned : returned left ≠ returned right

/-- A functional transformer and an insufficiency witness cannot inhabit the same receiver span. -/
theorem ReceiverTransformer.excludesInsufficiency
    {X : Type u} {Entering : Type v} {Returned : Type w}
    {entering : X → Entering} {returned : X → Returned}
    (transformer : ReceiverTransformer entering returned)
    (insufficiency : ReceiverInsufficiency entering returned) : False := by
  exact insufficiency.differentReturned
    ((receiverTransformer_exists_iff entering returned).mp ⟨transformer⟩
      insufficiency.left insufficiency.right insufficiency.sameEntering)

/-- Distinct entering faces may lawfully condense into one returned face. -/
structure ReceiverCondensation {X : Type u} {Entering : Type v} {Returned : Type w}
    {entering : X → Entering} {returned : X → Returned}
    (transformer : ReceiverTransformer entering returned) where
  left : Set.range entering
  right : Set.range entering
  distinctEntering : left ≠ right
  sameReturned : transformer.transform left = transformer.transform right

end Soma.Holonics
