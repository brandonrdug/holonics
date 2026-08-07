import Mathlib.Logic.Relation

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

end Soma.Holonics

