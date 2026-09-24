import Holonics.Foundation.Holon
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Presentations of one affine relation, and the rebase between them

[definition] A linear or affine relation over a commutative ring **is** an origin together with
the span of a generating family. The generating family is a *presentation*: a chart, not the
object. Two presentations that span the same directions, and whose origins differ by one of
those directions, carry literally the same subset of `X × Y`, hence the same domain, the same
image and the same fibre over every point. Passing between them is a **rebase**: invertible,
with no residual.

This is the formal statement the resident owner needs.
`crates/holonic-engine/src/native_ecology/constitutive_fibre/field/material_transport/normal/
direct/wave/family/receiver.rs::NormalWaveFamily::read_prospective` carries a prospective future
in either of two charts — an expanded composite relation, or the retained ordered word applied to
this family's own receiver point — and `kernels/exact_resident_section.cu::fibre_rebase_step`
rescales one elimination row against its pivot before the products. Neither changes the relation;
both change only its presentation. The device test
`rebase_and_expansion_read_the_same_future` is `Rebase.carrier_eq` read at the receiver.

`Foundation/Holon.lean::Rebase` is the same word one grain up: an equivalence of complete holon
diagrams, where the occurrence population and both addressed ports travel through commuting
squares. This file is its linear-relation instance, where the "commuting squares" are the equality
of two spans.

The hypotheses are load-bearing: `presentationsWithDifferentSpansDiffer` constructs two
presentations over `ℤ` with different carriers, so `Rebase` is not vacuous in either direction.
-/

namespace Holonics.Foundation.RelationPresentation

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- An affine presentation: an origin and an indexed generating family of directions.
The relation itself is `carrier`; this structure is one chart of it. -/
structure Presentation (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V]
    (ι : Type*) where
  origin : V
  direction : ι → V

variable {ι κ μ : Type*}

/-- The directions a presentation spans. -/
def Presentation.span (p : Presentation R V ι) : Submodule R V :=
  Submodule.span R (Set.range p.direction)

/-- The relation a presentation carries: its origin translated by its own span. -/
def Presentation.carrier (p : Presentation R V ι) : Set V :=
  {v | v - p.origin ∈ p.span}

theorem Presentation.origin_mem (p : Presentation R V ι) : p.origin ∈ p.carrier := by
  simp [Presentation.carrier]

theorem Presentation.mem_carrier_iff (p : Presentation R V ι) (v : V) :
    v ∈ p.carrier ↔ v - p.origin ∈ p.span := Iff.rfl

/--
[definition] **A rebase of presentations.** The two charts span the same directions, and their
origins differ by one of those directions. Nothing else is required, and nothing weaker suffices.
-/
def Rebase (p : Presentation R V ι) (q : Presentation R V κ) : Prop :=
  p.span = q.span ∧ q.origin - p.origin ∈ p.span

namespace Rebase

theorem refl (p : Presentation R V ι) : Rebase p p := by
  refine ⟨rfl, ?_⟩
  simp

/-- [proved-derived] A rebase carries the identical relation: its residual is empty. -/
theorem carrier_eq {p : Presentation R V ι} {q : Presentation R V κ} (h : Rebase p q) :
    p.carrier = q.carrier := by
  obtain ⟨hspan, horigin⟩ := h
  ext v
  constructor
  · intro hv
    have : v - q.origin = (v - p.origin) - (q.origin - p.origin) := by abel
    rw [Presentation.mem_carrier_iff, this, ← hspan]
    exact Submodule.sub_mem _ hv horigin
  · intro hv
    have : v - p.origin = (v - q.origin) + (q.origin - p.origin) := by abel
    rw [Presentation.mem_carrier_iff, this]
    exact Submodule.add_mem _ (by rw [hspan]; exact hv) horigin

/-- [proved-derived] The rebase is invertible: the inverse chart change is a rebase. -/
theorem symm {p : Presentation R V ι} {q : Presentation R V κ} (h : Rebase p q) : Rebase q p := by
  obtain ⟨hspan, horigin⟩ := h
  refine ⟨hspan.symm, ?_⟩
  have : p.origin - q.origin = -(q.origin - p.origin) := by abel
  rw [this, ← hspan]
  exact Submodule.neg_mem _ horigin

/-- [proved-derived] Rebases compose, so a word of chart changes is one chart change. -/
theorem trans {p : Presentation R V ι} {q : Presentation R V κ} {r : Presentation R V μ}
    (h : Rebase p q) (h' : Rebase q r) : Rebase p r := by
  obtain ⟨hspan, horigin⟩ := h
  obtain ⟨hspan', horigin'⟩ := h'
  refine ⟨hspan.trans hspan', ?_⟩
  have : r.origin - p.origin = (r.origin - q.origin) + (q.origin - p.origin) := by abel
  rw [this]
  exact Submodule.add_mem _ (by rw [hspan]; exact horigin') horigin

/-- [proved-derived] Nothing is gained and nothing is lost: the residual in both directions is
empty. This is the "zero residual" the construction contract asks a chart change to carry. -/
theorem residual_empty {p : Presentation R V ι} {q : Presentation R V κ} (h : Rebase p q) :
    p.carrier \ q.carrier = ∅ ∧ q.carrier \ p.carrier = ∅ := by
  rw [h.carrier_eq]
  exact ⟨Set.sdiff_self, Set.sdiff_self⟩

end Rebase

section Faces

variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/-- The source face of a relation inside `X × Y`. -/
def domain (S : Set (X × Y)) : Set X := Prod.fst '' S

/-- The target face. -/
def image (S : Set (X × Y)) : Set Y := Prod.snd '' S

/-- The fibre retained over one source point: the complete preimage, never a selected member. -/
def fibre (S : Set (X × Y)) (x : X) : Set Y := {y | (x, y) ∈ S}

/-- [proved-derived] Row-equivalent presentations of a relation have equal domain, equal image
and equal fibre over every point. Every receiver reading that is a function of the relation is
therefore identical before and after the rebase. -/
theorem Rebase.faces_eq {p : Presentation R (X × Y) ι} {q : Presentation R (X × Y) κ}
    (h : Rebase p q) :
    domain p.carrier = domain q.carrier ∧
      image p.carrier = image q.carrier ∧
      ∀ x, fibre p.carrier x = fibre q.carrier x := by
  rw [h.carrier_eq]
  exact ⟨rfl, rfl, fun _ => rfl⟩

end Faces

section NonInstance

/-- [proved-derived] A constructed NON-instance: two presentations over `ℤ` with different spans
and different carriers. The rebase hypothesis is doing work; `carrier_eq` is not vacuously true
of any two presentations, and a chart change that alters the span is not a rebase. -/
theorem presentationsWithDifferentSpansDiffer :
    ∃ (p q : Presentation ℤ ℤ Unit), ¬ Rebase p q ∧ p.carrier ≠ q.carrier := by
  refine ⟨⟨0, fun _ => 1⟩, ⟨0, fun _ => 0⟩, ?_, ?_⟩
  · rintro ⟨hspan, -⟩
    have h1 : (1 : ℤ) ∈ Submodule.span ℤ (Set.range (fun _ : Unit => (1 : ℤ))) :=
      Submodule.subset_span ⟨(), rfl⟩
    rw [show Submodule.span ℤ (Set.range (fun _ : Unit => (1 : ℤ)))
        = (⟨0, fun _ => (1 : ℤ)⟩ : Presentation ℤ ℤ Unit).span from rfl, hspan] at h1
    have h0 : (⟨0, fun _ => (0 : ℤ)⟩ : Presentation ℤ ℤ Unit).span = ⊥ := by
      simp [Presentation.span, Set.range_const]
    rw [h0] at h1
    exact absurd (Submodule.mem_bot ℤ |>.mp h1) one_ne_zero
  · intro h
    have h1 : (1 : ℤ) ∈ (⟨0, fun _ => (1 : ℤ)⟩ : Presentation ℤ ℤ Unit).carrier := by
      have h : (1 : ℤ) ∈ Submodule.span ℤ (Set.range (fun _ : Unit => (1 : ℤ))) :=
        Submodule.subset_span ⟨(), rfl⟩
      simp [Presentation.carrier, Presentation.span, h]
    rw [h] at h1
    have h0 : (⟨0, fun _ => (0 : ℤ)⟩ : Presentation ℤ ℤ Unit).span = ⊥ := by
      simp [Presentation.span, Set.range_const]
    rw [Presentation.mem_carrier_iff, h0] at h1
    simp at h1

end NonInstance

section Audit

#print axioms Rebase.carrier_eq
#print axioms Rebase.symm
#print axioms Rebase.trans
#print axioms Rebase.residual_empty
#print axioms Rebase.faces_eq
#print axioms presentationsWithDifferentSpansDiffer

end Audit

end Holonics.Foundation.RelationPresentation
