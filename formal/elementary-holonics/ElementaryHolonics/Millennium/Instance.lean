import Mathlib.GroupTheory.QuotientGroup.Basic
import ElementaryHolonics.Millennium.Coupling
import ElementaryHolonics.Millennium.Paying

/-!
# One standing remainder, exhibited as a chain position

The coupling record left this open: the four named remainders were *argued* to be positions on a
transport chain and none was *exhibited* as one.  This file closes it for the descent, and closes
it sharply — not merely "it is a position" but **which** position.

The chain is doubling followed by reduction modulo what doubling reached.  It is exact at the
middle, so its homology is trivial; the descent's representative set lives at the chain's
**target**, which is the obstruction group of the doubling passage.  The descent theorem then reads:
**a transversal of the target, together with a bounded core, generates the source.**

Every `theorem` here is discharged.
-/

namespace Soma.Holonics.Millennium.Instance

open Soma.Holonics.Millennium Soma.Holonics.Millennium.Coupling
open Soma.Holonics.Millennium.Paying

universe u

variable {G : Type u} [AddCommGroup G]

/-! ## 1. Doubling, and the chain it generates -/

/-- **Doubling**, as a transport. -/
def doublingHom (G : Type u) [AddCommGroup G] : G →+ G where
  toFun g := g + g
  map_zero' := by simp
  map_add' := by intro a b; abel

@[simp] theorem doublingHom_apply (g : G) : doublingHom G g = g + g := rfl

/-- What doubling reaches. -/
def doubled (G : Type u) [AddCommGroup G] : AddSubgroup G := (doublingHom G).range

/-- **The doubling chain**: double, then reduce modulo what doubling reached. -/
def doublingChain (G : Type u) [AddCommGroup G] :
    TransportChain G G (G ⧸ doubled G) where
  into := doublingHom G
  outOf := QuotientAddGroup.mk' (doubled G)
  composite_zero := by
    intro a
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨a, rfl⟩

/-- **The doubling chain is exact at the middle**: what the reduction retains is exactly what
doubling realized, so the homology there is trivial. -/
theorem theDoublingChainIsExact : (doublingChain G).toPassage.Glues := by
  intro b hb
  exact (QuotientAddGroup.eq_zero_iff _).mp hb

/-- **So its coupling remainder vanishes.**  The descent's content is therefore *not* at the
middle — it is at the target. -/
theorem theDoublingChainHasNoCouplingRemainder :
    Subsingleton (doublingChain G).toPassage.ObstructionGroup :=
  (TransportChain.theCouplingRemainderIsTheHomology _).mp theDoublingChainIsExact

/-! ## 2. The descent's representatives live at the chain's target -/

variable (D : DescentData G)

/-- **Every class at the chain's target has a representative among the descent's.**

The splitting law says each element is a representative plus a double, which is exactly the
statement that the representatives meet every class modulo what doubling reached. -/
theorem theRepsCoverTheTarget :
    ∀ x : G ⧸ doubled G, ∃ r ∈ D.reps, (QuotientAddGroup.mk r : G ⧸ doubled G) = x := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H b =>
    obtain ⟨r, hr, g', hsplit⟩ := D.splits b
    refine ⟨r, hr, QuotientAddGroup.eq.mpr ?_⟩
    refine ⟨g', ?_⟩
    rw [hsplit]
    simp only [doublingHom_apply]
    abel

/-- **Therefore the target is finite.**  The descent's finiteness hypothesis on its representative
set is exactly the finiteness of the chain's target — the obstruction group of the doubling
passage. -/
theorem theTargetIsFinite (D : DescentData G) : Finite (G ⧸ doubled G) := by
  have hsurj : Function.Surjective
      (fun r : {x // x ∈ D.reps} => (QuotientAddGroup.mk r.1 : G ⧸ doubled G)) := by
    intro x
    obtain ⟨r, hr, hx⟩ := theRepsCoverTheTarget D x
    exact ⟨⟨r, hr⟩, hx⟩
  exact Finite.of_surjective _ hsurj

/-- **The descent, placed.**

A transversal of the chain's target, together with a bounded core, generates the source.  That is
the descent theorem restated at its chain position: the finite data sits at the target, the middle
is exact and contributes nothing, and what the two together supply is the whole source. -/
theorem theTransversalAndTheCoreGenerateTheSource
    (hfin : {x : G | D.size x ≤ D.bound}.Finite) :
    (∀ x : G ⧸ doubled G, ∃ r ∈ D.reps, (QuotientAddGroup.mk r : G ⧸ doubled G) = x) ∧
      ∃ S : Finset G, AddSubgroup.closure (S : Set G) = ⊤ :=
  ⟨theRepsCoverTheTarget D, D.theDescentComposesAFiniteAtlas hfin⟩

/-- **And the exactness is what makes the placement unambiguous.**  Were the middle inexact, the
descent would owe a second piece of finite data there; it does not, and this is why. -/
theorem theDescentOwesNothingAtTheMiddle :
    (doublingChain G).retained ≤ (doublingChain G).realized :=
  theDoublingChainIsExact

end Soma.Holonics.Millennium.Instance
