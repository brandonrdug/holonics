import ElementaryHolonics.Millennium.Coupling
import ElementaryHolonics.Millennium.Theta
import ElementaryHolonics.Millennium.Triangle

/-!
# The collapsed population is a chain position — and on one object, three names coincide

What a declared receiver family cannot separate has been named in this development since the
gluing frame was written, and never placed.  It is placed here: **the collapsed population is the
retained position of the chain whose outgoing transport is the receiver.**

That is the same position the compressed-positivity remainder occupies, so *what the receiver
cannot separate* and *what the aperture does not admit* are one position and not two.

Section 3 exhibits it on the theta complex, where the identification is threefold: the cycles are
simultaneously the chain's retained population, the radical of the boundary-pullback form, and the
collapsed population of the boundary reading.  **Three names, one subgroup, on a real object.**

Every `theorem` here is discharged.
-/

namespace Soma.Holonics.Millennium.Receiver

open Soma.Holonics.Millennium Soma.Holonics.Millennium.Coupling

/-! ## 1. An additive receiver family and what it collapses -/

universe u

variable {ι X V : Type u} [AddCommGroup X] [AddCommGroup V] (read : ι → (X →+ V))

/-- The **collapsed population**: what no reading in the family can see. -/
def collapsedPopulation : AddSubgroup X := ⨅ i, (read i).ker

/-- The family read all at once. -/
def jointReading : X →+ (ι → V) where
  toFun x := fun i => read i x
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

@[simp] theorem jointReading_apply (x : X) (i : ι) : jointReading read x i = read i x := rfl

/-- **The collapsed population is the kernel of the family read all at once.** -/
theorem theCollapsedIsTheJointKernel :
    (jointReading read).ker = collapsedPopulation read := by
  ext x
  simp [collapsedPopulation, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, funext_iff]

/-- **Two constructions are unseparated exactly when their difference is collapsed.**

This is what makes the collapsed population a subgroup rather than a relation: with additive
readings, indistinguishability is a coset condition. -/
theorem unseparatedIffDifferenceCollapsed (a b : X) :
    (∀ i, read i a = read i b) ↔ (b - a) ∈ collapsedPopulation read := by
  simp only [collapsedPopulation, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, map_sub,
    sub_eq_zero]
  exact forall_congr' fun _ => eq_comm

/-! ## 2. The placement -/

variable {A : Type u} [AddCommGroup A]

/-- A chain whose outgoing transport is the receiver family. -/
def receiverChain (into : A →+ X) (h : ∀ a : A, ∀ i : ι, read i (into a) = 0) :
    TransportChain A X (ι → V) where
  into := into
  outOf := jointReading read
  composite_zero := by
    intro a
    funext i
    exact h a i

/-- **The collapsed population is the chain's retained position.**

The same position the compressed-positivity remainder occupies.  What a receiver cannot separate
and what an aperture does not admit are one position, not two. -/
theorem theCollapsedIsTheRetainedPosition (into : A →+ X)
    (h : ∀ a : A, ∀ i : ι, read i (into a) = 0) :
    (receiverChain read into h).retained = collapsedPopulation read :=
  theCollapsedIsTheJointKernel read

/-- **And the homology is the collapsed population modulo what was supplied.**  A chain glues
exactly when everything the receiver cannot separate was already realized. -/
theorem theChainGluesIffTheCollapsedWasRealized (into : A →+ X)
    (h : ∀ a : A, ∀ i : ι, read i (into a) = 0) :
    (receiverChain read into h).toPassage.Glues ↔
      collapsedPopulation read ≤ (receiverChain read into h).realized := by
  rw [TransportChain.theChainGluesIffItIsExactAtTheMiddle,
    theCollapsedIsTheRetainedPosition read into h]

/-! ## 3. Three names, one subgroup, on the theta complex -/

open Soma.Holonics.Millennium.Theta

/-- The boundary, read as a one-reading receiver family. -/
def boundaryReading : Unit → (Edges →+ Verts) := fun _ => d1

/-- **The cycles are what the boundary reading collapses.** -/
theorem theCyclesAreTheCollapsedPopulation :
    collapsedPopulation boundaryReading = d1.ker := by
  ext x
  simp [collapsedPopulation, boundaryReading, AddSubgroup.mem_iInf]

/-- **The cycles are the radical of the boundary-pullback form.** -/
theorem theCyclesAreTheRadical (e : Edges) : e ∈ thetaDatum.radical ↔ d1 e = 0 := by
  constructor
  · rintro ⟨-, h⟩
    have hself : thetaForm e e = 0 := h e (by trivial)
    rw [thetaForm_apply, pair2_apply] at hself
    have hz : (d1 e).1 * (d1 e).1 + (d1 e).2 * (d1 e).2 = 0 := by exact_mod_cast hself
    have h1 : (d1 e).1 = 0 := by nlinarith [mul_self_nonneg (d1 e).1, mul_self_nonneg (d1 e).2]
    have h2 : (d1 e).2 = 0 := by nlinarith [mul_self_nonneg (d1 e).1, mul_self_nonneg (d1 e).2]
    exact Prod.ext h1 h2
  · intro h
    exact ⟨trivial, fun w _ => thePullbackVanishesOnCycles h w⟩

/-- **Three names, one subgroup.**

On the theta complex the cycles are at once: what the chain retains, what the boundary-pullback
form cannot see, and what the boundary reading collapses.  The three vocabularies this development
built separately name one object here. -/
theorem theCyclesAreRetainedRadicalAndCollapsed :
    thetaChain.retained = collapsedPopulation boundaryReading
      ∧ ∀ e : Edges, e ∈ thetaChain.retained ↔ e ∈ thetaDatum.radical := by
  constructor
  · rw [theCyclesAreTheCollapsedPopulation]
    rfl
  · intro e
    rw [theCyclesAreTheRadical]
    rfl

/-- **And the surviving loop witnesses all three at once**: it is retained, it is in the radical,
and the boundary reading cannot separate it from zero — yet nothing realizes it. -/
theorem theSurvivingLoopWitnessesAllThree :
    ((0, 1, -1) : Edges) ∈ thetaChain.retained
      ∧ ((0, 1, -1) : Edges) ∈ thetaDatum.radical
      ∧ ((0, 1, -1) : Edges) ∈ collapsedPopulation boundaryReading
      ∧ ((0, 1, -1) : Edges) ∉ thetaChain.realized := by
  refine ⟨theSurvivingLoopIsRetained, ?_, ?_, theSurvivingLoopIsNotRealized⟩
  · exact (theCyclesAreTheRadical _).mpr theSurvivingLoopIsRetained
  · rw [theCyclesAreTheCollapsedPopulation]
    exact theSurvivingLoopIsRetained

/-! ## 4. A declared field is not a derived object

The previous record tabulated the compressed-positivity **remainder** as sitting at the chain's
retained position.  That row was unsupported and is corrected here.

`CompressedPositivity.remainder` is a *field* — an input naming what the declared aperture does not
admit.  The chain's retained population and the form's radical are *computed*.  **Only derived
objects can coincide non-trivially; a declared one agreeing with a derived one is a choice.** -/

open Soma.Holonics.Millennium.Triangle in
/-- **On the theta complex the declared remainder and the derived retained population differ.**

The datum declares that its aperture admits nothing, so its remainder is everything; the chain
retains only the cycles.  A single edge is in one and not the other. -/
theorem theRemainderIsNotTheRetained : thetaDatum.remainder ≠ thetaChain.retained := by
  intro h
  have h1 : ((1, 0, 0) : Edges) ∈ thetaDatum.remainder := trivial
  rw [h] at h1
  have h2 : d1 ((1, 0, 0) : Edges) = 0 := h1
  simp [d1] at h2

open Soma.Holonics.Millennium.Triangle in
/-- **On the hollow triangle they do coincide — because the datum was declared that way.**

Definitional equality, not a theorem about the object. That is exactly the point. -/
theorem theHollowRemainderEqualsRetained :
    hollowTriangleDatum.remainder = hollowTriangleChain.retained := rfl

open Soma.Holonics.Millennium.Triangle in
/-- **Two data over one carrier may declare different remainders.**

So no general statement relates a remainder to any derived object, and the previous record's row
placing the remainder at the retained position is withdrawn. -/
theorem twoDataDeclareDifferentRemainders :
    thetaDatum.remainder ≠ hollowTriangleDatum.remainder := by
  intro h
  have h1 : ((1, 0, 0) : Edges) ∈ thetaDatum.remainder := trivial
  rw [h] at h1
  have h2 : Triangle.boundary ((1, 0, 0) : Cells) = 0 := h1
  simp [Triangle.boundary] at h2

/-- **What does coincide, and all three are derived.**

The chain's retained population, the form's radical, and the receiver's collapsed population are
each computed from the object.  Their agreement on the theta complex is therefore a finding; the
remainder's agreement anywhere is a declaration. -/
theorem theThreeDerivedObjectsCoincide :
    thetaChain.retained = collapsedPopulation boundaryReading
      ∧ (∀ e : Edges, e ∈ thetaChain.retained ↔ e ∈ thetaDatum.radical)
      ∧ thetaDatum.remainder ≠ thetaChain.retained :=
  ⟨theCyclesAreRetainedRadicalAndCollapsed.1,
   theCyclesAreRetainedRadicalAndCollapsed.2,
   theRemainderIsNotTheRetained⟩

/-! ## 5. The perp and the radical are different objects, and one witness separates them -/

open Soma.Holonics.Millennium.Triangle in
/-- **On the theta complex a nontrivial cutoff is available.**

Everything is retained there, so the perp is the radical, and the surviving loop inhabits it.  An
aperture may admit the whole loop and lose no positivity. -/
theorem theThetaAdmitsANontrivialCutoff :
    ((0, 1, -1) : Edges) ∈ thetaDatum.perp ∧ ((0, 1, -1) : Edges) ≠ 0 := by
  refine ⟨fun v _ => ?_, ?_⟩
  · exact thePullbackVanishesOnCycles theSurvivingLoopIsRetained v
  · intro h
    have : (1 : ℤ) = 0 := congrArg (fun p : Edges => p.2.1) h
    omega

open Soma.Holonics.Millennium.Triangle in
/-- **On the hollow triangle the perp is strictly larger than the radical.**

The triangle's form is faithful on what it retains, so its radical is trivial — but its remainder
is only the cycles, and plenty is orthogonal to those.  **A nontrivial cutoff is available where no
nontrivial radical is**, so the two objects are genuinely different and the earlier files were
right to keep them apart. -/
theorem theHollowPerpExceedsItsRadical :
    ((1, -1, 0) : Cells) ∈ hollowTriangleDatum.perp
      ∧ ((1, -1, 0) : Cells) ∉ hollowTriangleDatum.radical := by
  constructor
  · intro v hv
    obtain ⟨n, rfl⟩ := (Triangle.theLoopIsTheKernel v).mp hv
    show hollowTriangleDatum.form ((1, -1, 0) : Cells) ((n, n, n) : Cells) = 0
    simp [hollowTriangleDatum]
  · intro h
    have hmem : ((1, -1, 0) : Cells) ∈ Triangle.boundary.ker := h.1
    obtain ⟨n, hn⟩ := (Triangle.theLoopIsTheKernel _).mp hmem
    have h1 : (1 : ℤ) = n := congrArg (fun p : Cells => p.1) hn
    have h2 : (-1 : ℤ) = n := congrArg (fun p : Cells => p.2.1) hn
    omega

end Soma.Holonics.Millennium.Receiver
