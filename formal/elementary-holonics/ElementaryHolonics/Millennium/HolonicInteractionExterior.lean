import ElementaryHolonics.Geometry.SixSphereMonodromy
import ElementaryHolonics.Millennium.HolonicDifferenceCalculus
import Mathlib.Tactic

/-!
# Exterior transport and constitutive storage for the six-sphere torus family

The torus monodromies do not act only on fibre vectors.  They act functorially on oriented
two-planes, the carrier of flux and curl before a Hodge receiver selects a vector chart.  This file
constructs the exterior-square action in the ordered basis

```text
e01, e02, e03, e12, e13, e23.
```

The finite monodromies admit positive invariant storage by summing the ordinary square storage over
one complete orbit.  The cusp is different.  Its vector defect is square-zero, but its induced
bivector defect is cubic-zero and not square-zero.  The orbit of `e01` is therefore quadratic: its
second returned difference is the constant flux plane `2 e23`, and its third returned difference is
zero.  A nontrivial square-zero shear cannot preserve a definite bilinear storage form.

Truth status: `[proved-derived] [formal-checked]` for every theorem below, relative to the exact
integral monodromy matrices already checked in `SixSphereMonodromy.lean`.
-/

namespace Soma.Holonics.Millennium.HolonicInteractionExterior

open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Millennium.HolonicDifferenceCalculus
open scoped BigOperators

/-! ## The exact exterior-square transport -/

/-- Coordinates of an oriented two-plane in a rank-four lattice. -/
abbrev FluxPlane := Fin 6 → ℤ

/-- First index of the ordered basis `01, 02, 03, 12, 13, 23`. -/
def bladeFirst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- Second index of the ordered basis `01, 02, 03, 12, 13, 23`. -/
def bladeSecond : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- The second exterior power of a rank-four integral transport, in the ordered blade basis. -/
def exteriorSquareAction (M : LatticeEnd) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun row column ↦
    M (bladeFirst row) (bladeFirst column) *
        M (bladeSecond row) (bladeSecond column) -
      M (bladeFirst row) (bladeSecond column) *
        M (bladeSecond row) (bladeFirst column)

/-- The exact cusp transport on oriented flux planes. -/
def cuspFluxTransport : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     1, 0, 0, 0, 1, 0;
     1, 1, 0, 0, 1, 1]

/-- The displayed six-dimensional transport is literally `Λ² M₀`, not a fitted receiver
matrix. -/
theorem cuspFluxTransport_isExteriorSquare :
    cuspFluxTransport = exteriorSquareAction M0 := by
  decide

/-- The finite elliptic returns remain finite on oriented flux planes. -/
theorem exteriorSquare_A1_orderThree : (exteriorSquareAction A1) ^ 3 = 1 := by
  decide

theorem exteriorSquare_A2_orderFour : (exteriorSquareAction A2) ^ 4 = 1 := by
  decide

/-- All three dual monodromies conserve the oriented four-volume even though their lower exterior
powers have different return laws. -/
theorem dualMonodromies_preserveOrientedVolume :
    A1.det = 1 ∧ A2.det = 1 ∧ M0.det = 1 := by
  decide

/-- The returned defect on flux planes. -/
def cuspFluxDefect : Matrix (Fin 6) (Fin 6) ℤ := cuspFluxTransport - 1

/-- Exterior transport raises the nilpotence order: the flux-plane defect is cubic-zero. -/
theorem cuspFluxDefect_cubicZero : cuspFluxDefect ^ 3 = 0 := by
  decide

/-- The flux-plane defect is genuinely second order, unlike the square-zero vector defect. -/
theorem cuspFluxDefect_squareNonzero : cuspFluxDefect ^ 2 ≠ 0 := by
  decide

/-- The exact cusp orbit of the initial plane `e₀∧e₁`. -/
def cuspFluxOrbit (time : ℕ) : FluxPlane :=
  ![1, (time : ℤ), 0, 0, (time : ℤ), (time : ℤ) ^ 2]

/-- One cusp transport advances the complete quadratic flux orbit. -/
theorem cuspFluxTransport_advancesOrbit (time : ℕ) :
    cuspFluxTransport.mulVec (cuspFluxOrbit time) = cuspFluxOrbit (time + 1) := by
  ext i
  fin_cases i <;>
    simp [cuspFluxTransport, cuspFluxOrbit, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The orbit begins at the basis plane `e₀∧e₁`. -/
theorem cuspFluxOrbit_zero : cuspFluxOrbit 0 = ![1, 0, 0, 0, 0, 0] := by
  decide

/-- Iterating the induced monodromy returns the displayed quadratic orbit at every time. -/
theorem cuspFluxTransport_pow_onInitialPlane (time : ℕ) :
    (cuspFluxTransport ^ time).mulVec ![1, 0, 0, 0, 0, 0] = cuspFluxOrbit time := by
  induction time with
  | zero => simp [cuspFluxOrbit]
  | succ time ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, cuspFluxTransport_advancesOrbit]

/-- The plane orbit has a constant nonzero second returned difference. -/
theorem cuspFluxOrbit_secondDifference (time : ℕ) :
    secondDifference cuspFluxOrbit time = ![0, 0, 0, 0, 0, 2] := by
  ext i
  fin_cases i <;>
    simp [secondDifference, firstDifference, cuspFluxOrbit] <;>
    ring

/-- Its third returned difference vanishes exactly. -/
theorem cuspFluxOrbit_thirdDifference (time : ℕ) :
    iteratedDifference 3 cuspFluxOrbit time = 0 := by
  ext i
  fin_cases i <;>
    simp [iteratedDifference, firstDifference, cuspFluxOrbit] <;>
    ring

/-! ## Positive cyclic storage at the finite returns -/

/-- Ordinary exact square storage on the integral lattice. -/
def latticeSquareStorage (v : Lattice) : ℤ := ∑ i, v i ^ 2

theorem latticeSquareStorage_nonnegative (v : Lattice) : 0 ≤ latticeSquareStorage v := by
  simp [latticeSquareStorage, Fin.sum_univ_succ]
  positivity

theorem latticeSquareStorage_positive (v : Lattice) (hv : v ≠ 0) :
    0 < latticeSquareStorage v := by
  have hcoordinates : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  simp [latticeSquareStorage, Fin.sum_univ_succ]
  rcases hcoordinates with h | h | h | h <;>
    nlinarith [sq_pos_of_ne_zero h]

/-- Storage summed over one complete finite transport orbit. -/
def cyclicStorage (M : LatticeEnd) (order : ℕ) (v : Lattice) : ℤ :=
  ∑ step ∈ Finset.range order, latticeSquareStorage ((M ^ step).mulVec v)

/-- Summing a storage reading over a complete finite orbit makes it transport-invariant. -/
theorem cyclicStorage_invariant_of_pow_eq_one
    (M : LatticeEnd) (order : ℕ) (horder : M ^ order = 1) (v : Lattice) :
    cyclicStorage M order (M.mulVec v) = cyclicStorage M order v := by
  let f : ℕ → ℤ := fun step ↦ latticeSquareStorage ((M ^ step).mulVec v)
  have hterminal : f order = f 0 := by
    simp [f, horder]
  have htel := Soma.Holonics.finite_telescoping f order
  have hshift :
      (∑ step ∈ Finset.range order, f (step + 1)) =
        ∑ step ∈ Finset.range order, f step := by
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib, htel, hterminal, sub_self]
  unfold cyclicStorage
  have hadvance (step : ℕ) :
      latticeSquareStorage ((M ^ step).mulVec (M.mulVec v)) = f (step + 1) := by
    rw [Matrix.mulVec_mulVec, ← pow_succ]
  simp_rw [hadvance]
  exact hshift

/-- The order-three monodromy carries a positive, exactly invariant capacitance form. -/
theorem A1_cyclicStorage_invariant (v : Lattice) :
    cyclicStorage A1 3 (A1.mulVec v) = cyclicStorage A1 3 v := by
  exact cyclicStorage_invariant_of_pow_eq_one A1 3 (by decide) v

/-- The order-four monodromy carries its own positive, exactly invariant capacitance form. -/
theorem A2_cyclicStorage_invariant (v : Lattice) :
    cyclicStorage A2 4 (A2.mulVec v) = cyclicStorage A2 4 v := by
  exact cyclicStorage_invariant_of_pow_eq_one A2 4 (by decide) v

theorem A1_cyclicStorage_positive (v : Lattice) (hv : v ≠ 0) :
    0 < cyclicStorage A1 3 v := by
  apply Finset.sum_pos'
  · intro step _
    exact latticeSquareStorage_nonnegative _
  · refine ⟨0, by simp, ?_⟩
    simpa using latticeSquareStorage_positive v hv

theorem A2_cyclicStorage_positive (v : Lattice) (hv : v ≠ 0) :
    0 < cyclicStorage A2 4 v := by
  apply Finset.sum_pos'
  · intro step _
    exact latticeSquareStorage_nonnegative _
  · refine ⟨0, by simp, ?_⟩
    simpa using latticeSquareStorage_positive v hv

/-! ## A fixed definite storage form cannot absorb the cusp shear -/

/-- A square-zero shear which preserves a bilinear storage form forces every shear direction to
be null for that form. -/
theorem invariantStorage_makesSquareZeroDefectNull
    {V R : Type*} [AddCommGroup V] [AddCommGroup R]
    (B : V → V → R) (N : V → V)
    (haddLeft : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsquare : ∀ x, N (N x) = 0)
    (hinvariant : ∀ x y, B (x + N x) (y + N y) = B x y)
    (x : V) :
    B (N x) (N x) = 0 := by
  have h := hinvariant x (N x)
  rw [hsquare, add_zero, haddLeft] at h
  have h' : B x (N x) + B (N x) (N x) = B x (N x) + 0 := by
    simpa using h
  exact add_left_cancel h'

/-- The dual cusp's square-zero vector defect, written in source coordinates. -/
def dualCuspDefect (v : Lattice) : Lattice := ![0, 0, v 1, -v 0]

theorem dualCuspDefect_eq_matrixDifference (v : Lattice) :
    dualCuspDefect v = (M0 - 1).mulVec v := by
  ext i
  fin_cases i <;>
    simp [dualCuspDefect, M0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem dualCuspDefect_squareZero (v : Lattice) :
    dualCuspDefect (dualCuspDefect v) = 0 := by
  ext i
  fin_cases i <;> simp [dualCuspDefect]

theorem dualCuspDefect_nontrivial :
    dualCuspDefect ![1, 0, 0, 0] ≠ 0 := by
  decide

/-- No definite bilinear storage form can remain fixed under the nontrivial cusp shear.  A lawful
constitutive model must therefore transport its metric with the shear or return the accumulated
deformation to a relaxation/dissipation law. -/
theorem noDefiniteInvariantStorage_forDualCusp
    (B : Lattice → Lattice → ℤ)
    (haddLeft : ∀ x y z, B (x + y) z = B x z + B y z)
    (hinvariant : ∀ x y,
      B (x + dualCuspDefect x) (y + dualCuspDefect y) = B x y)
    (hdefinite : ∀ x, B x x = 0 → x = 0) :
    False := by
  let probe : Lattice := ![1, 0, 0, 0]
  have hnull : B (dualCuspDefect probe) (dualCuspDefect probe) = 0 :=
    invariantStorage_makesSquareZeroDefectNull B dualCuspDefect haddLeft
      dualCuspDefect_squareZero hinvariant probe
  exact dualCuspDefect_nontrivial (hdefinite _ hnull)

end Soma.Holonics.Millennium.HolonicInteractionExterior

section Audit
open Soma.Holonics.Millennium.HolonicInteractionExterior
#print axioms cuspFluxTransport_isExteriorSquare
#print axioms exteriorSquare_A1_orderThree
#print axioms exteriorSquare_A2_orderFour
#print axioms dualMonodromies_preserveOrientedVolume
#print axioms cuspFluxDefect_cubicZero
#print axioms cuspFluxDefect_squareNonzero
#print axioms cuspFluxTransport_pow_onInitialPlane
#print axioms cuspFluxOrbit_secondDifference
#print axioms cuspFluxOrbit_thirdDifference
#print axioms A1_cyclicStorage_invariant
#print axioms A2_cyclicStorage_invariant
#print axioms A1_cyclicStorage_positive
#print axioms A2_cyclicStorage_positive
#print axioms noDefiniteInvariantStorage_forDualCusp
end Audit
