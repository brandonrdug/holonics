import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborWorldTube

/-!
# Exact coordinate reduction before Brandt destination classification

The actual Brandt neighbor carrier is defined by a polar kernel together with
one fractional isotropic generator.  A destination classification must act on
that lattice, not merely on its residue direction or on the aggregate `p+1`
count.

This file removes the unbounded polar-kernel presentation.  Whenever the first
polar coefficient is invertible modulo `p`, the integral kernel has the exact
normal form

`(p*q + cY*y + cZ*z, y, z)`.

When the first coefficient vanishes and the second is invertible, it instead
has the exact normal form

`(x, p*q + cZ*z, z)`.

The correction coefficients are computed by the already-founded exact pivot
correction.  Applying these two charts to both Tunnell--Brandt source classes
gives an explicit four-integer surjection onto every actual rational neighbor:
three kernel coordinates and one fractional-generator coordinate.  The map is
not declared injective; its complete fibre is intentionally retained.

Thus the remaining Jones--Pall edge is genuinely the classification of these
explicit returned lattices into the two global integral classes.  It is no
longer mixed with construction of the neighbor population or solution of an
unbounded congruence.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationClassification

open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube

variable {p : ℕ} [Fact p.Prime]

/-! ## A source-neutral exact polar-kernel reduction -/

/-- Four retained integer coordinates: three for the integral polar kernel and
one for the fractional isotropic generator. -/
abbrev NeighborCoordinates := ℤ × ℤ × ℤ × ℤ

/-- The correction which solves `A*c + K = 0 (mod p)`. -/
def modularCorrection (A K : ℤ) : ℤ :=
  pivotCorrection (p := p) (A : ZMod p) K

theorem cast_modularCorrection {A K : ℤ} (hA : (A : ZMod p) ≠ 0) :
    (modularCorrection (p := p) A K : ZMod p) = -(K : ZMod p) / (A : ZMod p) := by
  simpa [modularCorrection, pivotCorrection] using
    ZMod.natCast_zmod_val (-(K : ZMod p) / (A : ZMod p))

/-- Normal form when the first polar coefficient is the invertible pivot. -/
def firstPivotKernelPoint (A B C q y z : ℤ) : IntTriple :=
  ((p : ℤ) * q + modularCorrection (p := p) A B * y +
      modularCorrection (p := p) A C * z,
    y, z)

/-- Normal form when the first polar coefficient vanishes and the second is the
invertible pivot. -/
def secondPivotKernelPoint (B C x q z : ℤ) : IntTriple :=
  (x, (p : ℤ) * q + modularCorrection (p := p) B C * z, z)

/-- Exact reduction of a ternary integral linear congruence through its first
invertible coefficient. -/
theorem firstPivotKernel_iff {A B C : ℤ} (hA : (A : ZMod p) ≠ 0)
    (m : IntTriple) :
    (p : ℤ) ∣ A * m.1 + B * m.2.1 + C * m.2.2 ↔
      ∃ q : ℤ, m = firstPivotKernelPoint (p := p) A B C q m.2.1 m.2.2 := by
  constructor
  · intro hm
    have hcast :
        ((A * m.1 + B * m.2.1 + C * m.2.2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hm
    let cY := modularCorrection (p := p) A B
    let cZ := modularCorrection (p := p) A C
    have hcY : (cY : ZMod p) = -(B : ZMod p) / (A : ZMod p) := by
      exact cast_modularCorrection (p := p) hA
    have hcZ : (cZ : ZMod p) = -(C : ZMod p) / (A : ZMod p) := by
      exact cast_modularCorrection (p := p) hA
    have hresidue :
        ((m.1 - cY * m.2.1 - cZ * m.2.2 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hcY, hcZ]
      calc
        (m.1 : ZMod p) - (-(B : ZMod p) / (A : ZMod p)) * (m.2.1 : ZMod p) -
              (-(C : ZMod p) / (A : ZMod p)) * (m.2.2 : ZMod p) =
            (A : ZMod p)⁻¹ *
              ((A : ZMod p) * (m.1 : ZMod p) +
                (B : ZMod p) * (m.2.1 : ZMod p) +
                (C : ZMod p) * (m.2.2 : ZMod p)) := by
                  field_simp [hA]
                  ring
        _ = 0 := by
          rw [show (A : ZMod p) * (m.1 : ZMod p) +
                (B : ZMod p) * (m.2.1 : ZMod p) +
                (C : ZMod p) * (m.2.2 : ZMod p) = 0 by
              exact_mod_cast hcast]
          simp
    have hdiv : (p : ℤ) ∣ m.1 - cY * m.2.1 - cZ * m.2.2 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hresidue
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨q, ?_⟩
    apply Prod.ext
    · dsimp [firstPivotKernelPoint]
      change m.1 = (p : ℤ) * q + cY * m.2.1 + cZ * m.2.2
      omega
    · rfl
  · rintro ⟨q, hq⟩
    have hx := congrArg Prod.fst hq
    change m.1 = (p : ℤ) * q + modularCorrection (p := p) A B * m.2.1 +
      modularCorrection (p := p) A C * m.2.2 at hx
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hx]
    push_cast
    rw [cast_modularCorrection (p := p) hA,
      cast_modularCorrection (p := p) hA]
    field_simp [hA]
    simp

/-- Exact reduction through the second coordinate after the first coefficient
has vanished in the residue chart. -/
theorem secondPivotKernel_iff {A B C : ℤ}
    (hA : (A : ZMod p) = 0) (hB : (B : ZMod p) ≠ 0) (m : IntTriple) :
    (p : ℤ) ∣ A * m.1 + B * m.2.1 + C * m.2.2 ↔
      ∃ q : ℤ, m = secondPivotKernelPoint (p := p) B C m.1 q m.2.2 := by
  constructor
  · intro hm
    have hcast :
        ((A * m.1 + B * m.2.1 + C * m.2.2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hm
    let cZ := modularCorrection (p := p) B C
    have hcZ : (cZ : ZMod p) = -(C : ZMod p) / (B : ZMod p) := by
      exact cast_modularCorrection (p := p) hB
    have hresidue : ((m.2.1 - cZ * m.2.2 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hcZ]
      calc
        (m.2.1 : ZMod p) - (-(C : ZMod p) / (B : ZMod p)) *
              (m.2.2 : ZMod p) =
            (B : ZMod p)⁻¹ *
              ((A : ZMod p) * (m.1 : ZMod p) +
                (B : ZMod p) * (m.2.1 : ZMod p) +
                (C : ZMod p) * (m.2.2 : ZMod p)) := by
                  rw [hA]
                  field_simp [hB]
                  ring
        _ = 0 := by
          rw [show (A : ZMod p) * (m.1 : ZMod p) +
                (B : ZMod p) * (m.2.1 : ZMod p) +
                (C : ZMod p) * (m.2.2 : ZMod p) = 0 by
              exact_mod_cast hcast]
          simp
    have hdiv : (p : ℤ) ∣ m.2.1 - cZ * m.2.2 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hresidue
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨q, ?_⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · dsimp [secondPivotKernelPoint]
        change m.2.1 = (p : ℤ) * q + cZ * m.2.2
        omega
      · rfl
  · rintro ⟨q, hq⟩
    have hy := congrArg (fun w : IntTriple => w.2.1) hq
    change m.2.1 = (p : ℤ) * q +
      modularCorrection (p := p) B C * m.2.2 at hy
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hy]
    push_cast
    rw [hA, cast_modularCorrection (p := p) hB]
    field_simp [hB]
    simp

/-! ## The explicit four-coordinate neighbor chart -/

/-- The four-coordinate rational point in a first-pivot chart. -/
def firstPivotNeighborPoint (A B C : ℤ) (v : IntTriple)
    (u : NeighborCoordinates) : RatTriple :=
  ratTripleAdd
    (intTripleToRat
      (firstPivotKernelPoint (p := p) A B C u.1 u.2.1 u.2.2.1))
    (ratTripleScale ((u.2.2.2 : ℚ) / (p : ℚ)) (intTripleToRat v))

/-- The four-coordinate rational point in a second-pivot chart. -/
def secondPivotNeighborPoint (B C : ℤ) (v : IntTriple)
    (u : NeighborCoordinates) : RatTriple :=
  ratTripleAdd
    (intTripleToRat
      (secondPivotKernelPoint (p := p) B C u.1 u.2.1 u.2.2.1))
    (ratTripleScale ((u.2.2.2 : ℚ) / (p : ℚ)) (intTripleToRat v))

/-- The first-pivot coordinate chart is an additive transport, not merely a
set-theoretic parametrization. -/
def firstPivotNeighborHom (A B C : ℤ) (v : IntTriple) :
    NeighborCoordinates →+ RatTriple where
  toFun := firstPivotNeighborPoint (p := p) A B C v
  map_zero' := by
    apply Prod.ext
    · simp [firstPivotNeighborPoint, firstPivotKernelPoint, modularCorrection,
        ratTripleAdd, ratTripleScale, intTripleToRat]
    · apply Prod.ext <;>
        simp [firstPivotNeighborPoint, firstPivotKernelPoint, modularCorrection,
          ratTripleAdd, ratTripleScale, intTripleToRat]
  map_add' := by
    intro u w
    apply Prod.ext
    · simp [firstPivotNeighborPoint, firstPivotKernelPoint, ratTripleAdd,
        ratTripleScale, intTripleToRat]
      ring
    · apply Prod.ext
      · simp [firstPivotNeighborPoint, firstPivotKernelPoint, ratTripleAdd,
          ratTripleScale, intTripleToRat]
        ring
      · simp [firstPivotNeighborPoint, firstPivotKernelPoint, ratTripleAdd,
          ratTripleScale, intTripleToRat]
        ring

/-- The second-pivot coordinate chart is likewise additive. -/
def secondPivotNeighborHom (B C : ℤ) (v : IntTriple) :
    NeighborCoordinates →+ RatTriple where
  toFun := secondPivotNeighborPoint (p := p) B C v
  map_zero' := by
    apply Prod.ext
    · simp [secondPivotNeighborPoint, secondPivotKernelPoint, modularCorrection,
        ratTripleAdd, ratTripleScale, intTripleToRat]
    · apply Prod.ext <;>
        simp [secondPivotNeighborPoint, secondPivotKernelPoint, modularCorrection,
          ratTripleAdd, ratTripleScale, intTripleToRat]
  map_add' := by
    intro u w
    apply Prod.ext
    · simp [secondPivotNeighborPoint, secondPivotKernelPoint, ratTripleAdd,
        ratTripleScale, intTripleToRat]
      ring
    · apply Prod.ext
      · simp [secondPivotNeighborPoint, secondPivotKernelPoint, ratTripleAdd,
          ratTripleScale, intTripleToRat]
        ring
      · simp [secondPivotNeighborPoint, secondPivotKernelPoint, ratTripleAdd,
          ratTripleScale, intTripleToRat]
        ring

/-- A zero rational return from an integral point plus `a/p` times a primitive
residue direction forces the fractional coordinate `a` to contain a complete
factor of `p`.  This is the first exact part of the one-dimensional relation
kernel, independent of which polar pivot chart produced the integral point. -/
theorem fourthCoordinate_dvd_of_fractionalPoint_eq_zero
    (m v : IntTriple) (a : ℤ)
    (hv : reduceTriple (p := p) v ≠ (0, 0, 0))
    (hzero :
      ratTripleAdd (intTripleToRat m)
          (ratTripleScale ((a : ℚ) / (p : ℚ)) (intTripleToRat v)) =
        (0, 0, 0)) :
    (p : ℤ) ∣ a := by
  have hpQ : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx := congrArg Prod.fst hzero
  have hy := congrArg (fun w : RatTriple => w.2.1) hzero
  have hz := congrArg (fun w : RatTriple => w.2.2) hzero
  simp only [ratTripleAdd, ratTripleScale, intTripleToRat] at hx hy hz
  have hxZ : (p : ℤ) * m.1 + a * v.1 = 0 := by
    field_simp [hpQ] at hx
    have hx' : m.1 * (p : ℤ) + a * v.1 = (p : ℤ) * 0 := by
      exact_mod_cast hx
    simpa [mul_comm] using hx'
  have hyZ : (p : ℤ) * m.2.1 + a * v.2.1 = 0 := by
    field_simp [hpQ] at hy
    have hy' : m.2.1 * (p : ℤ) + a * v.2.1 = (p : ℤ) * 0 := by
      exact_mod_cast hy
    simpa [mul_comm] using hy'
  have hzZ : (p : ℤ) * m.2.2 + a * v.2.2 = 0 := by
    field_simp [hpQ] at hz
    have hz' : m.2.2 * (p : ℤ) + a * v.2.2 = (p : ℤ) * 0 := by
      exact_mod_cast hz
    simpa [mul_comm] using hz'
  have hxmod := congrArg (fun n : ℤ => (n : ZMod p)) hxZ
  have hymod := congrArg (fun n : ℤ => (n : ZMod p)) hyZ
  have hzmod := congrArg (fun n : ℤ => (n : ZMod p)) hzZ
  push_cast at hxmod hymod hzmod
  simp only [ZMod.natCast_self, zero_mul, zero_add] at hxmod hymod hzmod
  have ha : (a : ZMod p) = 0 := by
    by_contra ha0
    have hvx : (v.1 : ZMod p) = 0 := (mul_eq_zero.mp hxmod).resolve_left ha0
    have hvy : (v.2.1 : ZMod p) = 0 := (mul_eq_zero.mp hymod).resolve_left ha0
    have hvz : (v.2.2 : ZMod p) = 0 := (mul_eq_zero.mp hzmod).resolve_left ha0
    apply hv
    apply Prod.ext
    · simpa [reduceTriple] using hvx
    · apply Prod.ext
      · simpa [reduceTriple] using hvy
      · simpa [reduceTriple] using hvz
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ha

/-- The explicit coordinate map for a first-class actual neighbor. -/
def firstBrandtNeighborPoint (hp2 : p ≠ 2)
    (d : FirstBrandtDirection (p := p)) : NeighborCoordinates → RatTriple :=
  let v := adjustedDirectionLift 32 d
  match d.1 with
  | .inl _ => firstPivotNeighborPoint (p := p)
      (4 * v.1) (2 * v.2.1) (64 * v.2.2) v
  | .inr _ => secondPivotNeighborPoint (p := p)
      (2 * v.2.1) (64 * v.2.2) v

/-- The explicit coordinate map for a second-class actual neighbor. -/
def secondBrandtNeighborPoint (hp2 : p ≠ 2)
    (d : SecondBrandtDirection (p := p)) : NeighborCoordinates → RatTriple :=
  let v := adjustedBrandtSecondDirectionLift hp2 d
  let A := 4 * v.1
  let B := 8 * v.2.1 + 4 * v.2.2
  let C := 4 * v.2.1 + 18 * v.2.2
  match d.1 with
  | .inl _ => firstPivotNeighborPoint (p := p) A B C v
  | .inr _ => secondPivotNeighborPoint (p := p) B C v

/-- The actual first-class chart packaged as an additive morphism. -/
def firstBrandtNeighborHom (hp2 : p ≠ 2)
    (d : FirstBrandtDirection (p := p)) : NeighborCoordinates →+ RatTriple :=
  let v := adjustedDirectionLift 32 d
  match d.1 with
  | .inl _ => firstPivotNeighborHom (p := p)
      (4 * v.1) (2 * v.2.1) (64 * v.2.2) v
  | .inr _ => secondPivotNeighborHom (p := p)
      (2 * v.2.1) (64 * v.2.2) v

/-- The actual second-class chart packaged as an additive morphism. -/
def secondBrandtNeighborHom (hp2 : p ≠ 2)
    (d : SecondBrandtDirection (p := p)) : NeighborCoordinates →+ RatTriple :=
  let v := adjustedBrandtSecondDirectionLift hp2 d
  let A := 4 * v.1
  let B := 8 * v.2.1 + 4 * v.2.2
  let C := 4 * v.2.1 + 18 * v.2.2
  match d.1 with
  | .inl _ => firstPivotNeighborHom (p := p) A B C v
  | .inr _ => secondPivotNeighborHom (p := p) B C v

theorem firstBrandtNeighborHom_apply (hp2 : p ≠ 2)
    (d : FirstBrandtDirection (p := p)) (u : NeighborCoordinates) :
    firstBrandtNeighborHom hp2 d u = firstBrandtNeighborPoint hp2 d u := by
  rcases d with ⟨chart, hchart⟩
  cases chart <;> rfl

theorem secondBrandtNeighborHom_apply (hp2 : p ≠ 2)
    (d : SecondBrandtDirection (p := p)) (u : NeighborCoordinates) :
    secondBrandtNeighborHom hp2 d u = secondBrandtNeighborPoint hp2 d u := by
  rcases d with ⟨chart, hchart⟩
  cases chart <;> rfl

/-- Every zero fibre of an actual first-class additive neighbor chart has a
fractional coordinate divisible by `p`. -/
theorem firstBrandtNeighborHom_zero_fourthCoordinate_dvd (hp2 : p ≠ 2)
    (d : FirstBrandtDirection (p := p)) (u : NeighborCoordinates)
    (hzero : firstBrandtNeighborHom hp2 d u = 0) :
    (p : ℤ) ∣ u.2.2.2 := by
  let v := adjustedDirectionLift 32 d
  have hv : reduceTriple (p := p) v ≠ (0, 0, 0) := by
    rw [reduce_adjustedDirectionLift (p := p) hp2 32 d]
    exact projectiveDirectionVector_ne_zero d
  rcases d with ⟨chart, hchart⟩
  cases chart with
  | inl yz =>
      apply fourthCoordinate_dvd_of_fractionalPoint_eq_zero (p := p)
        (m := firstPivotKernelPoint (p := p) (4 * v.1) (2 * v.2.1)
          (64 * v.2.2) u.1 u.2.1 u.2.2.1)
        (v := v) (a := u.2.2.2) hv
      simpa [firstBrandtNeighborHom, firstPivotNeighborHom, firstPivotNeighborPoint, v, Prod.mk_zero_zero] using hzero
  | inr z =>
      apply fourthCoordinate_dvd_of_fractionalPoint_eq_zero (p := p)
        (m := secondPivotKernelPoint (p := p) (2 * v.2.1) (64 * v.2.2)
          u.1 u.2.1 u.2.2.1)
        (v := v) (a := u.2.2.2) hv
      simpa [firstBrandtNeighborHom, secondPivotNeighborHom, secondPivotNeighborPoint, v, Prod.mk_zero_zero] using hzero

/-- Every zero fibre of an actual second-class additive neighbor chart has the
same exact divisibility. -/
theorem secondBrandtNeighborHom_zero_fourthCoordinate_dvd (hp2 : p ≠ 2)
    (d : SecondBrandtDirection (p := p)) (u : NeighborCoordinates)
    (hzero : secondBrandtNeighborHom hp2 d u = 0) :
    (p : ℤ) ∣ u.2.2.2 := by
  let v := adjustedBrandtSecondDirectionLift hp2 d
  have hv : reduceTriple (p := p) v ≠ (0, 0, 0) := by
    rw [reduce_adjustedBrandtSecondDirectionLift (p := p) hp2 d]
    exact brandtSecondDirectionVector_ne_zero hp2 d
  rcases d with ⟨chart, hchart⟩
  cases chart with
  | inl yz =>
      let A := 4 * v.1
      let B := 8 * v.2.1 + 4 * v.2.2
      let C := 4 * v.2.1 + 18 * v.2.2
      apply fourthCoordinate_dvd_of_fractionalPoint_eq_zero (p := p)
        (m := firstPivotKernelPoint (p := p) A B C u.1 u.2.1 u.2.2.1)
        (v := v) (a := u.2.2.2) hv
      simpa [secondBrandtNeighborHom, firstPivotNeighborHom, firstPivotNeighborPoint, v, A, B, C, Prod.mk_zero_zero] using hzero
  | inr z =>
      let B := 8 * v.2.1 + 4 * v.2.2
      let C := 4 * v.2.1 + 18 * v.2.2
      apply fourthCoordinate_dvd_of_fractionalPoint_eq_zero (p := p)
        (m := secondPivotKernelPoint (p := p) B C u.1 u.2.1 u.2.2.1)
        (v := v) (a := u.2.2.2) hv
      simpa [secondBrandtNeighborHom, secondPivotNeighborHom, secondPivotNeighborPoint, v, B, C, Prod.mk_zero_zero] using hzero

private theorem two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

private theorem four_ne_zero (hp2 : p ≠ 2) : (4 : ZMod p) ≠ 0 := by
  rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
  exact pow_ne_zero 2 (two_ne_zero (p := p) hp2)

/-- Every point of every actual first-class neighbor, and only such a point, is
returned by its explicit four-integer chart. -/
theorem mem_firstBrandtNeighbor_iff_coordinates (hp2 : p ≠ 2)
    (d : FirstBrandtDirection (p := p)) (x : RatTriple) :
    x ∈ integralNeighbor (p := p) 32 d ↔
      ∃ u : NeighborCoordinates, firstBrandtNeighborPoint hp2 d u = x := by
  let v := adjustedDirectionLift 32 d
  have hreduce := reduce_adjustedDirectionLift (p := p) hp2 32 d
  rcases d with ⟨chart, hisotropic⟩
  cases chart with
  | inl yz =>
      have hvx : (v.1 : ZMod p) = 1 := by
        have h := congrArg Prod.fst hreduce
        simpa [v, projectiveDirectionVector, reduceTriple] using h
      have hA : ((4 * v.1 : ℤ) : ZMod p) ≠ 0 := by
        push_cast
        rw [hvx]
        simpa using four_ne_zero (p := p) hp2
      constructor
      · rintro ⟨m, hm, a, rfl⟩
        have hm' : (p : ℤ) ∣ 4 * v.1 * m.1 + 2 * v.2.1 * m.2.1 +
            64 * v.2.2 * m.2.2 := by
          simpa [polarKernel, intTunnellPolar, v, mul_comm, mul_left_comm,
            mul_assoc] using hm
        obtain ⟨q, hq⟩ :=
          (firstPivotKernel_iff (p := p) hA m).1 hm'
        refine ⟨(q, m.2.1, m.2.2, a), ?_⟩
        simp only [firstBrandtNeighborPoint, firstPivotNeighborPoint]
        rw [← hq]
      · rintro ⟨u, rfl⟩
        refine ⟨firstPivotKernelPoint (p := p) (4 * v.1) (2 * v.2.1)
            (64 * v.2.2) u.1 u.2.1 u.2.2.1, ?_, u.2.2.2, ?_⟩
        · let m0 := firstPivotKernelPoint (p := p) (4 * v.1) (2 * v.2.1)
              (64 * v.2.2) u.1 u.2.1 u.2.2.1
          have hkernel : (p : ℤ) ∣ 4 * v.1 * m0.1 + 2 * v.2.1 * m0.2.1 +
              64 * v.2.2 * m0.2.2 := by
            apply (firstPivotKernel_iff (p := p) hA m0).2
            refine ⟨u.1, ?_⟩
            simp [m0, firstPivotKernelPoint]
          simpa [m0, polarKernel, intTunnellPolar, v, mul_comm, mul_left_comm,
            mul_assoc] using hkernel
        · rfl
  | inr z =>
      have hvx : (v.1 : ZMod p) = 0 := by
        have h := congrArg Prod.fst hreduce
        simpa [v, projectiveDirectionVector, reduceTriple] using h
      have hvy : (v.2.1 : ZMod p) = 1 := by
        have h := congrArg (fun w => w.2.1) hreduce
        simpa [v, reduceTriple, projectiveDirectionVector] using h
      have hA : ((4 * v.1 : ℤ) : ZMod p) = 0 := by
        push_cast
        rw [hvx]
        ring
      have hB : ((2 * v.2.1 : ℤ) : ZMod p) ≠ 0 := by
        push_cast
        rw [hvy]
        simpa using two_ne_zero (p := p) hp2
      constructor
      · rintro ⟨m, hm, a, rfl⟩
        have hm' : (p : ℤ) ∣ 4 * v.1 * m.1 + 2 * v.2.1 * m.2.1 +
            64 * v.2.2 * m.2.2 := by
          simpa [polarKernel, intTunnellPolar, v, mul_comm, mul_left_comm,
            mul_assoc] using hm
        obtain ⟨q, hq⟩ :=
          (secondPivotKernel_iff (p := p) hA hB m).1 hm'
        refine ⟨(m.1, q, m.2.2, a), ?_⟩
        simp only [firstBrandtNeighborPoint, secondPivotNeighborPoint]
        rw [← hq]
      · rintro ⟨u, rfl⟩
        refine ⟨secondPivotKernelPoint (p := p) (2 * v.2.1) (64 * v.2.2)
            u.1 u.2.1 u.2.2.1, ?_, u.2.2.2, ?_⟩
        · let m0 := secondPivotKernelPoint (p := p) (2 * v.2.1) (64 * v.2.2)
              u.1 u.2.1 u.2.2.1
          have hkernel : (p : ℤ) ∣ 4 * v.1 * m0.1 + 2 * v.2.1 * m0.2.1 +
              64 * v.2.2 * m0.2.2 := by
            apply (secondPivotKernel_iff (p := p) hA hB m0).2
            refine ⟨u.2.1, ?_⟩
            simp [m0, secondPivotKernelPoint]
          simpa [m0, polarKernel, intTunnellPolar, v, mul_comm, mul_left_comm,
            mul_assoc] using hkernel
        · rfl

/-! The second-class proof follows the same reduction but keeps the cross-term
polar coefficients rather than transporting the integral lattice through the
determinant-two residue chart. -/

/-- Every point of every actual second-class neighbor, and only such a point,
is returned by its explicit four-integer chart. -/
theorem mem_secondBrandtNeighbor_iff_coordinates (hp2 : p ≠ 2)
    (d : SecondBrandtDirection (p := p)) (x : RatTriple) :
    x ∈ brandtSecondIntegralNeighbor hp2 d ↔
      ∃ u : NeighborCoordinates, secondBrandtNeighborPoint hp2 d u = x := by
  let v := adjustedBrandtSecondDirectionLift hp2 d
  let A := 4 * v.1
  let B := 8 * v.2.1 + 4 * v.2.2
  let C := 4 * v.2.1 + 18 * v.2.2
  have hreduce := reduce_adjustedBrandtSecondDirectionLift (p := p) hp2 d
  rcases d with ⟨chart, hisotropic⟩
  cases chart with
  | inl yz =>
      have hvx : (v.1 : ZMod p) = 1 := by
        have h := congrArg Prod.fst hreduce
        simpa [v, reduceTriple, brandtSecondDirectionVector, thinToBrandtSecondMod,
          projectiveDirectionVector] using h
      have hA : (A : ZMod p) ≠ 0 := by
        dsimp [A]
        push_cast
        rw [hvx]
        simpa using four_ne_zero (p := p) hp2
      constructor
      · rintro ⟨m, hm, a, rfl⟩
        have hm' : (p : ℤ) ∣ A * m.1 + B * m.2.1 + C * m.2.2 := by
          change (p : ℤ) ∣ brandtSecondPolar m
            (adjustedBrandtSecondDirectionLift hp2 ⟨Sum.inl yz, hisotropic⟩) at hm
          convert hm using 1 <;> simp [brandtSecondPolar, v, A, B, C] <;> ring
        obtain ⟨q, hq⟩ := (firstPivotKernel_iff (p := p) hA m).1 hm'
        refine ⟨(q, m.2.1, m.2.2, a), ?_⟩
        simp only [secondBrandtNeighborPoint, firstPivotNeighborPoint]
        rw [← hq]
      · rintro ⟨u, rfl⟩
        refine ⟨firstPivotKernelPoint (p := p) A B C u.1 u.2.1 u.2.2.1,
          ?_, u.2.2.2, ?_⟩
        · let m0 := firstPivotKernelPoint (p := p) A B C u.1 u.2.1 u.2.2.1
          have hkernel : (p : ℤ) ∣ A * m0.1 + B * m0.2.1 + C * m0.2.2 := by
            apply (firstPivotKernel_iff (p := p) hA m0).2
            refine ⟨u.1, ?_⟩
            simp [m0, firstPivotKernelPoint]
          change (p : ℤ) ∣ brandtSecondPolar m0
            (adjustedBrandtSecondDirectionLift hp2 ⟨Sum.inl yz, hisotropic⟩)
          convert hkernel using 1 <;> simp [m0, brandtSecondPolar, v, A, B, C] <;> ring
        · rfl
  | inr z =>
      have hvx : (v.1 : ZMod p) = 0 := by
        have h := congrArg Prod.fst hreduce
        simpa [v, reduceTriple, brandtSecondDirectionVector, thinToBrandtSecondMod,
          projectiveDirectionVector] using h
      have hA : (A : ZMod p) = 0 := by
        dsimp [A]
        push_cast
        rw [hvx]
        ring
      have hvy : (v.2.1 : ZMod p) = (1 - z) / 2 := by
        have h := congrArg (fun w => w.2.1) hreduce
        simpa [v, reduceTriple, brandtSecondDirectionVector,
          thinToBrandtSecondMod, projectiveDirectionVector] using h
      have hvz : (v.2.2 : ZMod p) = z := by
        have h := congrArg (fun w => w.2.2) hreduce
        simpa [v, reduceTriple, brandtSecondDirectionVector,
          thinToBrandtSecondMod, projectiveDirectionVector] using h
      have hBvalue : (B : ZMod p) = 4 := by
        dsimp [B]
        push_cast
        rw [hvy, hvz]
        field_simp [two_ne_zero (p := p) hp2]
        ring
      have hB : (B : ZMod p) ≠ 0 := by
        rw [hBvalue]
        exact four_ne_zero (p := p) hp2
      constructor
      · rintro ⟨m, hm, a, rfl⟩
        have hm' : (p : ℤ) ∣ A * m.1 + B * m.2.1 + C * m.2.2 := by
          change (p : ℤ) ∣ brandtSecondPolar m
            (adjustedBrandtSecondDirectionLift hp2 ⟨Sum.inr z, hisotropic⟩) at hm
          convert hm using 1 <;> simp [brandtSecondPolar, v, A, B, C] <;> ring
        obtain ⟨q, hq⟩ := (secondPivotKernel_iff (p := p) hA hB m).1 hm'
        refine ⟨(m.1, q, m.2.2, a), ?_⟩
        simp only [secondBrandtNeighborPoint, secondPivotNeighborPoint]
        rw [← hq]
      · rintro ⟨u, rfl⟩
        refine ⟨secondPivotKernelPoint (p := p) B C u.1 u.2.1 u.2.2.1,
          ?_, u.2.2.2, ?_⟩
        · let m0 := secondPivotKernelPoint (p := p) B C u.1 u.2.1 u.2.2.1
          have hkernel : (p : ℤ) ∣ A * m0.1 + B * m0.2.1 + C * m0.2.2 := by
            apply (secondPivotKernel_iff (p := p) hA hB m0).2
            refine ⟨u.2.1, ?_⟩
            simp [m0, secondPivotKernelPoint]
          change (p : ℤ) ∣ brandtSecondPolar m0
            (adjustedBrandtSecondDirectionLift hp2 ⟨Sum.inr z, hisotropic⟩)
          convert hkernel using 1 <;> simp [m0, brandtSecondPolar, v, A, B, C] <;> ring
        · rfl

/-- One coordinate chart for every occurrence in the fused two-source
world-tube. -/
def brandtNeighborCoordinatePoint (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    NeighborCoordinates → RatTriple :=
  match occurrence with
  | .inl d => firstBrandtNeighborPoint hp2 d
  | .inr d => secondBrandtNeighborPoint hp2 d

/-- The fused two-source coordinate atlas as one additive returned passage. -/
def brandtNeighborCoordinateHom (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    NeighborCoordinates →+ RatTriple :=
  match occurrence with
  | .inl d => firstBrandtNeighborHom hp2 d
  | .inr d => secondBrandtNeighborHom hp2 d

theorem brandtNeighborCoordinateHom_apply (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (u : NeighborCoordinates) :
    brandtNeighborCoordinateHom hp2 occurrence u =
      brandtNeighborCoordinatePoint hp2 occurrence u := by
  cases occurrence with
  | inl d => exact firstBrandtNeighborHom_apply hp2 d u
  | inr d => exact secondBrandtNeighborHom_apply hp2 d u

/-- **EVERY ZERO FIBRE OF THE FUSED ADDITIVE ATLAS CARRIES A COMPLETE
`p` FACTOR IN ITS FRACTIONAL DIRECTION.**  Writing that coordinate as `p*k`
is therefore lawful in the next relation-generator theorem. -/
theorem brandtNeighborCoordinateHom_zero_fourthCoordinate_dvd
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (u : NeighborCoordinates)
    (hzero : brandtNeighborCoordinateHom hp2 occurrence u = 0) :
    (p : ℤ) ∣ u.2.2.2 := by
  cases occurrence with
  | inl d => exact firstBrandtNeighborHom_zero_fourthCoordinate_dvd hp2 d u hzero
  | inr d => exact secondBrandtNeighborHom_zero_fourthCoordinate_dvd hp2 d u hzero

/-- **THE COMPLETE ACTUAL NEIGHBOR WORLD-TUBE HAS AN EXACT FOUR-INTEGER
COORDINATE REDUCTION.**  This is the source object on which the remaining
Jones--Pall destination classifier must act. -/
theorem BrandtNeighborOccurrence.mem_neighbor_iff_coordinates
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (x : RatTriple) :
    occurrence.neighborMember hp2 x ↔
      ∃ u : NeighborCoordinates, brandtNeighborCoordinatePoint hp2 occurrence u = x := by
  cases occurrence with
  | inl d => exact mem_firstBrandtNeighbor_iff_coordinates hp2 d x
  | inr d => exact mem_secondBrandtNeighbor_iff_coordinates hp2 d x

#print axioms firstPivotKernel_iff
#print axioms secondPivotKernel_iff
#print axioms fourthCoordinate_dvd_of_fractionalPoint_eq_zero
#print axioms firstBrandtNeighborHom_zero_fourthCoordinate_dvd
#print axioms secondBrandtNeighborHom_zero_fourthCoordinate_dvd
#print axioms brandtNeighborCoordinateHom_zero_fourthCoordinate_dvd
#print axioms mem_firstBrandtNeighbor_iff_coordinates
#print axioms mem_secondBrandtNeighbor_iff_coordinates
#print axioms BrandtNeighborOccurrence.mem_neighbor_iff_coordinates

end Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationClassification
