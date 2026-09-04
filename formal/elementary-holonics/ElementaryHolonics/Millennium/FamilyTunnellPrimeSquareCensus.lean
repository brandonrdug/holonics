import ElementaryHolonics.Millennium.FamilyTunnellNormOneReturn
import ElementaryHolonics.Millennium.GaussCoefficient

/-!
# The prime-square census beneath the Tunnell Brandt sign

A norm-one vector in a first-class `p`-neighbor returns an integral solution of

`2x² + y² + 32z² = p²`.

This file constructs that complete finite population and separates the two
imprimitive axis occurrences from the primitive residue directions.  The
imprimitive classification is exact and uniform at every prime: the only source
vectors reducing to zero are `(0,p,0)` and `(0,-p,0)`.  Thus every remaining
prime-square occurrence carries a nonzero projective direction.

This is the arithmetic census needed to count the two sheets of the Brandt class
receiver.  The subsequent edge is the explicit equivalence between its primitive
direction fibres and the Frobenius/Hecke trace carrier.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellPrimeSquareCensus

open Finset
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellHeckeIncidence
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellNormOneReturn

variable {p : ℕ} [Fact p.Prime]

/-- The complete finite fibre of the first Brandt norm above `p²`. -/
def firstPrimeSquarePopulation : Finset IntTriple :=
  canonicalThickPopulation (p ^ 2)

theorem mem_firstPrimeSquarePopulation_iff (m : IntTriple) :
    m ∈ firstPrimeSquarePopulation (p := p) ↔
      brandtFirstQuadratic m = (p : ℤ) ^ 2 := by
  unfold firstPrimeSquarePopulation
  rw [mem_canonicalThickPopulation_iff_intTunnellQuadratic]
  rfl

/-- The prime-square occurrences whose residue direction survives. -/
def primitiveFirstPrimeSquarePopulation : Finset IntTriple :=
  (firstPrimeSquarePopulation (p := p)).filter fun m =>
    reduceTriple (p := p) m ≠ (0, 0, 0)

/-- The deleted zero-residue fibre, retained separately. -/
def imprimitiveFirstPrimeSquarePopulation : Finset IntTriple :=
  (firstPrimeSquarePopulation (p := p)).filter fun m =>
    reduceTriple (p := p) m = (0, 0, 0)

private theorem coordinate_dvd_of_reduce_eq_zero
    {m : IntTriple} (hzero : reduceTriple (p := p) m = (0, 0, 0)) :
    (p : ℤ) ∣ m.1 ∧ (p : ℤ) ∣ m.2.1 ∧ (p : ℤ) ∣ m.2.2 := by
  have hx := congrArg (fun w : CoordinateTriple (ZMod p) => w.1) hzero
  have hy := congrArg (fun w : CoordinateTriple (ZMod p) => w.2.1) hzero
  have hz := congrArg (fun w : CoordinateTriple (ZMod p) => w.2.2) hzero
  simp [reduceTriple] at hx hy hz
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd m.1 p).mp hx,
    (ZMod.intCast_zmod_eq_zero_iff_dvd m.2.1 p).mp hy,
    (ZMod.intCast_zmod_eq_zero_iff_dvd m.2.2 p).mp hz⟩

private theorem endpoint_mem_firstPrimeSquarePopulation (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) :
    (0, sign * (p : ℤ), 0) ∈ firstPrimeSquarePopulation (p := p) := by
  rw [mem_firstPrimeSquarePopulation_iff]
  rcases hsign with rfl | rfl <;> simp [brandtFirstQuadratic]

private theorem endpoint_reduce_eq_zero (sign : ℤ) :
    reduceTriple (p := p) (0, sign * (p : ℤ), 0) = (0, 0, 0) := by
  apply Prod.ext
  · simp [reduceTriple]
  · apply Prod.ext <;> simp [reduceTriple]

/-- **THE ZERO-RESIDUE PRIME-SQUARE FIBRE CONSISTS OF EXACTLY TWO ORIENTED
AXIS OCCURRENCES.** -/
theorem imprimitiveFirstPrimeSquarePopulation_eq_pair :
    imprimitiveFirstPrimeSquarePopulation (p := p) =
      {(0, (p : ℤ), 0), (0, -(p : ℤ), 0)} := by
  ext m
  constructor
  · intro hm
    have hm' := Finset.mem_filter.mp hm
    have hnorm := (mem_firstPrimeSquarePopulation_iff (p := p) m).mp hm'.1
    rcases coordinate_dvd_of_reduce_eq_zero (p := p) hm'.2 with
      ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩
    have hfactor :
        (p : ℤ) ^ 2 * brandtFirstQuadratic (x, y, z) = (p : ℤ) ^ 2 := by
      calc
        (p : ℤ) ^ 2 * brandtFirstQuadratic (x, y, z) =
            brandtFirstQuadratic m := by
              simp [brandtFirstQuadratic, hx, hy, hz]
              ring
        _ = (p : ℤ) ^ 2 := hnorm
    have hpZ : (p : ℤ) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have hunit : brandtFirstQuadratic (x, y, z) = 1 := by
      apply (mul_left_cancel₀ hpZ)
      simpa using hfactor
    rcases (brandtFirstQuadratic_eq_one_iff (x, y, z)).mp hunit with hpos | hneg
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      have ex := congrArg (fun q : IntTriple => q.1) hpos
      have ey := congrArg (fun q : IntTriple => q.2.1) hpos
      have ez := congrArg (fun q : IntTriple => q.2.2) hpos
      simp at ex ey ez
      apply Prod.ext
      · simpa [ex] using hx
      · apply Prod.ext
        · simpa [ey, mul_comm] using hy
        · simpa [ez] using hz
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      have ex := congrArg (fun q : IntTriple => q.1) hneg
      have ey := congrArg (fun q : IntTriple => q.2.1) hneg
      have ez := congrArg (fun q : IntTriple => q.2.2) hneg
      simp at ex ey ez
      apply Prod.ext
      · simpa [ex] using hx
      · apply Prod.ext
        · simpa [ey, mul_comm] using hy
        · simpa [ez] using hz
  · intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by
        simpa using endpoint_mem_firstPrimeSquarePopulation (p := p) 1 (Or.inl rfl), by
          simpa using endpoint_reduce_eq_zero (p := p) 1⟩
    · exact Finset.mem_filter.mpr
        ⟨by simpa using
            endpoint_mem_firstPrimeSquarePopulation (p := p) (-1) (Or.inr rfl), by
          simpa using endpoint_reduce_eq_zero (p := p) (-1)⟩

/-- The two imprimitive orientations are distinct at every prime. -/
theorem imprimitiveFirstPrimeSquarePopulation_card :
    (imprimitiveFirstPrimeSquarePopulation (p := p)).card = 2 := by
  rw [imprimitiveFirstPrimeSquarePopulation_eq_pair]
  have hp : (p : ℤ) ≠ -(p : ℤ) := by
    have hpos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
    omega
  simp [hp]

/-- Primitive and zero-residue occurrences are the exact complementary charts of
the complete prime-square population. -/
theorem primitive_card_add_two_eq_complete_card :
    (primitiveFirstPrimeSquarePopulation (p := p)).card + 2 =
      (firstPrimeSquarePopulation (p := p)).card := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := firstPrimeSquarePopulation (p := p))
    (fun m : IntTriple => reduceTriple (p := p) m ≠ (0, 0, 0))
  rw [show (firstPrimeSquarePopulation (p := p)).filter
      (fun m => reduceTriple (p := p) m ≠ (0, 0, 0)) =
        primitiveFirstPrimeSquarePopulation (p := p) by rfl] at hpartition
  have himp :
      (firstPrimeSquarePopulation (p := p)).filter
          (fun m => ¬ reduceTriple (p := p) m ≠ (0, 0, 0)) =
        imprimitiveFirstPrimeSquarePopulation (p := p) := by
    ext m
    simp [imprimitiveFirstPrimeSquarePopulation]
  rw [himp, imprimitiveFirstPrimeSquarePopulation_card] at hpartition
  exact hpartition

#print axioms mem_firstPrimeSquarePopulation_iff
#print axioms imprimitiveFirstPrimeSquarePopulation_eq_pair
#print axioms imprimitiveFirstPrimeSquarePopulation_card
#print axioms primitive_card_add_two_eq_complete_card

end Soma.Holonics.Millennium.FamilyTunnellPrimeSquareCensus
