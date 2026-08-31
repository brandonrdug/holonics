import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighbors
import Mathlib.Algebra.Quaternion

/-!
# Quaternionic realization of the two Tunnell--Brandt lattices

The Brandt neighbor action is an ideal-class action in the Hamilton quaternion
algebra ramified at `2` and infinity.  This file constructs the exact source
bridge rather than leaving the two ternary forms as unexplained coordinate
tables.

The first lattice is

`Z i + Z (j+k) + Z 4(j-k)`

with the first two ternary coordinates swapped to match the repository's
`2x²+y²+32z²` convention.  The second is

`Z (i+j) + Z 2k + Z (2i-2j+k)`.

Both embeddings are proved injective, land in the trace-zero quaternions, and
their Hamilton norms are proved equal to the two Brandt quadratic forms.  These
are actual additive lattice carriers; no quaternion-ideal or Hecke law is
assumed here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge

open scoped Quaternion
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector

abbrev HamiltonInt := ℍ[ℤ]

/-- The first Brandt lattice in the pure Hamilton quaternions. -/
def firstBrandtQuaternion (m : IntTriple) : HamiltonInt :=
  ⟨0, m.2.1, m.1 + 4 * m.2.2, m.1 - 4 * m.2.2⟩

/-- The second Brandt lattice in the pure Hamilton quaternions. -/
def secondBrandtQuaternion (m : IntTriple) : HamiltonInt :=
  ⟨0, m.1 + 2 * m.2.2, m.1 - 2 * m.2.2,
    2 * m.2.1 + m.2.2⟩

@[simp] theorem firstBrandtQuaternion_re (m : IntTriple) :
    (firstBrandtQuaternion m).re = 0 := rfl

@[simp] theorem secondBrandtQuaternion_re (m : IntTriple) :
    (secondBrandtQuaternion m).re = 0 := rfl

/-- The first quaternion norm is exactly the first Brandt ternary form. -/
theorem normSq_firstBrandtQuaternion (m : IntTriple) :
    Quaternion.normSq (firstBrandtQuaternion m) = brandtFirstQuadratic m := by
  rw [Quaternion.normSq_def']
  simp [firstBrandtQuaternion, brandtFirstQuadratic]
  ring

/-- The second quaternion norm is exactly the cross-term Brandt form. -/
theorem normSq_secondBrandtQuaternion (m : IntTriple) :
    Quaternion.normSq (secondBrandtQuaternion m) = brandtSecondQuadratic m := by
  rw [Quaternion.normSq_def']
  simp [secondBrandtQuaternion, brandtSecondQuadratic]
  ring

/-- Additive lattice embedding of the first class. -/
def firstBrandtEmbedding : IntTriple →+ HamiltonInt where
  toFun := firstBrandtQuaternion
  map_zero' := by
    apply Quaternion.ext <;> simp [firstBrandtQuaternion]
  map_add' := by
    intro m n
    apply Quaternion.ext <;> simp [firstBrandtQuaternion] <;> ring

/-- Additive lattice embedding of the second class. -/
def secondBrandtEmbedding : IntTriple →+ HamiltonInt where
  toFun := secondBrandtQuaternion
  map_zero' := by
    apply Quaternion.ext <;> simp [secondBrandtQuaternion]
  map_add' := by
    intro m n
    apply Quaternion.ext <;> simp [secondBrandtQuaternion] <;> ring

theorem firstBrandtEmbedding_injective :
    Function.Injective firstBrandtEmbedding := by
  intro m n h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  apply Prod.ext
  · simp [firstBrandtEmbedding, firstBrandtQuaternion] at hi hj hk ⊢
    omega
  · apply Prod.ext
    · simpa [firstBrandtEmbedding, firstBrandtQuaternion] using hi
    · simp [firstBrandtEmbedding, firstBrandtQuaternion] at hj hk ⊢
      omega

theorem secondBrandtEmbedding_injective :
    Function.Injective secondBrandtEmbedding := by
  intro m n h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  simp [secondBrandtEmbedding, secondBrandtQuaternion] at hi hj hk
  apply Prod.ext
  · omega
  · apply Prod.ext
    · omega
    · omega

/-- The two source lattices as actual additive subgroups of Hamilton's algebra. -/
def firstBrandtQuaternionLattice : AddSubgroup HamiltonInt :=
  firstBrandtEmbedding.range

def secondBrandtQuaternionLattice : AddSubgroup HamiltonInt :=
  secondBrandtEmbedding.range

theorem mem_firstBrandtQuaternionLattice_iff (q : HamiltonInt) :
    q ∈ firstBrandtQuaternionLattice ↔
      ∃ m : IntTriple, firstBrandtQuaternion m = q := by
  rfl

theorem mem_secondBrandtQuaternionLattice_iff (q : HamiltonInt) :
    q ∈ secondBrandtQuaternionLattice ↔
      ∃ m : IntTriple, secondBrandtQuaternion m = q := by
  rfl

/-- Every first-class ternary occurrence is reconstructed uniquely from its
quaternion occurrence. -/
def firstBrandtQuaternionEquivRange :
    IntTriple ≃ firstBrandtQuaternionLattice :=
  Equiv.ofInjective firstBrandtEmbedding firstBrandtEmbedding_injective

/-- Every second-class ternary occurrence is reconstructed uniquely from its
quaternion occurrence. -/
def secondBrandtQuaternionEquivRange :
    IntTriple ≃ secondBrandtQuaternionLattice :=
  Equiv.ofInjective secondBrandtEmbedding secondBrandtEmbedding_injective

/-- The norm-`n` fibre of the first quaternion lattice is exactly its ternary
representation population. -/
theorem firstBrandtQuaternion_norm_eq_iff (n : ℕ) (m : IntTriple) :
    Quaternion.normSq (firstBrandtEmbedding m) = (n : ℤ) ↔
      brandtFirstQuadratic m = (n : ℤ) := by
  change Quaternion.normSq (firstBrandtQuaternion m) = (n : ℤ) ↔ _
  rw [normSq_firstBrandtQuaternion]

/-- The corresponding exact fibre statement for the second class. -/
theorem secondBrandtQuaternion_norm_eq_iff (n : ℕ) (m : IntTriple) :
    Quaternion.normSq (secondBrandtEmbedding m) = (n : ℤ) ↔
      brandtSecondQuadratic m = (n : ℤ) := by
  change Quaternion.normSq (secondBrandtQuaternion m) = (n : ℤ) ↔ _
  rw [normSq_secondBrandtQuaternion]

#print axioms normSq_firstBrandtQuaternion
#print axioms normSq_secondBrandtQuaternion
#print axioms firstBrandtEmbedding_injective
#print axioms secondBrandtEmbedding_injective
#print axioms firstBrandtQuaternion_norm_eq_iff
#print axioms secondBrandtQuaternion_norm_eq_iff

end Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge
