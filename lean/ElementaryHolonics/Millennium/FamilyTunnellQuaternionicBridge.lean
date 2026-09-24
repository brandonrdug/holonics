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

section HamiltonComponents

/-- Component laws for `HamiltonInt`, restated because Mathlib's `Quaternion` no longer exposes
the `QuaternionAlgebra` component simp lemmas through the definitional wrapper.  The primed forms
are the definitional unfoldings with the structure constants `(-1, 0, -1)` in place. -/
@[simp] theorem hamilton_add_re (a b : HamiltonInt) : (a + b).re = a.re + b.re := rfl
@[simp] theorem hamilton_add_imI (a b : HamiltonInt) : (a + b).imI = a.imI + b.imI := rfl
@[simp] theorem hamilton_add_imJ (a b : HamiltonInt) : (a + b).imJ = a.imJ + b.imJ := rfl
@[simp] theorem hamilton_add_imK (a b : HamiltonInt) : (a + b).imK = a.imK + b.imK := rfl
@[simp] theorem hamilton_neg_re (a : HamiltonInt) : (-a).re = -a.re := rfl
@[simp] theorem hamilton_neg_imI (a : HamiltonInt) : (-a).imI = -a.imI := rfl
@[simp] theorem hamilton_neg_imJ (a : HamiltonInt) : (-a).imJ = -a.imJ := rfl
@[simp] theorem hamilton_neg_imK (a : HamiltonInt) : (-a).imK = -a.imK := rfl
@[simp] theorem hamilton_sub_re (a b : HamiltonInt) : (a - b).re = a.re - b.re := rfl
@[simp] theorem hamilton_sub_imI (a b : HamiltonInt) : (a - b).imI = a.imI - b.imI := rfl
@[simp] theorem hamilton_sub_imJ (a b : HamiltonInt) : (a - b).imJ = a.imJ - b.imJ := rfl
@[simp] theorem hamilton_sub_imK (a b : HamiltonInt) : (a - b).imK = a.imK - b.imK := rfl

theorem hamilton_star_re' (a : HamiltonInt) : (star a).re = a.re + 0 * a.imI := rfl
@[simp] theorem hamilton_star_re (a : HamiltonInt) : (star a).re = a.re := by
  rw [hamilton_star_re']
  ring
@[simp] theorem hamilton_star_imI (a : HamiltonInt) : (star a).imI = -a.imI := rfl
@[simp] theorem hamilton_star_imJ (a : HamiltonInt) : (star a).imJ = -a.imJ := rfl
@[simp] theorem hamilton_star_imK (a : HamiltonInt) : (star a).imK = -a.imK := rfl

theorem hamilton_mul_re' (a b : HamiltonInt) :
    (a * b).re = a.re * b.re + (-1) * a.imI * b.imI + (-1) * a.imJ * b.imJ +
      0 * (-1) * a.imJ * b.imK - (-1) * (-1) * a.imK * b.imK := rfl
theorem hamilton_mul_imI' (a b : HamiltonInt) :
    (a * b).imI = a.re * b.imI + a.imI * b.re + 0 * a.imI * b.imI - (-1) * a.imJ * b.imK +
      (-1) * a.imK * b.imJ := rfl
theorem hamilton_mul_imJ' (a b : HamiltonInt) :
    (a * b).imJ = a.re * b.imJ + (-1) * a.imI * b.imK + a.imJ * b.re + 0 * a.imJ * b.imI -
      (-1) * a.imK * b.imI := rfl
theorem hamilton_mul_imK' (a b : HamiltonInt) :
    (a * b).imK = a.re * b.imK + a.imI * b.imJ + 0 * a.imI * b.imK - a.imJ * b.imI +
      a.imK * b.re := rfl

@[simp] theorem hamilton_mul_re (a b : HamiltonInt) :
    (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK := by
  rw [hamilton_mul_re']
  ring
@[simp] theorem hamilton_mul_imI (a b : HamiltonInt) :
    (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ := by
  rw [hamilton_mul_imI']
  ring
@[simp] theorem hamilton_mul_imJ (a b : HamiltonInt) :
    (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI := by
  rw [hamilton_mul_imJ']
  ring
@[simp] theorem hamilton_mul_imK (a b : HamiltonInt) :
    (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re := by
  rw [hamilton_mul_imK']
  ring

/-- The explicit constructor of `HamiltonInt`, kept opaque so that literals stay well typed at
`HamiltonInt` (anonymous constructors elaborate at the underlying algebra type). -/
def hmk (a b c d : ℤ) : HamiltonInt := ⟨a, b, c, d⟩
@[simp] theorem hmk_re (a b c d : ℤ) : (hmk a b c d).re = a := rfl
@[simp] theorem hmk_imI (a b c d : ℤ) : (hmk a b c d).imI = b := rfl
@[simp] theorem hmk_imJ (a b c d : ℤ) : (hmk a b c d).imJ = c := rfl
@[simp] theorem hmk_imK (a b c d : ℤ) : (hmk a b c d).imK = d := rfl
@[simp] theorem hamilton_one_re : (1 : HamiltonInt).re = 1 := rfl
@[simp] theorem hamilton_one_imI : (1 : HamiltonInt).imI = 0 := rfl
@[simp] theorem hamilton_one_imJ : (1 : HamiltonInt).imJ = 0 := rfl
@[simp] theorem hamilton_one_imK : (1 : HamiltonInt).imK = 0 := rfl
@[simp] theorem hamilton_zero_re : (0 : HamiltonInt).re = 0 := rfl
@[simp] theorem hamilton_zero_imI : (0 : HamiltonInt).imI = 0 := rfl
@[simp] theorem hamilton_zero_imJ : (0 : HamiltonInt).imJ = 0 := rfl
@[simp] theorem hamilton_zero_imK : (0 : HamiltonInt).imK = 0 := rfl
@[simp] theorem hamilton_coe_re (x : ℤ) : ((x : ℤ) : HamiltonInt).re = x := rfl
@[simp] theorem hamilton_coe_imI (x : ℤ) : ((x : ℤ) : HamiltonInt).imI = 0 := rfl
@[simp] theorem hamilton_coe_imJ (x : ℤ) : ((x : ℤ) : HamiltonInt).imJ = 0 := rfl
@[simp] theorem hamilton_coe_imK (x : ℤ) : ((x : ℤ) : HamiltonInt).imK = 0 := rfl

end HamiltonComponents

@[simp] theorem hamilton_mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℤ) :
    ((⟨a₁, a₂, a₃, a₄⟩ : HamiltonInt) + ⟨b₁, b₂, b₃, b₄⟩) =
      ⟨a₁ + b₁, a₂ + b₂, a₃ + b₃, a₄ + b₄⟩ := rfl

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
    apply Quaternion.ext <;> (change _ = _ + _; simp only [firstBrandtQuaternion, Prod.fst_add, Prod.snd_add]; try ring)

/-- Additive lattice embedding of the second class. -/
def secondBrandtEmbedding : IntTriple →+ HamiltonInt where
  toFun := secondBrandtQuaternion
  map_zero' := by
    apply Quaternion.ext <;> simp [secondBrandtQuaternion]
  map_add' := by
    intro m n
    apply Quaternion.ext <;> (change _ = _ + _; simp only [secondBrandtQuaternion, Prod.fst_add, Prod.snd_add]; try ring)

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
