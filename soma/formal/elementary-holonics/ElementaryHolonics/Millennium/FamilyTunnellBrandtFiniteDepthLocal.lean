import ElementaryHolonics.Millennium.FamilyTunnellBrandtLocalizeAtPrime

/-!
# Finite-depth local receiver at the defining prime

The actual neighbor is rational, so its local coordinate section is exposed by
the already proved integral `p`-scale.  At depth `n` the receiver is the
coordinatewise reduction into `ZMod (p^n)`.  The fibers are retained as
dependent reconstruction fibers rather than replaced by residue counts.

This file proves the finite-depth receiver compatibility and the transported
quadratic law.  It does not assert a local isometry at `p`, nor complete genus
membership; those remain an explicit open passage between the source and
neighbor fibers.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtFiniteDepthLocal

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient

variable {p : ℕ} [Fact p.Prime]

abbrev LocalDepthTriple (n : ℕ) := CoordinateTriple (ZMod (p ^ n))

/-- The exact depth-`n` residue receiver for an integral coordinate triple. -/
def finiteDepthReduce (n : ℕ) (v : IntTriple) : LocalDepthTriple (p := p) n :=
  ((v.1 : ZMod (p ^ n)), (v.2.1 : ZMod (p ^ n)), (v.2.2 : ZMod (p ^ n)))

theorem finiteDepthReduce_add (n : ℕ) (u v : IntTriple) :
    finiteDepthReduce (p := p) n (u + v) =
      finiteDepthReduce n u + finiteDepthReduce n v := by
  apply Prod.ext
  · simp [finiteDepthReduce]
  · apply Prod.ext <;> simp [finiteDepthReduce]

theorem finiteDepthReduce_zsmul (n : ℕ) (a : ℤ) (v : IntTriple) :
    finiteDepthReduce (p := p) n (a • v) =
      a • finiteDepthReduce n v := by
  apply Prod.ext
  · simp [finiteDepthReduce]
  · apply Prod.ext <;> simp [finiteDepthReduce]

/-- Restriction from depth `m` to depth `n`, for `n ≤ m`. -/
def finiteDepthRestriction {n m : ℕ} (h : n ≤ m) :
    LocalDepthTriple (p := p) m → LocalDepthTriple (p := p) n := fun v =>
  (ZMod.castHom (pow_dvd_pow p h) _ v.1,
    ZMod.castHom (pow_dvd_pow p h) _ v.2.1,
    ZMod.castHom (pow_dvd_pow p h) _ v.2.2)

theorem finiteDepthRestriction_reduce {n m : ℕ} (h : n ≤ m) (v : IntTriple) :
    finiteDepthRestriction (p := p) h (finiteDepthReduce m v) =
      finiteDepthReduce n v := by
  apply Prod.ext
  · simp [finiteDepthRestriction, finiteDepthReduce]
  · apply Prod.ext <;> simp [finiteDepthRestriction, finiteDepthReduce]

/-- The source-specific quadratic receiver at finite depth. -/
def finiteDepthQuadratic (n : ℕ)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (v : LocalDepthTriple (p := p) n) : ZMod (p ^ n) :=
  match occurrence with
  | .inl _ => 2 * v.1 ^ 2 + v.2.1 ^ 2 + 32 * v.2.2 ^ 2
  | .inr _ =>
      2 * v.1 ^ 2 + 4 * v.2.1 ^ 2 + 4 * v.2.1 * v.2.2 + 9 * v.2.2 ^ 2

theorem finiteDepthQuadratic_cast (n : ℕ)
    (occurrence : BrandtNeighborOccurrence (p := p)) (v : IntTriple) :
    finiteDepthQuadratic n occurrence (finiteDepthReduce n v) =
      match occurrence with
      | .inl _ => (intTunnellQuadratic 32 v : ZMod (p ^ n))
      | .inr _ => (brandtSecondQuadratic v : ZMod (p ^ n)) := by
  cases occurrence <;> simp [finiteDepthQuadratic, finiteDepthReduce,
    intTunnellQuadratic, brandtSecondQuadratic] <;> ring

theorem finiteDepthQuadratic_restriction {n m : ℕ} (h : n ≤ m)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (v : LocalDepthTriple (p := p) m) :
    finiteDepthQuadratic n occurrence (finiteDepthRestriction (p := p) h v) =
      ZMod.castHom (pow_dvd_pow p h) _ (finiteDepthQuadratic m occurrence v) := by
  cases occurrence <;>
    simp only [finiteDepthQuadratic, finiteDepthRestriction, ZMod.castHom_apply,
      map_add, map_mul, map_pow, map_natCast, map_ofNat]

/-- Source receiver section at depth `n`. -/
def sourceFiniteDepthReceiver (n : ℕ)
    (occurrence : BrandtNeighborOccurrence (p := p)) (v : IntTriple) :
    LocalDepthTriple (p := p) n :=
  finiteDepthReduce n v

/-- Neighbor receiver section at depth `n`, using the exact integral numerator
returned by the previously proved one-`p` scaling passage. -/
def neighborFiniteDepthReceiver (hp2 : p ≠ 2) (n : ℕ)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : occurrenceNeighborSubgroup hp2 occurrence) :
    LocalDepthTriple (p := p) n :=
  finiteDepthReduce n
    (BrandtNeighborOccurrence.integralPScale hp2 occurrence x)

/-- The source reconstruction fiber at a finite receiver depth. -/
def sourceReconstructionFiber (n : ℕ)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (y : LocalDepthTriple (p := p) n) :=
  {v : IntTriple // sourceFiniteDepthReceiver n occurrence v = y}

/-- The neighbor reconstruction fiber at a finite receiver depth. -/
def neighborReconstructionFiber (hp2 : p ≠ 2) (n : ℕ)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (y : LocalDepthTriple (p := p) n) :=
  {x : occurrenceNeighborSubgroup hp2 occurrence //
    neighborFiniteDepthReceiver hp2 n occurrence x = y}

theorem sourceReconstructionFiber_mem (n : ℕ)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (y : LocalDepthTriple (p := p) n)
    (v : sourceReconstructionFiber n occurrence y) :
    sourceFiniteDepthReceiver n occurrence v.1 = y := v.2

theorem neighborReconstructionFiber_mem (hp2 : p ≠ 2) (n : ℕ)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (y : LocalDepthTriple (p := p) n)
    (x : neighborReconstructionFiber hp2 n occurrence y) :
    neighborFiniteDepthReceiver hp2 n occurrence x.1 = y := x.2

/-! The remaining defining-prime passage is now typed: it must supply an
isometry/transport between these source and neighbor local fibers, compatible
with the restriction maps and the quadratic receiver. -/

#print axioms finiteDepthReduce_add
#print axioms finiteDepthRestriction_reduce
#print axioms finiteDepthQuadratic_cast
#print axioms finiteDepthQuadratic_restriction
#print axioms sourceReconstructionFiber_mem
#print axioms neighborReconstructionFiber_mem

end Soma.Holonics.Millennium.FamilyTunnellBrandtFiniteDepthLocal
