import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborQuotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.StdBasis

/-!
# Actual Brandt neighbors are free of rank three

The four-coordinate Brandt chart has one exact cyclic relation.  This file
proves that its actual source-addressed image is a finite free `ℤ`-module of
rank exactly three and returns a `Fin 3` basis.

The rank proof does not read the index of an arbitrarily chosen basis.  It
constructs two exact transports.  Multiplication by `p` sends every actual
neighbor point into the integral coordinate lattice, while multiplication by
`p` embeds the full integral coordinate lattice back into every actual
neighbor.  The reciprocal injections force equality with rank three.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationClassification
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient

variable {p : ℕ} [Fact p.Prime]

/-- The exact integral-coordinate inclusion. -/
def intTripleInclusion : IntTriple →+ RatTriple where
  toFun := intTripleToRat
  map_zero' := by
    simp [intTripleToRat]
  map_add' m n := by
    apply Prod.ext
    · simp [intTripleToRat]
    · apply Prod.ext <;> simp [intTripleToRat]

theorem intTripleInclusion_injective :
    Function.Injective intTripleInclusion := by
  intro m n h
  change intTripleToRat m = intTripleToRat n at h
  apply Prod.ext
  · have hx : (m.1 : ℚ) = (n.1 : ℚ) := congrArg Prod.fst h
    exact_mod_cast hx
  · apply Prod.ext
    · have hy : (m.2.1 : ℚ) = (n.2.1 : ℚ) :=
        congrArg (fun x : RatTriple => x.2.1) h
      exact_mod_cast hy
    · have hz : (m.2.2 : ℚ) = (n.2.2 : ℚ) :=
        congrArg (fun x : RatTriple => x.2.2) h
      exact_mod_cast hz

/-- Coordinate multiplication by the prime in the common rational receiver. -/
def ratTripleScaleP : RatTriple →+ RatTriple where
  toFun x := ratTripleScale (p : ℚ) x
  map_zero' := by
    simp [ratTripleScale]
  map_add' x y := by
    apply Prod.ext
    · simp [ratTripleScale]
      ring
    · apply Prod.ext <;> simp [ratTripleScale] <;> ring

private theorem p_rat_ne_zero : (p : ℚ) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem ratTripleScaleP_injective : Function.Injective (ratTripleScaleP (p := p)) := by
  intro x y h
  have hx := congrArg Prod.fst h
  have hy := congrArg (fun w : RatTriple => w.2.1) h
  have hz := congrArg (fun w : RatTriple => w.2.2) h
  simp only [ratTripleScaleP, ratTripleScale, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk] at hx hy hz
  apply Prod.ext
  · exact mul_left_cancel₀ (p_rat_ne_zero (p := p)) hx
  · apply Prod.ext
    · exact mul_left_cancel₀ (p_rat_ne_zero (p := p)) hy
    · exact mul_left_cancel₀ (p_rat_ne_zero (p := p)) hz

/-- Every actual neighbor becomes an integral triple after one complete
`p`-scale.  The witness is constructed from its retained kernel and
fractional-generator coordinates. -/
theorem BrandtNeighborOccurrence.exists_integral_p_scale (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : occurrenceNeighborSubgroup hp2 occurrence) :
    ∃ m : IntTriple,
      intTripleInclusion m = ratTripleScaleP (p := p) x.1 := by
  cases occurrence with
  | inl d =>
      rcases x.2 with ⟨m, hm, a, hx⟩
      refine ⟨(p : ℤ) • m + a • adjustedDirectionLift 32 d, ?_⟩
      rw [hx]
      apply Prod.ext
      · simp [intTripleInclusion, ratTripleScaleP, intTripleToRat,
          ratTripleAdd, ratTripleScale]
        field_simp [p_rat_ne_zero (p := p)]
      · apply Prod.ext <;>
          simp [intTripleInclusion, ratTripleScaleP, intTripleToRat,
            ratTripleAdd, ratTripleScale] <;>
          field_simp [p_rat_ne_zero (p := p)]
  | inr d =>
      rcases x.2 with ⟨m, hm, a, hx⟩
      refine ⟨(p : ℤ) • m + a • adjustedBrandtSecondDirectionLift hp2 d, ?_⟩
      rw [hx]
      apply Prod.ext
      · simp [intTripleInclusion, ratTripleScaleP, intTripleToRat,
          ratTripleAdd, ratTripleScale]
        field_simp [p_rat_ne_zero (p := p)]
      · apply Prod.ext <;>
          simp [intTripleInclusion, ratTripleScaleP, intTripleToRat,
            ratTripleAdd, ratTripleScale] <;>
          field_simp [p_rat_ne_zero (p := p)]

/-- The unique integral numerator of an actual neighbor point. -/
def BrandtNeighborOccurrence.integralPScale (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : occurrenceNeighborSubgroup hp2 occurrence) : IntTriple :=
  Classical.choose
    (BrandtNeighborOccurrence.exists_integral_p_scale hp2 occurrence x)

theorem BrandtNeighborOccurrence.intTripleInclusion_integralPScale
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (x : occurrenceNeighborSubgroup hp2 occurrence) :
    intTripleInclusion (BrandtNeighborOccurrence.integralPScale hp2 occurrence x) =
      ratTripleScaleP (p := p) x.1 :=
  Classical.choose_spec
    (BrandtNeighborOccurrence.exists_integral_p_scale hp2 occurrence x)

/-- Multiplication by `p`, with its exact integral landing type. -/
def BrandtNeighborOccurrence.neighborToIntegral (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceNeighborSubgroup hp2 occurrence →+ IntTriple where
  toFun := BrandtNeighborOccurrence.integralPScale hp2 occurrence
  map_zero' := by
    apply intTripleInclusion_injective
    rw [BrandtNeighborOccurrence.intTripleInclusion_integralPScale]
    simp [intTripleInclusion, ratTripleScaleP, ratTripleScale, intTripleToRat]
  map_add' x y := by
    apply intTripleInclusion_injective
    rw [BrandtNeighborOccurrence.intTripleInclusion_integralPScale]
    rw [map_add]
    rw [BrandtNeighborOccurrence.intTripleInclusion_integralPScale,
      BrandtNeighborOccurrence.intTripleInclusion_integralPScale]
    exact map_add _ _ _

theorem BrandtNeighborOccurrence.neighborToIntegral_injective (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Function.Injective
      (BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence) := by
  intro x y h
  change BrandtNeighborOccurrence.integralPScale hp2 occurrence x =
    BrandtNeighborOccurrence.integralPScale hp2 occurrence y at h
  apply Subtype.ext
  apply ratTripleScaleP_injective (p := p)
  rw [← BrandtNeighborOccurrence.intTripleInclusion_integralPScale,
    ← BrandtNeighborOccurrence.intTripleInclusion_integralPScale, h]

/-- Every `p`-scaled integral coordinate point belongs to every actual
source-addressed neighbor. -/
theorem BrandtNeighborOccurrence.scaled_integral_mem (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (m : IntTriple) :
    ratTripleScaleP (p := p) (intTripleInclusion m) ∈
      occurrenceNeighborSubgroup hp2 occurrence := by
  cases occurrence with
  | inl d =>
      refine ⟨(p : ℤ) • m, ?_, 0, ?_⟩
      · change (p : ℤ) ∣ intTunnellPolar 32 ((p : ℤ) • m)
          (adjustedDirectionLift 32 d)
        refine ⟨intTunnellPolar 32 m (adjustedDirectionLift 32 d), ?_⟩
        simp [intTunnellPolar]
        ring
      · apply Prod.ext
        · simp [ratTripleScaleP, intTripleInclusion, ratTripleScale,
            intTripleToRat, ratTripleAdd]
        · apply Prod.ext <;>
            simp [ratTripleScaleP, intTripleInclusion, ratTripleScale,
              intTripleToRat, ratTripleAdd]
  | inr d =>
      refine ⟨(p : ℤ) • m, ?_, 0, ?_⟩
      · change (p : ℤ) ∣ brandtSecondPolar ((p : ℤ) • m)
          (adjustedBrandtSecondDirectionLift hp2 d)
        refine ⟨brandtSecondPolar m (adjustedBrandtSecondDirectionLift hp2 d), ?_⟩
        simp [brandtSecondPolar]
        ring
      · apply Prod.ext
        · simp [ratTripleScaleP, intTripleInclusion, ratTripleScale,
            intTripleToRat, ratTripleAdd]
        · apply Prod.ext <;>
            simp [ratTripleScaleP, intTripleInclusion, ratTripleScale,
              intTripleToRat, ratTripleAdd]

/-- The full integral coordinate lattice embedded in an actual neighbor. -/
def BrandtNeighborOccurrence.integralToNeighbor (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    IntTriple →+ occurrenceNeighborSubgroup hp2 occurrence where
  toFun m := ⟨ratTripleScaleP (p := p) (intTripleInclusion m),
    BrandtNeighborOccurrence.scaled_integral_mem hp2 occurrence m⟩
  map_zero' := by
    apply Subtype.ext
    simp [ratTripleScaleP, intTripleInclusion, ratTripleScale, intTripleToRat]
  map_add' m n := by
    apply Subtype.ext
    change ratTripleScaleP (intTripleInclusion (m + n)) =
      ratTripleScaleP (intTripleInclusion m) +
        ratTripleScaleP (intTripleInclusion n)
    rw [map_add, map_add]

theorem BrandtNeighborOccurrence.integralToNeighbor_injective (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Function.Injective
      (BrandtNeighborOccurrence.integralToNeighbor hp2 occurrence) := by
  intro m n h
  apply intTripleInclusion_injective
  apply ratTripleScaleP_injective (p := p)
  exact congrArg Subtype.val h

/-! ## Exact rank and returned basis -/

/-- The standard three-coordinate basis, with its index cardinality exposed as
`Fin 3`. -/
def intTripleBasis : Module.Basis (Fin 3) ℤ IntTriple :=
  Module.Basis.ofEquivFun
    { toFun := fun m i =>
        Fin.cases m.1 (fun j => Fin.cases m.2.1 (fun _ => m.2.2) j) i
      invFun := fun f => (f 0, f 1, f 2)
      map_add' := by
        intro m n
        funext i
        fin_cases i <;> rfl
      map_smul' := by
        intro a m
        funext i
        fin_cases i <;> rfl
      left_inv := by
        intro m
        rfl
      right_inv := by
        intro f
        funext i
        fin_cases i <;> rfl }

theorem intTriple_finrank : Module.finrank ℤ IntTriple = 3 := by
  simpa using Module.finrank_eq_card_basis intTripleBasis

/-- **EVERY ACTUAL BRANDT NEIGHBOR IS A FINITE FREE INTEGRAL MODULE OF RANK
EXACTLY THREE.**  The source occurrence remains in the carrier type. -/
theorem BrandtNeighborOccurrence.finite_free_rank_three (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ∃ b : Module.Basis (Fin 3) ℤ
        (occurrenceNeighborSubgroup hp2 occurrence),
      Module.finrank ℤ (occurrenceNeighborSubgroup hp2 occurrence) = 3 := by
  let toInt :=
    (BrandtNeighborOccurrence.neighborToIntegral hp2 occurrence).toIntLinearMap
  letI : Module.Finite ℤ (occurrenceNeighborSubgroup hp2 occurrence) :=
    Module.Finite.of_injective toInt
      (BrandtNeighborOccurrence.neighborToIntegral_injective hp2 occurrence)
  letI : Module.IsTorsionFree ℤ
      (occurrenceNeighborSubgroup hp2 occurrence) := by
    constructor
    intro r hr x y hxy
    apply BrandtNeighborOccurrence.neighborToIntegral_injective hp2 occurrence
    apply Module.IsTorsionFree.isSMulRegular hr
    simpa only [map_smul] using congrArg toInt hxy
  letI : Module.Free ℤ (occurrenceNeighborSubgroup hp2 occurrence) := inferInstance
  have hupper :
      Module.finrank ℤ (occurrenceNeighborSubgroup hp2 occurrence) ≤ 3 := by
    rw [← intTriple_finrank]
    exact LinearMap.finrank_le_finrank_of_injective (f := toInt)
      (BrandtNeighborOccurrence.neighborToIntegral_injective hp2 occurrence)
  have hlower :
      3 ≤ Module.finrank ℤ (occurrenceNeighborSubgroup hp2 occurrence) := by
    rw [← intTriple_finrank]
    let fromInt :=
      (BrandtNeighborOccurrence.integralToNeighbor hp2 occurrence).toIntLinearMap
    exact LinearMap.finrank_le_finrank_of_injective (f := fromInt)
      (BrandtNeighborOccurrence.integralToNeighbor_injective hp2 occurrence)
  have hrank : Module.finrank ℤ
      (occurrenceNeighborSubgroup hp2 occurrence) = 3 := Nat.le_antisymm hupper hlower
  obtain ⟨n, b⟩ : Σ n : ℕ, Module.Basis (Fin n) ℤ
      (occurrenceNeighborSubgroup hp2 occurrence) :=
    Module.basisOfFiniteTypeTorsionFree'
  have hn : n = 3 := by
    have hb := Module.finrank_eq_card_basis b
    simpa [hrank] using hb.symm
  subst n
  exact ⟨b, hrank⟩

/-- A chosen exact rank-three basis for the actual neighbor selected by a
source occurrence. -/
def BrandtNeighborOccurrence.rankThreeBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Module.Basis (Fin 3) ℤ (occurrenceNeighborSubgroup hp2 occurrence) :=
  Classical.choose
    (BrandtNeighborOccurrence.finite_free_rank_three hp2 occurrence)

theorem BrandtNeighborOccurrence.rankThreeBasis_finrank (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Module.finrank ℤ (occurrenceNeighborSubgroup hp2 occurrence) = 3 :=
  (Classical.choose_spec
    (BrandtNeighborOccurrence.finite_free_rank_three hp2 occurrence))

#print axioms BrandtNeighborOccurrence.exists_integral_p_scale
#print axioms BrandtNeighborOccurrence.neighborToIntegral_injective
#print axioms BrandtNeighborOccurrence.scaled_integral_mem
#print axioms BrandtNeighborOccurrence.integralToNeighbor_injective
#print axioms BrandtNeighborOccurrence.finite_free_rank_three
#print axioms BrandtNeighborOccurrence.rankThreeBasis_finrank

end Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree
