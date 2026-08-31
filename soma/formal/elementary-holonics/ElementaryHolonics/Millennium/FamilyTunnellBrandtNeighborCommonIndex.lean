import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborDiscriminant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# The common index of an actual odd-prime Brandt neighbor

The integral source lattice and its actual `p`-neighbor meet in the retained
polar kernel.  This file computes the neighbor-side index directly from the
four-coordinate quotient: the fourth coordinate modulo `p` is the complete
quotient receiver, and the unique cyclic relation lies in its kernel.

The source-side computation is carried by the polar residue functional.  Its
surjectivity follows from the normalized projective pivot, rather than from a
cardinality assertion.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationClassification
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborDiscriminant
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborGram
open Soma.Holonics.Millennium.FamilyTunnellBrandtRelationKernel
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree

variable {p : ℕ} [Fact p.Prime]

private theorem two_mod_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

private theorem four_mod_ne_zero (hp2 : p ≠ 2) : (4 : ZMod p) ≠ 0 := by
  rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
  exact pow_ne_zero 2 (two_mod_ne_zero (p := p) hp2)

/-! ## The neighbor-side quotient -/

/-- The exact residual coefficient of a four-coordinate neighbor chart. -/
def fourthResidueHom : NeighborCoordinates →+ ZMod p where
  toFun u := (u.2.2.2 : ZMod p)
  map_zero' := by simp
  map_add' u v := by simp

theorem fourthResidueHom_surjective :
    Function.Surjective (fourthResidueHom (p := p)) := by
  intro a
  refine ⟨(0, 0, 0, (a.val : ℤ)), ?_⟩
  simpa [fourthResidueHom] using ZMod.natCast_zmod_val a

theorem fourthResidueKernel_index :
    (fourthResidueHom (p := p)).ker.index = p := by
  rw [AddSubgroup.index_ker]
  have hrange : (fourthResidueHom (p := p)).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr fourthResidueHom_surjective
  rw [hrange]
  simpa using Nat.card_zmod p

/-- The cyclic relation is invisible to the fourth-coordinate residue
receiver because its complete turn is exactly `p`. -/
theorem relationSubgroup_le_fourthResidueKernel (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    AddSubgroup.zmultiples (occurrenceRelationGenerator hp2 occurrence) ≤
      (fourthResidueHom (p := p)).ker := by
  intro u hu
  rw [AddSubgroup.mem_zmultiples_iff] at hu
  obtain ⟨k, rfl⟩ := hu
  rw [AddMonoidHom.mem_ker]
  simp [fourthResidueHom, occurrenceRelationGenerator_fourth]

/-- The retained kernel inside the exact cyclic quotient. -/
def quotientPolarCore (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    AddSubgroup (OccurrenceQuotient hp2 occurrence) :=
  (fourthResidueHom (p := p)).ker.map
    (QuotientAddGroup.mk'
      (AddSubgroup.zmultiples (occurrenceRelationGenerator hp2 occurrence)))

theorem quotientPolarCore_index (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (quotientPolarCore hp2 occurrence).index = p := by
  let R := AddSubgroup.zmultiples (occurrenceRelationGenerator hp2 occurrence)
  let q := QuotientAddGroup.mk' R
  calc
    (quotientPolarCore hp2 occurrence).index =
        (fourthResidueHom (p := p)).ker.index := by
      apply AddSubgroup.index_map_eq
      · exact QuotientAddGroup.mk'_surjective R
      · rw [QuotientAddGroup.ker_mk']
        exact relationSubgroup_le_fourthResidueKernel hp2 occurrence
    _ = p := fourthResidueKernel_index

/-- The same retained core transported into the actual rational neighbor. -/
def neighborPolarCore (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    AddSubgroup (occurrenceNeighborSubgroup hp2 occurrence) :=
  (quotientPolarCore hp2 occurrence).map
    (occurrenceQuotientEquivNeighbor hp2 occurrence).toAddMonoidHom

theorem neighborPolarCore_index (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (neighborPolarCore hp2 occurrence).index = p := by
  change (AddSubgroup.map
      (occurrenceQuotientEquivNeighbor hp2 occurrence :
        OccurrenceQuotient hp2 occurrence →+
          occurrenceNeighborSubgroup hp2 occurrence)
      (quotientPolarCore hp2 occurrence)).index = p
  rw [AddSubgroup.index_map_equiv (quotientPolarCore hp2 occurrence)
    (occurrenceQuotientEquivNeighbor hp2 occurrence)]
  exact quotientPolarCore_index hp2 occurrence

/-! ## The source-side polar receiver -/

/-- The corrected integral direction retained by an occurrence. -/
def occurrenceDirectionLift (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : IntTriple :=
  match occurrence with
  | .inl d => adjustedDirectionLift 32 d
  | .inr d => adjustedBrandtSecondDirectionLift hp2 d

/-- The source full-polar functional reduced at `p`. -/
def occurrencePolarResidueHom (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : IntTriple →+ ZMod p where
  toFun m :=
    match occurrence with
    | .inl d => (intTunnellPolar 32 m (adjustedDirectionLift 32 d) : ZMod p)
    | .inr d =>
        (brandtSecondPolar m (adjustedBrandtSecondDirectionLift hp2 d) : ZMod p)
  map_zero' := by
    cases occurrence <;> simp [intTunnellPolar, brandtSecondPolar]
  map_add' m n := by
    cases occurrence <;>
      simp [intTunnellPolar, brandtSecondPolar] <;> ring

/-- The normalized projective pivot makes the source polar residue functional
onto.  The first branch uses the `x` pivot; the infinity branch uses the `y`
pivot. -/
theorem occurrencePolarResidueHom_surjective (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Function.Surjective (occurrencePolarResidueHom hp2 occurrence) := by
  intro a
  cases occurrence with
  | inl d =>
      rcases d with ⟨chart, hisotropic⟩
      cases chart with
      | inl yz =>
          let c : ZMod p := a / 4
          refine ⟨((c.val : ℤ), 0, 0), ?_⟩
          have hv := reduce_adjustedDirectionLift (p := p) hp2 32
            ⟨Sum.inl yz, hisotropic⟩
          have hvx := congrArg Prod.fst hv
          simp only [projectiveDirectionVector] at hvx
          simp [occurrencePolarResidueHom, intTunnellPolar]
          rw [show ((adjustedDirectionLift 32
              ⟨Sum.inl yz, hisotropic⟩).1 : ZMod p) = 1 by
                simpa [reduceTriple] using hvx]
          dsimp [c]
          field_simp [four_mod_ne_zero (p := p) hp2]
      | inr z =>
          let c : ZMod p := a / 2
          refine ⟨(0, (c.val : ℤ), 0), ?_⟩
          have hv := reduce_adjustedDirectionLift (p := p) hp2 32
            ⟨Sum.inr z, hisotropic⟩
          have hvy := congrArg (fun w => w.2.1) hv
          simp only [projectiveDirectionVector] at hvy
          simp [occurrencePolarResidueHom, intTunnellPolar]
          rw [show ((adjustedDirectionLift 32
              ⟨Sum.inr z, hisotropic⟩).2.1 : ZMod p) = 1 by
                simpa [reduceTriple] using hvy]
          dsimp [c]
          field_simp [two_mod_ne_zero (p := p) hp2]
  | inr d =>
      rcases d with ⟨chart, hisotropic⟩
      cases chart with
      | inl yz =>
          let c : ZMod p := a / 4
          refine ⟨((c.val : ℤ), 0, 0), ?_⟩
          have hv := reduce_adjustedBrandtSecondDirectionLift (p := p) hp2
            ⟨Sum.inl yz, hisotropic⟩
          have hvx := congrArg Prod.fst hv
          simp only [brandtSecondDirectionVector, thinToBrandtSecondMod,
            projectiveDirectionVector] at hvx
          simp [occurrencePolarResidueHom, brandtSecondPolar]
          rw [show ((adjustedBrandtSecondDirectionLift hp2
              ⟨Sum.inl yz, hisotropic⟩).1 : ZMod p) = 1 by
                simpa [reduceTriple] using hvx]
          dsimp [c]
          field_simp [four_mod_ne_zero (p := p) hp2]
      | inr z =>
          let c : ZMod p := a / 4
          refine ⟨(0, (c.val : ℤ), 0), ?_⟩
          have hv := reduce_adjustedBrandtSecondDirectionLift (p := p) hp2
            ⟨Sum.inr z, hisotropic⟩
          have hvy := congrArg (fun w => w.2.1) hv
          have hvz := congrArg (fun w => w.2.2) hv
          simp only [brandtSecondDirectionVector, thinToBrandtSecondMod,
            projectiveDirectionVector] at hvy hvz
          simp [occurrencePolarResidueHom, brandtSecondPolar]
          have hcoeff : ((8 * (adjustedBrandtSecondDirectionLift hp2
                ⟨Sum.inr z, hisotropic⟩).2.1 +
              4 * (adjustedBrandtSecondDirectionLift hp2
                ⟨Sum.inr z, hisotropic⟩).2.2 : ℤ) : ZMod p) = 4 := by
            push_cast
            rw [show ((adjustedBrandtSecondDirectionLift hp2
                ⟨Sum.inr z, hisotropic⟩).2.1 : ZMod p) =
                  (1 - z) / 2 by simpa [reduceTriple] using hvy]
            rw [show ((adjustedBrandtSecondDirectionLift hp2
                ⟨Sum.inr z, hisotropic⟩).2.2 : ZMod p) = z by
                  simpa [reduceTriple] using hvz]
            field_simp [two_mod_ne_zero (p := p) hp2]
            ring
          push_cast at hcoeff
          calc
            8 * c *
                  ((adjustedBrandtSecondDirectionLift hp2
                    ⟨Sum.inr z, hisotropic⟩).2.1 : ZMod p) +
                4 * c *
                  ((adjustedBrandtSecondDirectionLift hp2
                    ⟨Sum.inr z, hisotropic⟩).2.2 : ZMod p) =
                c * (8 * ((adjustedBrandtSecondDirectionLift hp2
                    ⟨Sum.inr z, hisotropic⟩).2.1 : ZMod p) +
                  4 * ((adjustedBrandtSecondDirectionLift hp2
                    ⟨Sum.inr z, hisotropic⟩).2.2 : ZMod p)) := by ring
            _ = c * 4 := by rw [hcoeff]
            _ = a := by
              dsimp [c]
              field_simp [four_mod_ne_zero (p := p) hp2]

theorem occurrencePolarResidueKernel_index (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrencePolarResidueHom hp2 occurrence).ker.index = p := by
  rw [AddSubgroup.index_ker]
  have hrange : (occurrencePolarResidueHom hp2 occurrence).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr
      (occurrencePolarResidueHom_surjective hp2 occurrence)
  rw [hrange]
  simpa using Nat.card_zmod p

/-! ## Both integral populations in the common rational ambient receiver -/

/-- The complete source integral lattice in the common rational chart. -/
def sourceIntegralLattice : AddSubgroup RatTriple :=
  (⊤ : AddSubgroup IntTriple).map intTripleInclusion

/-- The retained polar kernel in that same chart. -/
def sourcePolarCore (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : AddSubgroup RatTriple :=
  (occurrencePolarResidueHom hp2 occurrence).ker.map intTripleInclusion

theorem sourcePolarCore_le_sourceIntegralLattice (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    sourcePolarCore hp2 occurrence ≤ sourceIntegralLattice := by
  exact AddSubgroup.map_mono le_top

/-- The source lattice sees the retained polar kernel with exact index `p`. -/
theorem sourcePolarCore_relIndex_sourceIntegralLattice (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (sourcePolarCore hp2 occurrence).relIndex sourceIntegralLattice = p := by
  rw [sourcePolarCore, sourceIntegralLattice,
    AddSubgroup.relIndex_map_map_of_injective
      (occurrencePolarResidueHom hp2 occurrence).ker ⊤
      intTripleInclusion_injective]
  rw [AddSubgroup.relIndex_top_right]
  exact occurrencePolarResidueKernel_index hp2 occurrence

/-- The corrected isotropic direction itself lies in the retained polar
kernel.  This is the exact `p·(v/p)=v` return on the source side. -/
theorem occurrenceDirectionLift_mem_polarResidueKernel (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceDirectionLift hp2 occurrence ∈
      (occurrencePolarResidueHom hp2 occurrence).ker := by
  rw [AddMonoidHom.mem_ker]
  cases occurrence with
  | inl d =>
      obtain ⟨q, hq⟩ := prime_sq_dvd_adjustedDirectionLift_norm
        (p := p) hp2 32 d
      change (intTunnellPolar 32 (adjustedDirectionLift 32 d)
        (adjustedDirectionLift 32 d) : ZMod p) = 0
      have hpolar : intTunnellPolar 32 (adjustedDirectionLift 32 d)
          (adjustedDirectionLift 32 d) =
        2 * intTunnellQuadratic 32 (adjustedDirectionLift 32 d) := by
        simp [intTunnellPolar, intTunnellQuadratic]
        ring
      rw [hpolar, hq]
      push_cast
      simp
  | inr d =>
      obtain ⟨q, hq⟩ := prime_sq_dvd_adjustedBrandtSecondDirectionLift_norm
        (p := p) hp2 d
      change (brandtSecondPolar (adjustedBrandtSecondDirectionLift hp2 d)
        (adjustedBrandtSecondDirectionLift hp2 d) : ZMod p) = 0
      have hpolar : brandtSecondPolar (adjustedBrandtSecondDirectionLift hp2 d)
          (adjustedBrandtSecondDirectionLift hp2 d) =
        2 * brandtSecondQuadratic (adjustedBrandtSecondDirectionLift hp2 d) := by
        simp [brandtSecondPolar, brandtSecondQuadratic]
        ring
      rw [hpolar, hq]
      push_cast
      simp

/-- The neighbor-side core, now embedded into the shared rational ambient
receiver. -/
def ambientNeighborPolarCore (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : AddSubgroup RatTriple :=
  (neighborPolarCore hp2 occurrence).map
    (occurrenceNeighborSubgroup hp2 occurrence).subtype

theorem ambientNeighborPolarCore_relIndex_neighbor (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (ambientNeighborPolarCore hp2 occurrence).relIndex
      (occurrenceNeighborSubgroup hp2 occurrence) = p := by
  have hmap := AddSubgroup.relIndex_map_map_of_injective
    (neighborPolarCore hp2 occurrence) ⊤
    (occurrenceNeighborSubgroup hp2 occurrence).subtype_injective
  rw [AddSubgroup.relIndex_top_right, neighborPolarCore_index] at hmap
  have htop : AddSubgroup.map
      (occurrenceNeighborSubgroup hp2 occurrence).subtype
      ⊤ = occurrenceNeighborSubgroup hp2 occurrence := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  rw [htop] at hmap
  simpa [ambientNeighborPolarCore] using hmap

/-! ## Identification of the two retained cores -/

/-- A first-pivot chart whose fourth coordinate completes a `p`-turn returns
an integral point in the same linear residue kernel. -/
theorem firstPivot_completeTurn_returns_kernel
    (A B C : ℤ) (v : IntTriple) (u : NeighborCoordinates)
    (hA : (A : ZMod p) ≠ 0)
    (hv : (p : ℤ) ∣ A * v.1 + B * v.2.1 + C * v.2.2)
    (hu : (p : ℤ) ∣ u.2.2.2) :
    ∃ m : IntTriple,
      (p : ℤ) ∣ A * m.1 + B * m.2.1 + C * m.2.2 ∧
      intTripleInclusion m = firstPivotNeighborHom (p := p) A B C v u := by
  obtain ⟨k, hk⟩ := hu
  let m₀ := firstPivotKernelPoint (p := p) A B C u.1 u.2.1 u.2.2.1
  let m : IntTriple := m₀ + k • v
  have hm₀ : (p : ℤ) ∣ A * m₀.1 + B * m₀.2.1 + C * m₀.2.2 := by
    apply (firstPivotKernel_iff (p := p) hA m₀).2
    exact ⟨u.1, rfl⟩
  refine ⟨m, ?_, ?_⟩
  · convert dvd_add hm₀ (hv.mul_left k) using 1 <;>
      simp [m] <;> ring
  · have hpQ : (p : ℚ) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hratio : (u.2.2.2 : ℚ) / (p : ℚ) = (k : ℚ) := by
      rw [hk]
      push_cast
      field_simp [hpQ]
    apply Prod.ext
    · simp [m, m₀, intTripleInclusion, intTripleToRat,
        firstPivotNeighborHom, firstPivotNeighborPoint, firstPivotKernelPoint,
        ratTripleAdd, ratTripleScale, hratio]
    · apply Prod.ext <;>
        simp [m, m₀, intTripleInclusion, intTripleToRat,
          firstPivotNeighborHom, firstPivotNeighborPoint, firstPivotKernelPoint,
          ratTripleAdd, ratTripleScale, hratio] <;> ring

/-- The corresponding second-pivot complete-turn theorem. -/
theorem secondPivot_completeTurn_returns_kernel
    (A B C : ℤ) (v : IntTriple) (u : NeighborCoordinates)
    (hA : (A : ZMod p) = 0) (hB : (B : ZMod p) ≠ 0)
    (hv : (p : ℤ) ∣ A * v.1 + B * v.2.1 + C * v.2.2)
    (hu : (p : ℤ) ∣ u.2.2.2) :
    ∃ m : IntTriple,
      (p : ℤ) ∣ A * m.1 + B * m.2.1 + C * m.2.2 ∧
      intTripleInclusion m = secondPivotNeighborHom (p := p) B C v u := by
  obtain ⟨k, hk⟩ := hu
  let m₀ := secondPivotKernelPoint (p := p) B C u.1 u.2.1 u.2.2.1
  let m : IntTriple := m₀ + k • v
  have hm₀ : (p : ℤ) ∣ A * m₀.1 + B * m₀.2.1 + C * m₀.2.2 := by
    apply (secondPivotKernel_iff (p := p) hA hB m₀).2
    exact ⟨u.2.1, rfl⟩
  refine ⟨m, ?_, ?_⟩
  · convert dvd_add hm₀ (hv.mul_left k) using 1 <;>
      simp [m] <;> ring
  · have hpQ : (p : ℚ) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hratio : (u.2.2.2 : ℚ) / (p : ℚ) = (k : ℚ) := by
      rw [hk]
      push_cast
      field_simp [hpQ]
    apply Prod.ext
    · simp [m, m₀, intTripleInclusion, intTripleToRat,
        secondPivotNeighborHom, secondPivotNeighborPoint, secondPivotKernelPoint,
        ratTripleAdd, ratTripleScale, hratio]
    · apply Prod.ext <;>
        simp [m, m₀, intTripleInclusion, intTripleToRat,
          secondPivotNeighborHom, secondPivotNeighborPoint, secondPivotKernelPoint,
          ratTripleAdd, ratTripleScale, hratio] <;> ring

/-- A zero fourth residue in the exact occurrence chart is precisely a point
of the source polar kernel.  This direction is the nontrivial inclusion needed
for common-index cancellation. -/
theorem coordinateFourthKernel_maps_to_sourcePolarCore (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u : NeighborCoordinates)
    (hu : u ∈ (fourthResidueHom (p := p)).ker) :
    brandtNeighborCoordinateHom hp2 occurrence u ∈
      sourcePolarCore hp2 occurrence := by
  have hudvd : (p : ℤ) ∣ u.2.2.2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    exact hu
  cases occurrence with
  | inl d =>
      let v := adjustedDirectionLift 32 d
      have hvpolar : (p : ℤ) ∣
          4 * v.1 * v.1 + 2 * v.2.1 * v.2.1 + 64 * v.2.2 * v.2.2 := by
        have hvker := occurrenceDirectionLift_mem_polarResidueKernel hp2
          (Sum.inl d)
        rw [AddMonoidHom.mem_ker] at hvker
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
          (by simpa [occurrencePolarResidueHom, occurrenceDirectionLift,
            intTunnellPolar, v] using hvker)
      rcases d with ⟨chart, hisotropic⟩
      cases chart with
      | inl yz =>
          have hreduce := reduce_adjustedDirectionLift (p := p) hp2 32
            ⟨Sum.inl yz, hisotropic⟩
          have hvx := congrArg Prod.fst hreduce
          have hA : ((4 * v.1 : ℤ) : ZMod p) ≠ 0 := by
            push_cast
            rw [show (v.1 : ZMod p) = 1 by
              simpa [v, reduceTriple, projectiveDirectionVector] using hvx]
            simpa using four_mod_ne_zero (p := p) hp2
          obtain ⟨m, hm, heq⟩ := firstPivot_completeTurn_returns_kernel
            (p := p) (4 * v.1) (2 * v.2.1) (64 * v.2.2) v u hA
            (by simpa [mul_assoc] using hvpolar) hudvd
          rw [sourcePolarCore, AddSubgroup.mem_map]
          refine ⟨m, ?_, ?_⟩
          · rw [AddMonoidHom.mem_ker]
            apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2
            convert hm using 1 <;>
              simp [occurrencePolarResidueHom, intTunnellPolar, v] <;> ring
          · simpa [brandtNeighborCoordinateHom, firstBrandtNeighborHom, v]
              using heq
      | inr z =>
          have hreduce := reduce_adjustedDirectionLift (p := p) hp2 32
            ⟨Sum.inr z, hisotropic⟩
          have hvx := congrArg Prod.fst hreduce
          have hvy := congrArg (fun w => w.2.1) hreduce
          have hA : ((4 * v.1 : ℤ) : ZMod p) = 0 := by
            push_cast
            rw [show (v.1 : ZMod p) = 0 by
              simpa [v, reduceTriple, projectiveDirectionVector] using hvx]
            ring
          have hB : ((2 * v.2.1 : ℤ) : ZMod p) ≠ 0 := by
            push_cast
            rw [show (v.2.1 : ZMod p) = 1 by
              simpa [v, reduceTriple, projectiveDirectionVector] using hvy]
            simpa using two_mod_ne_zero (p := p) hp2
          obtain ⟨m, hm, heq⟩ := secondPivot_completeTurn_returns_kernel
            (p := p) (4 * v.1) (2 * v.2.1) (64 * v.2.2) v u hA hB
            (by simpa [mul_assoc] using hvpolar) hudvd
          rw [sourcePolarCore, AddSubgroup.mem_map]
          refine ⟨m, ?_, ?_⟩
          · rw [AddMonoidHom.mem_ker]
            apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2
            convert hm using 1 <;>
              simp [occurrencePolarResidueHom, intTunnellPolar, v] <;> ring
          · simpa [brandtNeighborCoordinateHom, firstBrandtNeighborHom, v]
              using heq
  | inr d =>
      let v := adjustedBrandtSecondDirectionLift hp2 d
      let A := 4 * v.1
      let B := 8 * v.2.1 + 4 * v.2.2
      let C := 4 * v.2.1 + 18 * v.2.2
      have hvpolar : (p : ℤ) ∣ A * v.1 + B * v.2.1 + C * v.2.2 := by
        have hvker := occurrenceDirectionLift_mem_polarResidueKernel hp2
          (Sum.inr d)
        rw [AddMonoidHom.mem_ker] at hvker
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
        convert hvker using 1 <;>
          simp [occurrencePolarResidueHom, occurrenceDirectionLift,
            brandtSecondPolar, A, B, C, v] <;> ring
      rcases d with ⟨chart, hisotropic⟩
      cases chart with
      | inl yz =>
          have hreduce := reduce_adjustedBrandtSecondDirectionLift (p := p) hp2
            ⟨Sum.inl yz, hisotropic⟩
          have hvx := congrArg Prod.fst hreduce
          have hA : (A : ZMod p) ≠ 0 := by
            simp only [A]
            push_cast
            rw [show (v.1 : ZMod p) = 1 by
              simpa [v, reduceTriple, brandtSecondDirectionVector,
                thinToBrandtSecondMod, projectiveDirectionVector] using hvx]
            simpa using four_mod_ne_zero (p := p) hp2
          obtain ⟨m, hm, heq⟩ := firstPivot_completeTurn_returns_kernel
            (p := p) A B C v u hA hvpolar hudvd
          rw [sourcePolarCore, AddSubgroup.mem_map]
          refine ⟨m, ?_, ?_⟩
          · rw [AddMonoidHom.mem_ker]
            apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2
            convert hm using 1 <;>
              simp [occurrencePolarResidueHom, brandtSecondPolar,
                A, B, C, v] <;> ring
          · simpa [brandtNeighborCoordinateHom, secondBrandtNeighborHom,
              A, B, C, v] using heq
      | inr z =>
          have hreduce := reduce_adjustedBrandtSecondDirectionLift (p := p) hp2
            ⟨Sum.inr z, hisotropic⟩
          have hvx := congrArg Prod.fst hreduce
          have hvy := congrArg (fun w => w.2.1) hreduce
          have hvz := congrArg (fun w => w.2.2) hreduce
          have hA : (A : ZMod p) = 0 := by
            simp only [A]
            push_cast
            rw [show (v.1 : ZMod p) = 0 by
              simpa [v, reduceTriple, brandtSecondDirectionVector,
                thinToBrandtSecondMod, projectiveDirectionVector] using hvx]
            ring
          have hB : (B : ZMod p) ≠ 0 := by
            have hcoeff : (B : ZMod p) = 4 := by
              simp only [B]
              push_cast
              rw [show (v.2.1 : ZMod p) = (1 - z) / 2 by
                simpa [v, reduceTriple, brandtSecondDirectionVector,
                  thinToBrandtSecondMod, projectiveDirectionVector] using hvy]
              rw [show (v.2.2 : ZMod p) = z by
                simpa [v, reduceTriple, brandtSecondDirectionVector,
                  thinToBrandtSecondMod, projectiveDirectionVector] using hvz]
              field_simp [two_mod_ne_zero (p := p) hp2]
              ring
            rw [hcoeff]
            exact four_mod_ne_zero (p := p) hp2
          obtain ⟨m, hm, heq⟩ := secondPivot_completeTurn_returns_kernel
            (p := p) A B C v u hA hB hvpolar hudvd
          rw [sourcePolarCore, AddSubgroup.mem_map]
          refine ⟨m, ?_, ?_⟩
          · rw [AddMonoidHom.mem_ker]
            apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2
            convert hm using 1 <;>
              simp [occurrencePolarResidueHom, brandtSecondPolar,
                A, B, C, v] <;> ring
          · simpa [brandtNeighborCoordinateHom, secondBrandtNeighborHom,
              A, B, C, v] using heq

/-- The neighbor-side retained core is contained in the source polar core
after both are placed in the common rational receiver. -/
theorem ambientNeighborPolarCore_le_sourcePolarCore (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ambientNeighborPolarCore hp2 occurrence ≤ sourcePolarCore hp2 occurrence := by
  intro x hx
  rw [ambientNeighborPolarCore, AddSubgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [neighborPolarCore, AddSubgroup.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [quotientPolarCore, AddSubgroup.mem_map] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact coordinateFourthKernel_maps_to_sourcePolarCore hp2 occurrence u hu

/-- Every source polar-kernel point is admitted by the actual neighbor using
zero fractional coefficient. -/
theorem sourcePolarCore_le_neighbor (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    sourcePolarCore hp2 occurrence ≤ occurrenceNeighborSubgroup hp2 occurrence := by
  intro x hx
  rw [sourcePolarCore, AddSubgroup.mem_map] at hx
  obtain ⟨m, hm, rfl⟩ := hx
  rw [AddMonoidHom.mem_ker] at hm
  cases occurrence with
  | inl d =>
      refine ⟨m, ?_, 0, ?_⟩
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
          (by simpa [occurrencePolarResidueHom, polarKernel] using hm)
      · simp [intTripleInclusion, intTripleToRat, ratTripleAdd, ratTripleScale]
  | inr d =>
      refine ⟨m, ?_, 0, ?_⟩
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
          (by simpa [occurrencePolarResidueHom, brandtSecondPolarKernel] using hm)
      · simp [intTripleInclusion, intTripleToRat, ratTripleAdd, ratTripleScale]

/-- The occurrence's primitive `v/p` current in the common rational chart. -/
def occurrenceFractionalGenerator (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : RatTriple :=
  ratTripleScale ((1 : ℚ) / (p : ℚ))
    (intTripleToRat (occurrenceDirectionLift hp2 occurrence))

theorem occurrenceFractionalGenerator_mem_neighbor (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceFractionalGenerator hp2 occurrence ∈
      occurrenceNeighborSubgroup hp2 occurrence := by
  cases occurrence with
  | inl d =>
      exact fractionalGenerator_mem_integralNeighbor (p := p) hp2 32 d
  | inr d =>
      exact fractionalGenerator_mem_brandtSecondIntegralNeighbor (p := p) hp2 d

/-- The primitive fractional generator has not yet completed a full `p`-turn,
so it is not an integral source-lattice point. -/
theorem occurrenceFractionalGenerator_not_mem_sourceIntegralLattice
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceFractionalGenerator hp2 occurrence ∉ sourceIntegralLattice := by
  intro hx
  rw [sourceIntegralLattice, AddSubgroup.mem_map] at hx
  obtain ⟨m, hm, hmx⟩ := hx
  have hvnonzero : reduceTriple (p := p)
      (occurrenceDirectionLift hp2 occurrence) ≠ (0, 0, 0) := by
    cases occurrence with
    | inl d =>
        rw [occurrenceDirectionLift,
          reduce_adjustedDirectionLift (p := p) hp2 32 d]
        exact projectiveDirectionVector_ne_zero d
    | inr d =>
        rw [occurrenceDirectionLift,
          reduce_adjustedBrandtSecondDirectionLift (p := p) hp2 d]
        exact brandtSecondDirectionVector_ne_zero hp2 d
  have hzero :
      ratTripleAdd (intTripleToRat (-m))
          (ratTripleScale ((1 : ℚ) / (p : ℚ))
            (intTripleToRat (occurrenceDirectionLift hp2 occurrence))) =
        (0, 0, 0) := by
    have hmx' : intTripleInclusion m =
        occurrenceFractionalGenerator hp2 occurrence := by
      simpa using hmx
    apply Prod.ext
    · have h := congrArg Prod.fst hmx'
      simp [intTripleInclusion, occurrenceFractionalGenerator,
        intTripleToRat, ratTripleAdd, ratTripleScale] at h ⊢
      linarith
    · apply Prod.ext
      · have h := congrArg (fun w : RatTriple => w.2.1) hmx'
        simp [intTripleInclusion, occurrenceFractionalGenerator,
          intTripleToRat, ratTripleAdd, ratTripleScale] at h ⊢
        linarith
      · have h := congrArg (fun w : RatTriple => w.2.2) hmx'
        simp [intTripleInclusion, occurrenceFractionalGenerator,
          intTripleToRat, ratTripleAdd, ratTripleScale] at h ⊢
        linarith
  have hdvd : (p : ℤ) ∣ 1 :=
    fourthCoordinate_dvd_of_fractionalPoint_eq_zero (p := p)
      (-m) (occurrenceDirectionLift hp2 occurrence) 1 hvnonzero hzero
  have hpunit : IsUnit (p : ℤ) := isUnit_iff_dvd_one.mpr hdvd
  have habs : Int.natAbs (p : ℤ) = 1 := Int.isUnit_iff_natAbs_eq.mp hpunit
  have hpone : p = 1 := by simpa using habs
  exact (Fact.out : p.Prime).ne_one hpone

/-- The two index-`p` descriptions of the retained population are the same
subgroup of the rational ambient receiver.  The fractional generator rules
out a further index-one collapse on the neighbor side. -/
theorem ambientNeighborPolarCore_eq_sourcePolarCore
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    ambientNeighborPolarCore hp2 occurrence = sourcePolarCore hp2 occurrence := by
  let A := ambientNeighborPolarCore hp2 occurrence
  let S := sourcePolarCore hp2 occurrence
  let N := occurrenceNeighborSubgroup hp2 occurrence
  have hAS : A ≤ S := ambientNeighborPolarCore_le_sourcePolarCore hp2 occurrence
  have hSN : S ≤ N := sourcePolarCore_le_neighbor hp2 occurrence
  have hprod : A.relIndex S * S.relIndex N = p := by
    rw [AddSubgroup.relIndex_mul_relIndex A S N hAS hSN]
    exact ambientNeighborPolarCore_relIndex_neighbor hp2 occurrence
  have hSN_ne_one : S.relIndex N ≠ 1 := by
    intro hindex
    have hNS : N ≤ S := (AddSubgroup.relIndex_eq_one.mp hindex)
    have hgenS : occurrenceFractionalGenerator hp2 occurrence ∈ S :=
      hNS (occurrenceFractionalGenerator_mem_neighbor hp2 occurrence)
    have hgenL : occurrenceFractionalGenerator hp2 occurrence ∈
        sourceIntegralLattice :=
      sourcePolarCore_le_sourceIntegralLattice hp2 occurrence hgenS
    exact occurrenceFractionalGenerator_not_mem_sourceIntegralLattice
      hp2 occurrence hgenL
  have hSNdvd : S.relIndex N ∣ p := by
    exact ⟨A.relIndex S, by simpa [mul_comm] using hprod.symm⟩
  have hSNp : S.relIndex N = p :=
    ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hSNdvd).resolve_left hSN_ne_one
  have hAone : A.relIndex S = 1 := by
    rw [hSNp] at hprod
    exact Nat.mul_right_cancel (Fact.out : p.Prime).pos (by simpa using hprod)
  exact le_antisymm hAS (AddSubgroup.relIndex_eq_one.mp hAone)

/-- Equal nonzero indices from a common integral core force covolume one
between any two rational bases whose integral closures are the two lattices.
This is the determinant form of the common-index cancellation used below the
source-specific Brandt construction. -/
theorem abs_det_eq_one_of_common_relIndex_eq
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K L N : AddSubgroup E) (hKL : K ≤ L) (hKN : K ≤ N)
    (bK bL bN : Module.Basis ι ℚ E)
    (hK : K = .closure (Set.range bK))
    (hL : L = .closure (Set.range bL))
    (hN : N = .closure (Set.range bN))
    (hindex : K.relIndex L = K.relIndex N)
    (hindex_ne : K.relIndex N ≠ 0) :
    |bL.det bN| = 1 := by
  have hleft : ((K.relIndex L : ℕ) : ℚ) = |bL.det bK| :=
    AddSubgroup.relIndex_eq_abs_det K L hKL bK bL hK hL
  have hright : ((K.relIndex N : ℕ) : ℚ) = |bN.det bK| :=
    AddSubgroup.relIndex_eq_abs_det K N hKN bK bN hK hN
  have habs : |bL.det bK| = |bN.det bK| := by
    rw [← hleft, ← hright]
    exact_mod_cast hindex
  have hmul := Module.Basis.det_mul_det bL bN bK
  have habsmul : |bL.det bN| * |bN.det bK| = |bL.det bK| := by
    rw [← abs_mul, hmul]
  have hnonzero : |bN.det bK| ≠ 0 := by
    intro hz
    have hcast : ((K.relIndex N : ℕ) : ℚ) = 0 := by
      rw [hright, hz]
    exact hindex_ne (Nat.cast_eq_zero.mp hcast)
  apply mul_right_cancel₀ hnonzero
  calc
    |bL.det bN| * |bN.det bK| = |bL.det bK| := habsmul
    _ = |bN.det bK| := habs
    _ = 1 * |bN.det bK| := by rw [one_mul]

/-! ## Integral and rational ambient bases -/

/-- Multiplication by `p` lands every integral triple in the source polar
kernel. -/
def occurrencePolarKernelScale (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    IntTriple →+ (occurrencePolarResidueHom hp2 occurrence).ker where
  toFun m := ⟨(p : ℤ) • m, by
    rw [AddMonoidHom.mem_ker, map_zsmul]
    simp⟩
  map_zero' := by ext <;> simp
  map_add' m n := by ext <;> simp

theorem occurrencePolarKernelScale_injective (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Function.Injective (occurrencePolarKernelScale hp2 occurrence) := by
  intro m n h
  have hv := congrArg Subtype.val h
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply Prod.ext
  · have hx := congrArg Prod.fst hv
    simpa using mul_left_cancel₀ hpZ hx
  · apply Prod.ext
    · have hy := congrArg (fun w : IntTriple => w.2.1) hv
      simpa using mul_left_cancel₀ hpZ hy
    · have hz := congrArg (fun w : IntTriple => w.2.2) hv
      simpa using mul_left_cancel₀ hpZ hz

/-- The source polar kernel is itself finite free of rank three. -/
theorem occurrencePolarResidueKernel_finite_free_rank_three (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ∃ b : Module.Basis (Fin 3) ℤ
        (occurrencePolarResidueHom hp2 occurrence).ker.toIntSubmodule,
      Module.finrank ℤ
        (occurrencePolarResidueHom hp2 occurrence).ker.toIntSubmodule = 3 := by
  let K := (occurrencePolarResidueHom hp2 occurrence).ker.toIntSubmodule
  let toInt : K →ₗ[ℤ] IntTriple := K.subtype
  letI : Module.Finite ℤ K :=
    Module.Finite.of_injective toInt K.subtype_injective
  letI : Module.IsTorsionFree ℤ K := by
    constructor
    intro r hr x y hxy
    apply K.subtype_injective
    apply Module.IsTorsionFree.isSMulRegular hr
    simpa only [map_smul] using congrArg toInt hxy
  letI : Module.Free ℤ K := inferInstance
  have hupper : Module.finrank ℤ K ≤ 3 := by
    rw [← intTriple_finrank]
    exact LinearMap.finrank_le_finrank_of_injective K.subtype_injective
  have hlower : 3 ≤ Module.finrank ℤ K := by
    rw [← intTriple_finrank]
    let fromInt := (occurrencePolarKernelScale hp2 occurrence).toIntLinearMap
    exact LinearMap.finrank_le_finrank_of_injective (f := fromInt)
      (occurrencePolarKernelScale_injective hp2 occurrence)
  have hrank : Module.finrank ℤ K = 3 := Nat.le_antisymm hupper hlower
  obtain ⟨n, b⟩ : Σ n : ℕ, Module.Basis (Fin n) ℤ K :=
    Module.basisOfFiniteTypeTorsionFree'
  have hn : n = 3 := by
    have hb := Module.finrank_eq_card_basis b
    simpa [hrank] using hb.symm
  subst n
  exact ⟨b, hrank⟩

/-- A chosen exact integral basis of the source polar kernel. -/
noncomputable def occurrencePolarResidueKernelBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Module.Basis (Fin 3) ℤ
      (occurrencePolarResidueHom hp2 occurrence).ker.toIntSubmodule :=
  Classical.choose
    (occurrencePolarResidueKernel_finite_free_rank_three hp2 occurrence)

/-- The same integral basis after embedding the kernel into the common
rational chart. -/
noncomputable def sourcePolarCoreIntegralBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Module.Basis (Fin 3) ℤ (sourcePolarCore hp2 occurrence).toIntSubmodule := by
  change Module.Basis (Fin 3) ℤ
    (((occurrencePolarResidueHom hp2 occurrence).ker.map
      intTripleInclusion).toIntSubmodule)
  exact (occurrencePolarResidueKernelBasis hp2 occurrence).map
    ((occurrencePolarResidueHom hp2 occurrence).ker.equivMapOfInjective
      intTripleInclusion intTripleInclusion_injective).toIntLinearEquiv

@[simp] theorem sourcePolarCoreIntegralBasis_apply (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    ((sourcePolarCoreIntegralBasis hp2 occurrence i :
        (sourcePolarCore hp2 occurrence).toIntSubmodule) : RatTriple) =
      intTripleInclusion (occurrencePolarResidueKernelBasis hp2 occurrence i) := by
  change (((occurrencePolarResidueHom hp2 occurrence).ker.equivMapOfInjective
    intTripleInclusion intTripleInclusion_injective)
      (occurrencePolarResidueKernelBasis hp2 occurrence i) : RatTriple) = _
  exact AddSubgroup.coe_equivMapOfInjective_apply _ _ _ _

/-- An integral basis generates its ambient additive subgroup exactly. -/
theorem subgroup_eq_closure_range_integralBasis
    (A : AddSubgroup RatTriple) {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ A.toIntSubmodule) :
    A = AddSubgroup.closure
      (Set.range fun i => ((b i : A.toIntSubmodule) : RatTriple)) := by
  change A.toIntSubmodule.toAddSubgroup = _
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  apply congrArg Submodule.toAddSubgroup
  calc
    A.toIntSubmodule = Submodule.map A.toIntSubmodule.subtype ⊤ := by simp
    _ = Submodule.map A.toIntSubmodule.subtype
        (Submodule.span ℤ (Set.range b)) := by rw [b.span_eq]
    _ = Submodule.span ℤ (A.toIntSubmodule.subtype '' Set.range b) :=
      Submodule.map_span _ _
    _ = Submodule.span ℤ
        (Set.range fun i => ((b i : A.toIntSubmodule) : RatTriple)) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, rfl⟩

/-- The standard rational coordinate basis of the common ternary chart. -/
def ratTripleBasis : Module.Basis (Fin 3) ℚ RatTriple :=
  Module.Basis.ofEquivFun
    { toFun := fun m i =>
        Fin.cases m.1 (fun j => Fin.cases m.2.1 (fun _ => m.2.2) j) i
      invFun := fun f => (f 0, f 1, f 2)
      map_add' := by intro m n; funext i; fin_cases i <;> rfl
      map_smul' := by intro a m; funext i; fin_cases i <;> rfl
      left_inv := by intro m; rfl
      right_inv := by intro f; funext i; fin_cases i <;> rfl }

theorem ratTriple_finrank : Module.finrank ℚ RatTriple = 3 := by
  simpa using Module.finrank_eq_card_basis ratTripleBasis

theorem ratTripleBasis_repr_apply (x : RatTriple) (i : Fin 3) :
    ratTripleBasis.repr x i = ratTripleCoordinate i x := by
  let f : Fin 3 → ℚ := fun i =>
    Fin.cases x.1 (fun j => Fin.cases x.2.1 (fun _ => x.2.2) j) i
  have h := (Finsupp.linearEquivFunOnFinite ℚ ℚ (Fin 3)).apply_symm_apply f
  have hi := congrFun h i
  change ((Finsupp.linearEquivFunOnFinite ℚ ℚ (Fin 3)).symm f) i = _
  rw [← Finsupp.linearEquivFunOnFinite_apply ℚ ℚ (Fin 3)]
  exact hi

@[simp] theorem intTripleInclusion_intTripleBasis (i : Fin 3) :
    intTripleInclusion (intTripleBasis i) = ratTripleBasis i := by
  fin_cases i <;>
    simp [intTripleInclusion, intTripleBasis, ratTripleBasis,
      intTripleToRat, Module.Basis.ofEquivFun]

theorem sourcePolarCore_scaled_basis_mem (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    (p : ℚ) • ratTripleBasis i ∈ sourcePolarCore hp2 occurrence := by
  rw [sourcePolarCore, AddSubgroup.mem_map]
  refine ⟨(p : ℤ) • intTripleBasis i, ?_, ?_⟩
  · rw [AddMonoidHom.mem_ker, map_zsmul]
    simp
  · rw [map_zsmul, intTripleInclusion_intTripleBasis]
    apply Prod.ext
    · simp [ratTripleBasis]
    · apply Prod.ext <;> simp [ratTripleBasis]

theorem neighbor_scaled_basis_mem (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    (p : ℚ) • ratTripleBasis i ∈ occurrenceNeighborSubgroup hp2 occurrence := by
  have h := BrandtNeighborOccurrence.scaled_integral_mem hp2 occurrence
    (intTripleBasis i)
  simpa [ratTripleScaleP, intTripleInclusion_intTripleBasis, ratTripleScale] using h

/-- A full-rank integral lattice containing the `p`-scaled coordinate basis
spans the complete rational ambient receiver. -/
theorem rational_span_eq_top_of_scaled_basis_mem
    (A : AddSubgroup RatTriple) (b : Module.Basis (Fin 3) ℤ A.toIntSubmodule)
    (hp : ∀ i : Fin 3, (p : ℚ) • ratTripleBasis i ∈ A) :
    Submodule.span ℚ
      (Set.range fun i => ((b i : A.toIntSubmodule) : RatTriple)) = ⊤ := by
  let V := Submodule.span ℚ
    (Set.range fun i => ((b i : A.toIntSubmodule) : RatTriple))
  have hA_le : A ≤ V.toAddSubgroup := by
    rw [subgroup_eq_closure_range_integralBasis A b]
    apply (AddSubgroup.closure_le V.toAddSubgroup).2
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  apply top_unique
  rw [← ratTripleBasis.span_eq]
  apply Submodule.span_le.2
  rintro x ⟨i, rfl⟩
  have hpi : (p : ℚ) • ratTripleBasis i ∈ V := hA_le (hp i)
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have := V.smul_mem ((p : ℚ)⁻¹) hpi
  simpa [smul_smul, hpQ] using this

/-- Promote a rank-three integral lattice basis to a rational ambient basis
without changing its vectors. -/
noncomputable def rationalBasisOfIntegralBasis
    (A : AddSubgroup RatTriple) (b : Module.Basis (Fin 3) ℤ A.toIntSubmodule)
    (hspan : Submodule.span ℚ
      (Set.range fun i => ((b i : A.toIntSubmodule) : RatTriple)) = ⊤) :
    Module.Basis (Fin 3) ℚ RatTriple :=
  basisOfTopLeSpanOfCardEqFinrank _ (by rw [hspan]) (by simp [ratTriple_finrank])

@[simp] theorem rationalBasisOfIntegralBasis_apply
    (A : AddSubgroup RatTriple) (b : Module.Basis (Fin 3) ℤ A.toIntSubmodule)
    (hspan : Submodule.span ℚ
      (Set.range fun i => ((b i : A.toIntSubmodule) : RatTriple)) = ⊤)
    (i : Fin 3) :
    rationalBasisOfIntegralBasis A b hspan i =
      ((b i : A.toIntSubmodule) : RatTriple) := by
  simp [rationalBasisOfIntegralBasis]

/-- The integral source coordinate lattice is additively equivalent to the
standard integral triple through its exact inclusion. -/
noncomputable def sourceIntegralEquiv : IntTriple ≃+ sourceIntegralLattice := by
  change IntTriple ≃+ ((⊤ : AddSubgroup IntTriple).map intTripleInclusion)
  exact AddSubgroup.topEquiv.symm.trans
    ((⊤ : AddSubgroup IntTriple).equivMapOfInjective
      intTripleInclusion intTripleInclusion_injective)

noncomputable def sourceIntegralBasis :
    Module.Basis (Fin 3) ℤ sourceIntegralLattice.toIntSubmodule :=
  intTripleBasis.map sourceIntegralEquiv.toIntLinearEquiv

@[simp] theorem sourceIntegralBasis_apply (i : Fin 3) :
    ((sourceIntegralBasis i : sourceIntegralLattice.toIntSubmodule) : RatTriple) =
      ratTripleBasis i := by
  change ((sourceIntegralEquiv (intTripleBasis i) :
    sourceIntegralLattice) : RatTriple) = _
  change intTripleInclusion (intTripleBasis i) = _
  exact intTripleInclusion_intTripleBasis i

noncomputable def sourcePolarCoreRationalBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Module.Basis (Fin 3) ℚ RatTriple :=
  rationalBasisOfIntegralBasis (sourcePolarCore hp2 occurrence)
    (sourcePolarCoreIntegralBasis hp2 occurrence)
    (rational_span_eq_top_of_scaled_basis_mem _ _
      (sourcePolarCore_scaled_basis_mem hp2 occurrence))

noncomputable def occurrenceNeighborRationalBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Module.Basis (Fin 3) ℚ RatTriple :=
  rationalBasisOfIntegralBasis (occurrenceNeighborSubgroup hp2 occurrence)
    (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence)
    (rational_span_eq_top_of_scaled_basis_mem _ _
      (neighbor_scaled_basis_mem hp2 occurrence))

@[simp] theorem sourcePolarCoreRationalBasis_apply (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    sourcePolarCoreRationalBasis hp2 occurrence i =
      ((sourcePolarCoreIntegralBasis hp2 occurrence i :
        (sourcePolarCore hp2 occurrence).toIntSubmodule) : RatTriple) := by
  simp [sourcePolarCoreRationalBasis]

@[simp] theorem occurrenceNeighborRationalBasis_apply (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    occurrenceNeighborRationalBasis hp2 occurrence i =
      ((BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence i :
        occurrenceNeighborSubgroup hp2 occurrence) : RatTriple) := by
  exact rationalBasisOfIntegralBasis_apply _ _ _ i

theorem sourceIntegralLattice_closure_ratTripleBasis :
    sourceIntegralLattice = AddSubgroup.closure (Set.range ratTripleBasis) := by
  rw [subgroup_eq_closure_range_integralBasis sourceIntegralLattice
    sourceIntegralBasis]
  congr 2
  funext i
  exact sourceIntegralBasis_apply i

theorem sourcePolarCore_closure_rationalBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    sourcePolarCore hp2 occurrence =
      AddSubgroup.closure (Set.range (sourcePolarCoreRationalBasis hp2 occurrence)) := by
  rw [subgroup_eq_closure_range_integralBasis (sourcePolarCore hp2 occurrence)
    (sourcePolarCoreIntegralBasis hp2 occurrence)]
  congr 2
  funext i
  exact (sourcePolarCoreRationalBasis_apply hp2 occurrence i).symm

theorem occurrenceNeighbor_closure_rationalBasis (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceNeighborSubgroup hp2 occurrence =
      AddSubgroup.closure (Set.range (occurrenceNeighborRationalBasis hp2 occurrence)) := by
  rw [subgroup_eq_closure_range_integralBasis
    (occurrenceNeighborSubgroup hp2 occurrence)
    (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence)]
  congr 2
  funext i
  exact (occurrenceNeighborRationalBasis_apply hp2 occurrence i).symm

/-- The determinant of the promoted actual-neighbor basis is exactly the
determinant of the occurrence coordinate matrix. -/
theorem ratTripleBasis_det_occurrenceNeighbor_eq_coordinate_det (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ratTripleBasis.det (occurrenceNeighborRationalBasis hp2 occurrence) =
      (occurrenceBasisCoordinateMatrix hp2 occurrence).det := by
  rw [Module.Basis.det_apply]
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply]
  simp only [occurrenceNeighborRationalBasis_apply,
    occurrenceBasisCoordinateMatrix]
  rw [occurrenceBasisPoint_eq_rankThreeBasis]
  exact ratTripleBasis_repr_apply _ _

/-- Every actual odd-prime Brandt neighbor has exact absolute covolume one in
the common rational source chart. -/
theorem occurrenceBasisCoordinateMatrix_det_abs_eq_one (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    |(occurrenceBasisCoordinateMatrix hp2 occurrence).det| = 1 := by
  have hcoreIndex :
      (sourcePolarCore hp2 occurrence).relIndex
        (occurrenceNeighborSubgroup hp2 occurrence) = p := by
    rw [← ambientNeighborPolarCore_eq_sourcePolarCore hp2 occurrence]
    exact ambientNeighborPolarCore_relIndex_neighbor hp2 occurrence
  have habs := abs_det_eq_one_of_common_relIndex_eq
    (sourcePolarCore hp2 occurrence) sourceIntegralLattice
    (occurrenceNeighborSubgroup hp2 occurrence)
    (sourcePolarCore_le_sourceIntegralLattice hp2 occurrence)
    (sourcePolarCore_le_neighbor hp2 occurrence)
    (sourcePolarCoreRationalBasis hp2 occurrence) ratTripleBasis
    (occurrenceNeighborRationalBasis hp2 occurrence)
    (sourcePolarCore_closure_rationalBasis hp2 occurrence)
    sourceIntegralLattice_closure_ratTripleBasis
    (occurrenceNeighbor_closure_rationalBasis hp2 occurrence)
    (by rw [sourcePolarCore_relIndex_sourceIntegralLattice hp2 occurrence,
      hcoreIndex])
    (by rw [hcoreIndex]; exact (Fact.out : p.Prime).ne_zero)
  rw [ratTripleBasis_det_occurrenceNeighbor_eq_coordinate_det hp2 occurrence] at habs
  exact habs

theorem occurrenceBasisCoordinateMatrix_det_sq_eq_one (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceBasisCoordinateMatrix hp2 occurrence).det ^ 2 = 1 := by
  have habs := occurrenceBasisCoordinateMatrix_det_abs_eq_one hp2 occurrence
  nlinarith [sq_abs (occurrenceBasisCoordinateMatrix hp2 occurrence).det]

/-- **EVERY ACTUAL ODD-PRIME BRANDT NEIGHBOR HAS FULL-POLAR DETERMINANT
`512`.**  No destination classification is assumed. -/
theorem occurrenceFullGram_det_eq_512 (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceQuotientFullGram hp2 occurrence
      (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
        hp2 occurrence)).det = 512 :=
  occurrenceFullGram_det_of_covolume_sq_one hp2 occurrence
    (occurrenceBasisCoordinateMatrix_det_sq_eq_one hp2 occurrence)

#print axioms fourthResidueKernel_index
#print axioms quotientPolarCore_index
#print axioms neighborPolarCore_index
#print axioms occurrencePolarResidueHom_surjective
#print axioms occurrencePolarResidueKernel_index
#print axioms sourcePolarCore_relIndex_sourceIntegralLattice
#print axioms ambientNeighborPolarCore_relIndex_neighbor
#print axioms ambientNeighborPolarCore_eq_sourcePolarCore
#print axioms abs_det_eq_one_of_common_relIndex_eq
#print axioms occurrencePolarResidueKernel_finite_free_rank_three
#print axioms subgroup_eq_closure_range_integralBasis
#print axioms occurrenceBasisCoordinateMatrix_det_abs_eq_one
#print axioms occurrenceBasisCoordinateMatrix_det_sq_eq_one
#print axioms occurrenceFullGram_det_eq_512

end Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
