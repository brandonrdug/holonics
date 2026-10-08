import HolonicsResearch.Hodge.HodgeSphereProductFourCycle

/-!
# The actual normalized sphere coefficient

[agent-inferred] This is one mathematical owner moved from HodgeProductDiagonal.
Its declarations occur once with unchanged bodies, statements and scope; the
next complete owner consumes its checked maps. No partial-source acceptance
is used for the public nonboundary consumer.
-/

noncomputable section

namespace Holonics.Hodge.HodgeProductDiagonal

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Holonics.DiagonalChainTransport
open Holonics.Hodge.HodgeProjectiveLineSingularReduction
open Holonics.Hodge.HodgeSphereProductFiniteComplex
open Holonics.Hodge.HodgeTwoSphereFundamentalCycle
open Holonics.Hodge.HodgeSphereProductRulingProjections
open Holonics.Hodge.HodgeSphereHomologyEquivalence
open Holonics.Hodge.HodgeSphereFundamentalDetector

universe u

/-- [agent-inferred] Extend the *proved actual* sphere homology coordinate to all two-chains by
a rational linear retraction of cycle inclusion. Choice occurs only outside the cycles; the
boundary and fundamental values below are forced by the existing equivalence. -/
def sphereRawCoefficient : SphereSingularChainComplex.X 2 →ₗ[ℚ] ℚ :=
  sphereH2EquivQ.toLinearMap.comp
    ((SphereSingularChainComplex.homologyπ 2).hom.comp
      (SphereSingularChainComplex.iCycles 2).hom.leftInverse)

theorem sphereRawCoefficient_cycle (cycle : SphereSingularChainComplex.cycles 2) :
    sphereRawCoefficient (SphereSingularChainComplex.iCycles 2 cycle) =
      sphereH2EquivQ (SphereSingularChainComplex.homologyπ 2 cycle) := by
  have injective : LinearMap.ker (SphereSingularChainComplex.iCycles 2).hom = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      ((ModuleCat.mono_iff_injective (SphereSingularChainComplex.iCycles 2)).mp inferInstance)
  change sphereH2EquivQ
      ((SphereSingularChainComplex.homologyπ 2).hom
        ((SphereSingularChainComplex.iCycles 2).hom.leftInverse
          ((SphereSingularChainComplex.iCycles 2).hom cycle))) =
    sphereH2EquivQ ((SphereSingularChainComplex.homologyπ 2).hom cycle)
  rw [LinearMap.leftInverse_apply_of_inj injective]

theorem sphereRawCoefficient_boundary (chain : SphereSingularChainComplex.X 3) :
    sphereRawCoefficient (SphereSingularChainComplex.d 3 2 chain) = 0 := by
  have inclusion : SphereSingularChainComplex.iCycles 2
      (SphereSingularChainComplex.toCycles 3 2 chain) =
      SphereSingularChainComplex.d 3 2 chain := by
    change (SphereSingularChainComplex.toCycles 3 2 ≫
      SphereSingularChainComplex.iCycles 2) chain = _
    rw [SphereSingularChainComplex.toCycles_i]
  rw [← inclusion, sphereRawCoefficient_cycle]
  change sphereH2EquivQ ((SphereSingularChainComplex.toCycles 3 2 ≫
    SphereSingularChainComplex.homologyπ 2) chain) = 0
  rw [SphereSingularChainComplex.toCycles_comp_homologyπ]
  exact map_zero sphereH2EquivQ

theorem sphereRawCoefficient_fundamental :
    sphereRawCoefficient sphereFundamentalCandidate = 1 := by
  have included : SphereSingularChainComplex.iCycles 2 (sphereCycleLift 1) =
      sphereFundamentalCandidate := by
    change (sphereCycleLift ≫ SphereSingularChainComplex.iCycles 2) 1 = _
    rw [sphereCycleLift_i]
    change (1 : ℚ) • sphereFundamentalCandidate = sphereFundamentalCandidate
    exact one_smul ℚ _
  rw [← included, sphereRawCoefficient_cycle]
  exact sphereH2EquivQ_fundamental

/-- The existing detector contract is now inhabited from the actual homology theorem. -/
def sphereDetectorFromHomology : SphereDegreeTwoDetector where
  receive := ModuleCat.ofHom sphereRawCoefficient
  boundary_zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact sphereRawCoefficient_boundary
  fundamental_value := sphereRawCoefficient_fundamental

def sphereRawSimplexCoefficient (simplex : Simplex SphereSSet 2) : ℚ :=
  sphereRawCoefficient (topologicalSimplexGenerator sphereTopCat simplex)

theorem sphereRawSimplexCoefficient_closed (simplex : Simplex SphereSSet 3) :
    sphereRawSimplexCoefficient (face 0 simplex) -
      sphereRawSimplexCoefficient (face 1 simplex) +
        sphereRawSimplexCoefficient (face 2 simplex) -
          sphereRawSimplexCoefficient (face 3 simplex) = 0 := by
  have law := sphereRawCoefficient_boundary
    (topologicalSimplexGenerator sphereTopCat simplex)
  rw [boundary_topologicalSimplexGenerator] at law
  simp only [map_sum, map_smul] at law
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, smul_eq_mul, add_zero, zero_add] at law
  have faceThreeIndex : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, faceThreeIndex] at law
  simp only [sphereRawSimplexCoefficient, topologicalSimplexFace, face]
  simp only [topologicalSimplexFace, face] at law
  convert law using 1 <;> ring

def sphereNormalizedSimplexCoefficient : Simplex SphereSSet 2 → ℚ :=
  normalizedTwoCoefficient sphereRawSimplexCoefficient

def sphereNormalizedCurrentCoefficient : FactorCurrent SphereSSet 2 →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ sphereNormalizedSimplexCoefficient

def sphereCorrectionCurrentCoefficient : FactorCurrent SphereSSet 1 →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (twoCoefficientCorrection sphereRawSimplexCoefficient)

/-- The normalization carries its exact coboundary return. It agrees with the raw homology
coordinate on every closed current, rather than merely on the four fundamental faces. -/
theorem sphereNormalizedCurrentCoefficient_return (current : FactorCurrent SphereSSet 2) :
    sphereNormalizedCurrentCoefficient current =
      sphereRawCoefficient (topologicalCurrentToChain sphereTopCat 2 current) -
        sphereCorrectionCurrentCoefficient (factorBoundary SphereSSet 1 current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]; ring
  | single simplex coefficient =>
      have generatorLaw :
          sphereNormalizedCurrentCoefficient (generator simplex) =
            sphereRawCoefficient
                (topologicalCurrentToChain sphereTopCat 2 (generator simplex)) -
              sphereCorrectionCurrentCoefficient
                (factorBoundary SphereSSet 1 (generator simplex)) := by
        rw [topologicalCurrentToChain_generator, factorBoundary_generator]
        simp [sphereNormalizedCurrentCoefficient, sphereNormalizedSimplexCoefficient,
          normalizedTwoCoefficient, sphereCorrectionCurrentCoefficient,
          sphereRawSimplexCoefficient, factorBoundaryAtom, Fin.sum_univ_three,
          generator] <;> ring
      rw [show Finsupp.single simplex coefficient =
        coefficient • generator simplex by simp [generator]]
      simpa only [map_smul, smul_sub] using
        congrArg (coefficient • ·) generatorLaw

theorem sphereNormalizedCurrentCoefficient_boundary
    (current : FactorCurrent SphereSSet 3) :
    sphereNormalizedCurrentCoefficient (factorBoundary SphereSSet 2 current) = 0 := by
  rw [sphereNormalizedCurrentCoefficient_return,
    topologicalCurrentToChain_boundary, sphereRawCoefficient_boundary,
    topologicalFactorBoundary_sq, map_zero, sub_self]

theorem sphereNormalizedSimplexCoefficient_closed (simplex : Simplex SphereSSet 3) :
    sphereNormalizedSimplexCoefficient (face 0 simplex) -
      sphereNormalizedSimplexCoefficient (face 1 simplex) +
        sphereNormalizedSimplexCoefficient (face 2 simplex) -
          sphereNormalizedSimplexCoefficient (face 3 simplex) = 0 := by
  have law := sphereNormalizedCurrentCoefficient_boundary (generator simplex)
  rw [factorBoundary_generator] at law
  simp only [factorBoundaryAtom, map_sum, map_smul] at law
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, sphereNormalizedCurrentCoefficient, generator,
    Finsupp.linearCombination_single, smul_eq_mul, add_zero, zero_add] at law
  have faceThreeIndex : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, faceThreeIndex] at law
  convert law using 1 <;> ring

theorem sphereNormalizedSimplexCoefficient_degenerate (i : Fin 2)
    (edge : Simplex SphereSSet 1) :
    sphereNormalizedSimplexCoefficient (SphereSSet.σ i edge) = 0 :=
  normalizedTwoCoefficient_degenerate_zero sphereRawSimplexCoefficient
    sphereRawSimplexCoefficient_closed i edge

theorem sphereNormalizedCurrentCoefficient_fundamental :
    sphereNormalizedCurrentCoefficient
      (topologicalChainEquivCurrent sphereTopCat 2 sphereFundamentalCandidate) = 1 := by
  rw [sphereNormalizedCurrentCoefficient_return]
  change sphereRawCoefficient (topologicalCurrentToChain sphereTopCat 2
      (topologicalChainToCurrent sphereTopCat 2 sphereFundamentalCandidate)) -
    sphereCorrectionCurrentCoefficient (factorBoundary SphereSSet 1
      (topologicalChainEquivCurrent sphereTopCat 2 sphereFundamentalCandidate)) = 1
  rw [topologicalCurrent_chain_roundtrip, ← topologicalChainEquivCurrent_boundary,
    sphereFundamentalCandidate_boundary_zero, map_zero, map_zero, sub_zero,
    sphereRawCoefficient_fundamental]

/-- The full bilinear source population, not only one pair of source simplices, returns the
product of the two actual normalized factor readings. -/
theorem pairFourReceiver_pairTwoShuffle_pairCurrent
    (left : FactorCurrent SphereSSet 2) (right : FactorCurrent SphereSSet 2) :
    pairFourReceiver sphereNormalizedSimplexCoefficient sphereNormalizedSimplexCoefficient
      (pairTwoShuffle SphereSSet SphereSSet (pairCurrent left right)) =
        sphereNormalizedCurrentCoefficient left * sphereNormalizedCurrentCoefficient right := by
  induction left using Finsupp.induction_linear with
  | zero => simp [pairCurrent_zero_left]
  | add a b ha hb => simp only [pairCurrent_add_left, map_add, ha, hb]; ring
  | single x a =>
      induction right using Finsupp.induction_linear with
      | zero => simp [pairCurrent_zero_right]
      | add b c hb hc => simp only [pairCurrent_add_right, map_add, hb, hc]; ring
      | single y b =>
          rw [show Finsupp.single x a = a • generator x by simp [generator],
            show Finsupp.single y b = b • generator y by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right,
            pairCurrent_generator, map_smul, pairTwoShuffle, extend_generator]
          rw [pairFourReceiver_pairTwoShuffleAtom _ _
            sphereNormalizedSimplexCoefficient_degenerate]
          simp [sphereNormalizedCurrentCoefficient, generator, smul_eq_mul] <;> ring

section Audit

#print axioms sphereRawCoefficient_cycle
#print axioms sphereRawCoefficient_boundary
#print axioms sphereRawCoefficient_fundamental
#print axioms sphereRawSimplexCoefficient_closed
#print axioms sphereNormalizedCurrentCoefficient_return
#print axioms sphereNormalizedCurrentCoefficient_boundary
#print axioms sphereNormalizedSimplexCoefficient_closed
#print axioms sphereNormalizedSimplexCoefficient_degenerate
#print axioms sphereNormalizedCurrentCoefficient_fundamental
#print axioms pairFourReceiver_pairTwoShuffle_pairCurrent

end Audit

end Holonics.Hodge.HodgeProductDiagonal
