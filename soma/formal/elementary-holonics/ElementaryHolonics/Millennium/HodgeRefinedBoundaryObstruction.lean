import ElementaryHolonics.Millennium.HodgeRadialCurrent
import ElementaryHolonics.Millennium.HodgeFiniteCarrier
import ElementaryHolonics.Millennium.HodgeSphereProductRulingProjections
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The refined tetrahedral boundary obstruction

The radial receiver is now point-natural, so a hypothetical singular three-boundary can be
refined without inventing labels on copied occurrences.  Compactness supplies one exact depth at
which every genuinely supported tetrahedron descendant lies in a radius-third star ball.  The
empty fourfold star intersection makes each descendant boundary carry zero, while the same
subdivision carries the explicit radial sphere to the nonzero finite fundamental current.

The resulting contradiction removes the earlier `GeometricBoundaryReturn` construction
hypothesis: the explicit tetrahedral sphere cycle is proved not to be a singular boundary.

Truth status: every theorem is `[proved-derived; formal-checked]` from the finite support
reconstruction, exact barycentric word expansions, the Lebesgue-star aperture, point-current
naturality, and radial edge/face rigidity.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeRefinedBoundaryObstruction

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeFiniteCarrier
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgeBarycentricChainSupport
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedron
open Soma.Holonics.Millennium.HodgePointCarry
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeRadialCurrent
open Soma.Holonics.Millennium.HodgeSphereProductRulingProjections

set_option maxHeartbeats 2000000

/-- [proved-derived; formal-checked] Iterated tetrahedral refinement preserves zero. -/
theorem iteratedBarycentricTetrahedronSubdivision_zero (scale : ℕ) :
    iteratedBarycentricTetrahedronSubdivision scale (0 : SphereChain 3) = 0 := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      change barycentricTetrahedronSubdivisionMorphism
          (iteratedBarycentricTetrahedronSubdivision scale 0) = 0
      rw [inductionHypothesis, map_zero]

/-- [proved-derived; formal-checked] Iterated tetrahedral refinement is additive. -/
theorem iteratedBarycentricTetrahedronSubdivision_add (scale : ℕ)
    (left right : SphereChain 3) :
    iteratedBarycentricTetrahedronSubdivision scale (left + right) =
      iteratedBarycentricTetrahedronSubdivision scale left +
        iteratedBarycentricTetrahedronSubdivision scale right := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      change barycentricTetrahedronSubdivisionMorphism
          (iteratedBarycentricTetrahedronSubdivision scale (left + right)) =
        barycentricTetrahedronSubdivisionMorphism
            (iteratedBarycentricTetrahedronSubdivision scale left) +
          barycentricTetrahedronSubdivisionMorphism
            (iteratedBarycentricTetrahedronSubdivision scale right)
      rw [inductionHypothesis, map_add]

/-- [proved-derived; formal-checked] Iterated tetrahedral refinement preserves rational
coefficients. -/
theorem iteratedBarycentricTetrahedronSubdivision_smul (scale : ℕ)
    (coefficient : ℚ) (chain : SphereChain 3) :
    iteratedBarycentricTetrahedronSubdivision scale (coefficient • chain) =
      coefficient • iteratedBarycentricTetrahedronSubdivision scale chain := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      change barycentricTetrahedronSubdivisionMorphism
          (iteratedBarycentricTetrahedronSubdivision scale (coefficient • chain)) =
        coefficient • barycentricTetrahedronSubdivisionMorphism
          (iteratedBarycentricTetrahedronSubdivision scale chain)
      rw [inductionHypothesis, map_smul]

/-- [proved-derived; formal-checked] Refinement distributes through an actual finite occurrence
population. -/
theorem iteratedBarycentricTetrahedronSubdivision_finset_sum
    {index : Type*} (scale : ℕ) (population : Finset index)
    (chain : index → SphereChain 3) :
    iteratedBarycentricTetrahedronSubdivision scale
        (∑ occurrence ∈ population, chain occurrence) =
      ∑ occurrence ∈ population,
        iteratedBarycentricTetrahedronSubdivision scale (chain occurrence) := by
  classical
  induction population using Finset.induction_on with
  | empty => simp [iteratedBarycentricTetrahedronSubdivision_zero]
  | @insert occurrence population absent inductionHypothesis =>
      rw [Finset.sum_insert absent, Finset.sum_insert absent,
        iteratedBarycentricTetrahedronSubdivision_add, inductionHypothesis]

/-- [proved-derived; formal-checked] Every singular three-chain admits one common exact
refinement depth at which the point current of its complete refined boundary is zero.  The proof
uses only the genuinely nonzero source support and retains every fixed-depth address word. -/
theorem exists_scale_refined_boundary_pointCarry_zero
    (boundaryWitness : SphereChain 3) (lebesgue : StarLebesgueLabel) :
    ∃ scale : ℕ,
      pointCarryMorphism
          (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
            lebesgue) 2
          (SphereSingularChainComplex.d 3 2
            (iteratedBarycentricTetrahedronSubdivision scale boundaryWitness)) = 0 := by
  classical
  obtain ⟨scale, scaleLaw⟩ :=
    exists_scale_boundary_support_words_ball boundaryWitness lebesgue
  refine ⟨scale, ?_⟩
  rw [← sum_support_sphereChainCoefficient_simplexGenerator 3 boundaryWitness]
  rw [iteratedBarycentricTetrahedronSubdivision_finset_sum]
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro simplex simplexInSupport
  rw [iteratedBarycentricTetrahedronSubdivision_smul, map_smul, map_smul]
  rw [tetraWordExpansion, map_sum, map_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro word _
  rw [map_smul, map_smul]
  have small := scaleLaw ⟨simplex, simplexInSupport⟩
    (tetraWordList word) (tetraWordList_length word)
  obtain ⟨center, small⟩ := small
  have admissible := fourLabelsAdmissible_of_range_subset_ball lebesgue
    (tetraWordSubsimplex word simplex) center (by
      simpa only [tetraWordSubsimplex, Equiv.apply_symm_apply] using small)
  rw [pointCarry_boundary_three_eq_zero
    (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
      lebesgue) (tetraWordSubsimplex word simplex) admissible]
  simp

/-- [proved-derived; formal-checked] **THE RADIAL SPHERE IS NOT A SINGULAR BOUNDARY.**  No
geometric-return witness is assumed.  Any alleged bulk witness has a uniform refinement whose
local point current vanishes; boundary naturality identifies that current with the refined radial
sphere current, which is the nonzero tetrahedral fundamental face chain. -/
theorem sphereFundamentalCandidate_not_mem_boundary_range :
    sphereFundamentalCandidate ∉
      Set.range (SphereSingularChainComplex.d 3 2).hom.toAddMonoidHom := by
  rintro ⟨boundaryWitness, boundaryLaw⟩
  obtain ⟨lebesgue⟩ := exists_starLebesgueLabel
  obtain ⟨scale, bulkZero⟩ :=
    exists_scale_refined_boundary_pointCarry_zero boundaryWitness lebesgue
  apply fundamentalFaceChain_ne_zero
  rw [← refinedSphereFundamentalCurrent lebesgue scale]
  rw [← boundaryLaw]
  change pointCarryMorphism
      (Soma.Holonics.Millennium.HodgePointCarry.StarLebesgueLabel.toStarPointLabeling
        lebesgue) 2
      (iteratedBarycentricTriangleSubdivision scale
        (SphereSingularChainComplex.d 3 2 boundaryWitness)) = 0
  rw [← boundary_iteratedBarycentricTetrahedronSubdivision]
  exact bulkZero

/-- [proved-derived; formal-checked] The explicit sphere cycle represents a nonzero genuine
rational singular-homology class.  This is the exact quotient consequence of the nonboundary
theorem, not an assumed detector. -/
theorem sphereFundamentalHomologyClass_ne_zero :
    sphereFundamentalHomologyClass ≠ 0 := by
  intro homologyZero
  let quotientComplex : ShortComplex (ModuleCat ℚ) :=
    ShortComplex.mk
      (SphereSingularChainComplex.toCycles 3 2)
      (SphereSingularChainComplex.homologyπ 2)
      (SphereSingularChainComplex.toCycles_comp_homologyπ 3 2)
  have quotientExact : quotientComplex.Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    exact SphereSingularChainComplex.homologyIsCokernel 3 2 (by simp)
  have cycleZero :
      SphereSingularChainComplex.homologyπ 2 (sphereCycleLift 1) = 0 := by
    exact homologyZero
  obtain ⟨boundaryWitness, boundaryLaw⟩ :=
    (ShortComplex.moduleCat_exact_iff quotientComplex).mp quotientExact
      (sphereCycleLift 1) cycleZero
  apply sphereFundamentalCandidate_not_mem_boundary_range
  refine ⟨boundaryWitness, ?_⟩
  calc
    SphereSingularChainComplex.d 3 2 boundaryWitness =
        SphereSingularChainComplex.iCycles 2
          (SphereSingularChainComplex.toCycles 3 2 boundaryWitness) := by
      change (SphereSingularChainComplex.d 3 2) boundaryWitness =
        (SphereSingularChainComplex.toCycles 3 2 ≫
          SphereSingularChainComplex.iCycles 2) boundaryWitness
      rw [SphereSingularChainComplex.toCycles_i]
    _ = SphereSingularChainComplex.iCycles 2 (sphereCycleLift 1) := by
      exact congrArg (fun cycle => SphereSingularChainComplex.iCycles 2 cycle) boundaryLaw
    _ = sphereFundamentalCandidate := by
      change (sphereCycleLift ≫ SphereSingularChainComplex.iCycles 2) 1 =
        sphereFundamentalCandidate
      rw [sphereCycleLift_i]
      exact LinearMap.toSpanSingleton_apply_one ℚ _ sphereFundamentalCandidate

/-- [proved-derived; formal-checked] The finite tetrahedral top class embeds into genuine
rational singular homology without a supplied detector or retraction. -/
theorem tetrahedralHomologyRealization_injective :
    Function.Injective tetrahedralHomologyRealization :=
  tetrahedralHomologyRealization_injective_iff.mpr
    sphereFundamentalHomologyClass_ne_zero

/-- [proved-derived; formal-checked] The two geometric ruling classes in the sphere product
are linearly independent in genuine rational singular homology. -/
theorem rulingHomologyMap_injective :
    Function.Injective
      Soma.Holonics.Millennium.HodgeSphereProductRulingHomology.rulingHomologyMap :=
  rulingHomologyMap_injective_of_fundamentalClass_ne_zero
    sphereFundamentalHomologyClass_ne_zero

section Audit

#print axioms exists_scale_refined_boundary_pointCarry_zero
#print axioms sphereFundamentalCandidate_not_mem_boundary_range
#print axioms sphereFundamentalHomologyClass_ne_zero
#print axioms tetrahedralHomologyRealization_injective
#print axioms rulingHomologyMap_injective

end Audit

end Soma.Holonics.Millennium.HodgeRefinedBoundaryObstruction
