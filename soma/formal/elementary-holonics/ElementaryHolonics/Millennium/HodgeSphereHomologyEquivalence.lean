import ElementaryHolonics.Millennium.HodgeCommonStarNormalization
import ElementaryHolonics.Millennium.HodgeRefinedBoundaryObstruction

/-!
# Rational degree-two homology of the sphere from the common-star reduction

The common-star current now supplies the missing surjectivity half of the tetrahedral realization.
Together with the independently proved radial nonboundary theorem, this identifies every genuine
rational singular-homology class on `S²` with one finite tetrahedral top cycle.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSphereHomologyEquivalence

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgeCommonStarNormalization
open Soma.Holonics.Millennium.HodgeRefinedBoundaryObstruction
open Soma.Holonics.Millennium.HodgeSphereProductRulingProjections

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-- [proved-derived; formal-checked] Every addressed sphere two-cycle represents the same homology
class as a finite tetrahedral top cycle. -/
theorem cycle_homology_eq_tetrahedral_realization
    (lebesgue : StarLebesgueLabel)
    (cycle : SphereSingularChainComplex.cycles 2) :
    ∃ finiteCycle : (tetrahedralH2Module : Type),
      SphereSingularChainComplex.homologyπ 2 cycle =
        tetrahedralHomologyRealization finiteCycle := by
  let chain : SphereChain 2 := SphereSingularChainComplex.iCycles 2 cycle
  have chainClosed : SphereSingularChainComplex.d 2 1 chain = 0 := by
    change (SphereSingularChainComplex.iCycles 2 ≫
      SphereSingularChainComplex.d 2 1) cycle = 0
    rw [SphereSingularChainComplex.iCycles_d]
    rfl
  obtain ⟨current, coefficient, boundaryLaw⟩ :=
    exists_commonStarReduction_to_fundamental chain lebesgue chainClosed
  let moduleFundamental : (tetrahedralH2Module : Type) := fundamentalClass
  let finiteCycle : (tetrahedralH2Module : Type) := coefficient • moduleFundamental
  let targetCycle : SphereSingularChainComplex.cycles 2 :=
    tetrahedralCycleLift finiteCycle
  have targetInclusion :
      SphereSingularChainComplex.iCycles 2 targetCycle =
        coefficient • sphereFundamentalCandidate := by
    change (tetrahedralCycleLift ≫ SphereSingularChainComplex.iCycles 2)
        finiteCycle = coefficient • sphereFundamentalCandidate
    rw [tetrahedralCycleLift_i]
    rw [show finiteCycle = coefficient • moduleFundamental by rfl, map_smul]
    have fundamentalLaw : tetrahedralCycleMorphism moduleFundamental =
        sphereFundamentalCandidate := tetrahedralCycleMorphism_fundamental
    rw [fundamentalLaw]
  have differenceIsBoundary :
      cycle - targetCycle =
        SphereSingularChainComplex.toCycles 3 2 (-current) := by
    apply (ModuleCat.mono_iff_injective
      (SphereSingularChainComplex.iCycles 2)).mp inferInstance
    rw [map_sub]
    change chain -
        SphereSingularChainComplex.iCycles 2 targetCycle =
      SphereSingularChainComplex.iCycles 2
        (SphereSingularChainComplex.toCycles 3 2 (-current))
    rw [targetInclusion]
    change chain - coefficient • sphereFundamentalCandidate =
      (SphereSingularChainComplex.toCycles 3 2 ≫
        SphereSingularChainComplex.iCycles 2) (-current)
    rw [SphereSingularChainComplex.toCycles_i, map_neg, boundaryLaw]
    module
  have differenceVanishes :
      SphereSingularChainComplex.homologyπ 2 (cycle - targetCycle) = 0 := by
    rw [differenceIsBoundary]
    change (SphereSingularChainComplex.toCycles 3 2 ≫
      SphereSingularChainComplex.homologyπ 2) (-current) = 0
    rw [SphereSingularChainComplex.toCycles_comp_homologyπ]
    rfl
  have sameClass :
      SphereSingularChainComplex.homologyπ 2 cycle =
        SphereSingularChainComplex.homologyπ 2 targetCycle := by
    rw [map_sub, sub_eq_zero] at differenceVanishes
    exact differenceVanishes
  refine ⟨finiteCycle, ?_⟩
  change SphereSingularChainComplex.homologyπ 2 cycle =
    (tetrahedralCycleLift ≫ SphereSingularChainComplex.homologyπ 2) finiteCycle
  exact sameClass

/-- [proved-derived; formal-checked] The finite tetrahedral realization is onto genuine rational
singular homology in degree two. -/
theorem tetrahedralHomologyRealization_surjective :
    Function.Surjective tetrahedralHomologyRealization := by
  obtain ⟨lebesgue⟩ := exists_starLebesgueLabel
  intro homologyClass
  obtain ⟨cycle, cycleClass⟩ :=
    (ModuleCat.epi_iff_surjective
      (SphereSingularChainComplex.homologyπ 2)).mp inferInstance homologyClass
  obtain ⟨finiteCycle, finiteClass⟩ :=
    cycle_homology_eq_tetrahedral_realization lebesgue cycle
  exact ⟨finiteCycle, finiteClass.symm.trans cycleClass⟩

/-- [proved-derived; formal-checked] The tetrahedral top-cycle module is exactly rational sphere
homology in degree two. -/
def tetrahedralHomologyRealizationEquiv :
    TetrahedralH2 ≃ₗ[ℚ] RationalSingularHomology 2 sphereTopCat :=
  LinearEquiv.ofBijective tetrahedralHomologyRealization.hom
    ⟨tetrahedralHomologyRealization_injective,
      tetrahedralHomologyRealization_surjective⟩

/-- [proved-derived; formal-checked] Genuine rational singular `H₂` of the addressed sphere,
with its tetrahedral realization and reconstruction retained by the composed equivalence, is one
exact rational coordinate line. -/
def sphereH2EquivQ :
    RationalSingularHomology 2 sphereTopCat ≃ₗ[ℚ] ℚ :=
  tetrahedralHomologyRealizationEquiv.symm.trans tetrahedralH2EquivQ

/-- [proved-derived; formal-checked] The geometric fundamental cycle is the unit occurrence in
the exact rational coordinate chart. -/
theorem sphereH2EquivQ_fundamental :
    sphereH2EquivQ sphereFundamentalHomologyClass = 1 := by
  rw [← realizedFundamentalClass_eq_sphereFundamentalHomologyClass]
  change tetrahedralH2EquivQ
    (tetrahedralHomologyRealizationEquiv.symm
      (tetrahedralHomologyRealizationEquiv fundamentalClass)) = 1
  rw [tetrahedralHomologyRealizationEquiv.symm_apply_apply]
  rfl

section Audit

#print axioms cycle_homology_eq_tetrahedral_realization
#print axioms tetrahedralHomologyRealization_surjective
#print axioms tetrahedralHomologyRealizationEquiv
#print axioms sphereH2EquivQ
#print axioms sphereH2EquivQ_fundamental

end Audit

end Soma.Holonics.Millennium.HodgeSphereHomologyEquivalence
