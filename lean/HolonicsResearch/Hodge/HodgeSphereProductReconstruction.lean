import HolonicsResearch.Hodge.HodgeSphereProductCurrent

/-!
# Sphere-product separation and reconstruction

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

/-- [proved-derived; formal-checked] The actual singular boundary of one product triangle becomes
the componentwise diagonal boundary with no lost simplex occurrence. -/
theorem productChainDiagonalEquiv_boundary_generator (simplex : ProductSimplex 2) :
    productChainDiagonalEquiv 1
        (SphereProductSingularChainComplex.d 2 1 (productSimplexGenerator simplex)) =
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 (productSimplexGenerator simplex)) := by
  rw [boundary_productSimplexGenerator, map_sum]
  simp_rw [map_smul, productChainDiagonalEquiv_generator]
  change _ = extend diagonalBoundaryTwoAtom (generator (splitProductSimplex simplex))
  rw [extend_generator]
  change (∑ omitted : Fin 3, (-1 : ℚ) ^ (omitted : ℕ) •
      generator (splitProductSimplex (productSimplexFace omitted simplex))) =
    diagonalBoundaryTwoAtom (splitProductSimplex simplex)
  simp_rw [splitProductSimplex_face]
  rw [Fin.sum_univ_three]
  norm_num [diagonalBoundaryTwoAtom]
  module

/-- [proved-derived; formal-checked] The genuine singular boundary of one product tetrahedron
becomes the four-face diagonal boundary with every source occurrence retained. -/
theorem productChainDiagonalEquiv_boundary_three_generator
    (simplex : ProductSimplex 3) :
    productChainDiagonalEquiv 2
        (SphereProductSingularChainComplex.d 3 2 (productSimplexGenerator simplex)) =
      diagonalBoundaryThree SphereSSet SphereSSet
        (productChainDiagonalEquiv 3 (productSimplexGenerator simplex)) := by
  rw [boundary_productSimplexGenerator, map_sum]
  simp_rw [map_smul, productChainDiagonalEquiv_generator]
  change _ = extend diagonalBoundaryThreeAtom (generator (splitProductSimplex simplex))
  rw [extend_generator]
  change (∑ omitted : Fin 4, (-1 : ℚ) ^ (omitted : ℕ) •
      generator (splitProductSimplex (productSimplexFace omitted simplex))) =
    diagonalBoundaryThreeAtom (splitProductSimplex simplex)
  simp_rw [splitProductSimplex_face]
  rw [Fin.sum_univ_four]
  norm_num [diagonalBoundaryThreeAtom]
  module

/-- [proved-derived; formal-checked] The genuine singular boundary square commutes on every
rational product two-chain.  Thus the generic diagonal separation holon is now attached to the
actual `S² × S²` source rather than to an isolated word fixture. -/
theorem productChainDiagonalEquiv_boundary (chain : ProductChain 2) :
    productChainDiagonalEquiv 1 (SphereProductSingularChainComplex.d 2 1 chain) =
      diagonalBoundaryTwo SphereSSet SphereSSet (productChainDiagonalEquiv 2 chain) := by
  let left : SphereProductSingularChainComplex.X 2 ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet 1)) :=
    SphereProductSingularChainComplex.d 2 1 ≫
      productChainDiagonalMorphism 1
  let right : SphereProductSingularChainComplex.X 2 ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet 1)) :=
    separatedBoundaryAfterDiagonalMorphism
  have mapsEqual : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    simp only [left, right]
    change productChainDiagonalEquiv 1
        (SphereProductSingularChainComplex.d 2 1
          ((Limits.Sigma.ι
            (fun _ : ProductSimplex 2 => rationalCoefficient) simplex) coefficient)) =
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2
          ((Limits.Sigma.ι
            (fun _ : ProductSimplex 2 => rationalCoefficient) simplex) coefficient))
    rw [sigmaInjection_eq_smul_productGenerator]
    simp only [map_smul]
    exact congrArg (coefficient • ·)
      (productChainDiagonalEquiv_boundary_generator simplex)
  exact congrArg (fun morphism => morphism chain) mapsEqual

/-- [proved-derived; formal-checked] The genuine degree-three singular boundary square commutes on
every rational product chain. -/
theorem productChainDiagonalEquiv_boundary_three (chain : ProductChain 3) :
    productChainDiagonalEquiv 2 (SphereProductSingularChainComplex.d 3 2 chain) =
      diagonalBoundaryThree SphereSSet SphereSSet (productChainDiagonalEquiv 3 chain) := by
  let left : SphereProductSingularChainComplex.X 3 ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet 2)) :=
    SphereProductSingularChainComplex.d 3 2 ≫ productChainDiagonalMorphism 2
  let right : SphereProductSingularChainComplex.X 3 ⟶
      ModuleCat.of ℚ (Current (DiagonalOccurrence SphereSSet SphereSSet 2)) :=
    ModuleCat.ofHom ((diagonalBoundaryThree SphereSSet SphereSSet).comp
      (productChainDiagonalEquiv 3).toLinearMap)
  have mapsEqual : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    simp only [left, right]
    change productChainDiagonalEquiv 2
        (SphereProductSingularChainComplex.d 3 2
          ((Limits.Sigma.ι
            (fun _ : ProductSimplex 3 => rationalCoefficient) simplex) coefficient)) =
      diagonalBoundaryThree SphereSSet SphereSSet
        (productChainDiagonalEquiv 3
          ((Limits.Sigma.ι
            (fun _ : ProductSimplex 3 => rationalCoefficient) simplex) coefficient))
    rw [sigmaInjection_eq_smul_productGenerator]
    simp only [map_smul]
    exact congrArg (coefficient • ·)
      (productChainDiagonalEquiv_boundary_three_generator simplex)
  exact congrArg (fun morphism => morphism chain) mapsEqual

/-- The four-axis Alexander--Whitney current of one genuine product three-chain. -/
def separatedProductThreeChain (chain : ProductChain 3) :
    Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  separateThree SphereSSet SphereSSet (productChainDiagonalEquiv 3 chain)

/-- [proved-derived; formal-checked] The boundary of a genuine product three-chain separates as
an actual four-axis boundary.  This closes the boundary-compatibility half of the product
degree-two homology passage; the remaining reduction concerns the homology of the separated
axes, not whether source boundaries survive the receiver. -/
theorem separatedProductThreeChain_boundary (chain : ProductChain 3) :
    totalBoundaryThree SphereSSet SphereSSet (separatedProductThreeChain chain) =
      separateTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2
          (SphereProductSingularChainComplex.d 3 2 chain)) := by
  have law := LinearMap.congr_fun
    (boundary_separateThree SphereSSet SphereSSet)
    (productChainDiagonalEquiv 3 chain)
  change totalBoundaryThree SphereSSet SphereSSet
      (separateThree SphereSSet SphereSSet
        (productChainDiagonalEquiv 3 chain)) =
    separateTwo SphereSSet SphereSSet
      (diagonalBoundaryThree SphereSSet SphereSSet
        (productChainDiagonalEquiv 3 chain)) at law
  rw [← productChainDiagonalEquiv_boundary_three] at law
  exact law

/-- [proved-derived; formal-checked] Product boundary separation as one elementary boundary
holon.  Every source tetrahedral occurrence returns all four separated axes, and the receiver
retains the exact degree-two source boundary rather than only its vanishing homology class. -/
def productBoundarySeparationHolon :
    Holonics.BoundaryHolon
      (Current (TotalTwoOccurrence SphereSSet SphereSSet))
      (Current (TotalThreeOccurrence SphereSSet SphereSSet)) where
  Occurrence := ProductChain 3
  source _ := 0
  target chain :=
    separateTwo SphereSSet SphereSSet
      (productChainDiagonalEquiv 2
        (SphereProductSingularChainComplex.d 3 2 chain))
  receive := separatedProductThreeChain
  boundary := (totalBoundaryThree SphereSSet SphereSSet).toAddMonoidHom
  returnsBoundary := by
    intro chain
    change totalBoundaryThree SphereSSet SphereSSet
        (separatedProductThreeChain chain) =
      separateTwo SphereSSet SphereSSet
          (productChainDiagonalEquiv 2
            (SphereProductSingularChainComplex.d 3 2 chain)) - 0
    simpa using separatedProductThreeChain_boundary chain

/-- Genuine closed product two-currents, retaining the categorical singular-chain occurrence. -/
abbrev ProductTwoCycle :=
  LinearMap.ker (SphereProductSingularChainComplex.d 2 1).hom

/-- The complete separated `0×2 + 1×1 + 2×0` current of a genuine product cycle. -/
def separatedProductCycle (cycle : ProductTwoCycle) :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  separateTwo SphereSSet SphereSSet (productChainDiagonalEquiv 2 cycle.1)

theorem separatedProductCycle_boundary (cycle : ProductTwoCycle) :
    totalBoundaryTwo SphereSSet SphereSSet (separatedProductCycle cycle) = 0 := by
  have diagonalClosed :
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1) = 0 := by
    rw [← productChainDiagonalEquiv_boundary, cycle.2, map_zero]
  have transportLaw := LinearMap.congr_fun
    (boundary_separateTwo SphereSSet SphereSSet)
    (productChainDiagonalEquiv 2 cycle.1)
  simp only [LinearMap.comp_apply, diagonalClosed, map_zero] at transportLaw
  exact transportLaw

/-- [proved-derived; formal-checked] Genuine closed sphere-product currents instantiate the
generic diagonal separation boundary holon.  Its receiver keeps all three axes and its
reconstruction fibre keeps the originating singular cycle. -/
def productCycleSeparationHolon :
    Holonics.BoundaryHolon
      (Current (TotalOneOccurrence SphereSSet SphereSSet))
      (Current (TotalTwoOccurrence SphereSSet SphereSSet)) where
  Occurrence := ProductTwoCycle
  source _ := 0
  target _ := 0
  receive := separatedProductCycle
  boundary := (totalBoundaryTwo SphereSSet SphereSSet).toAddMonoidHom
  returnsBoundary := by
    intro cycle
    change totalBoundaryTwo SphereSSet SphereSSet (separatedProductCycle cycle) = 0 - 0
    simpa using separatedProductCycle_boundary cycle

/-- Reconstruct a genuine singular product chain from a separated three-axis current. -/
def rejoinedProductChain
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) : ProductChain 2 :=
  (productChainDiagonalEquiv 2).symm
    (rejoinTwo SphereSSet SphereSSet current)

/-- Reconstruct a genuine singular product three-chain from all four separated axes.  The two
interior axes retain their complete three-shuffle populations. -/
def rejoinedProductThreeChain
    (current : Current (TotalThreeOccurrence SphereSSet SphereSSet)) : ProductChain 3 :=
  (productChainDiagonalEquiv 3).symm
    (rejoinThree SphereSSet SphereSSet current)

/-- [proved-derived; formal-checked] The boundary of the four-axis reconstruction is the genuine
product-chain reconstruction of the separated boundary.  Consequently every filler constructed
in the separated total complex returns an actual singular boundary in `S² × S²`. -/
theorem rejoinedProductThreeChain_boundary
    (current : Current (TotalThreeOccurrence SphereSSet SphereSSet)) :
    SphereProductSingularChainComplex.d 3 2 (rejoinedProductThreeChain current) =
      rejoinedProductChain
        (totalBoundaryThree SphereSSet SphereSSet current) := by
  apply (productChainDiagonalEquiv 2).injective
  rw [productChainDiagonalEquiv_boundary_three,
    rejoinedProductThreeChain, LinearEquiv.apply_symm_apply]
  change diagonalBoundaryThree SphereSSet SphereSSet
      (rejoinThree SphereSSet SphereSSet current) =
    productChainDiagonalEquiv 2
      ((productChainDiagonalEquiv 2).symm
        (rejoinTwo SphereSSet SphereSSet
          (totalBoundaryThree SphereSSet SphereSSet current)))
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun
    (boundary_rejoinThree SphereSSet SphereSSet) current

/-- [proved-derived; formal-checked] A separated degree-two boundary rejoins to a genuine product
singular boundary, with the complete degree-three occurrence population as reconstruction fibre. -/
theorem rejoinedProductChain_of_separatedBoundary
    (current : Current (TotalThreeOccurrence SphereSSet SphereSSet)) :
    rejoinedProductChain (totalBoundaryThree SphereSSet SphereSSet current) =
      SphereProductSingularChainComplex.d 3 2
        (rejoinedProductThreeChain current) :=
  (rejoinedProductThreeChain_boundary current).symm

/-- [proved-derived; formal-checked] The boundary of the reconstructed genuine chain is exactly
the rejoined boundary of the separated current, viewed in the diagonal chart. -/
theorem productChainDiagonalEquiv_boundary_rejoined
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) :
    productChainDiagonalEquiv 1
        (SphereProductSingularChainComplex.d 2 1 (rejoinedProductChain current)) =
      rejoinOne SphereSSet SphereSSet
        (totalBoundaryTwo SphereSSet SphereSSet current) := by
  rw [productChainDiagonalEquiv_boundary]
  rw [rejoinedProductChain, LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (boundary_rejoinTwo SphereSSet SphereSSet) current

/-- A closed separated product current. -/
abbrev ClosedSeparatedProductCurrent :=
  LinearMap.ker (totalBoundaryTwo SphereSSet SphereSSet)

theorem rejoinedProductChain_boundary
    (current : ClosedSeparatedProductCurrent) :
    SphereProductSingularChainComplex.d 2 1 (rejoinedProductChain current.1) = 0 := by
  apply (productChainDiagonalEquiv 1).injective
  rw [map_zero, productChainDiagonalEquiv_boundary_rejoined, current.2, map_zero]

/-- [proved-derived; formal-checked] Every closed separated current reconstructs a genuine closed
singular product cycle. -/
def rejoinedProductCycle (current : ClosedSeparatedProductCurrent) : ProductTwoCycle :=
  ⟨rejoinedProductChain current.1, rejoinedProductChain_boundary current⟩

/-- The genuine product-chain residue after exact axis separation and ordered-shuffle
reconstruction.  This retains the full singular source occurrence rather than passing to a
normalized or endpoint-only quotient. -/
def productRoundTripDefectChain (chain : ProductChain 2) : ProductChain 2 :=
  rejoinedProductChain
      (separateTwo SphereSSet SphereSSet (productChainDiagonalEquiv 2 chain)) - chain

/-- [proved-derived; formal-checked] In the diagonal chart, the genuine singular-chain residue is
exactly the generic retained reconstruction defect. -/
theorem productRoundTripDefectChain_diagonal (chain : ProductChain 2) :
    productChainDiagonalEquiv 2 (productRoundTripDefectChain chain) =
      diagonalRoundTripDefectTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 chain) := by
  simp [productRoundTripDefectChain, rejoinedProductChain,
    diagonalRoundTripDefectTwo]

/-- [proved-derived; formal-checked] Separation followed by rejoining changes every genuine
product two-cycle by a genuine closed singular two-cycle.  The precise remaining reconstruction
obligation is to fill this returned cycle uniformly in degree three. -/
theorem productRoundTripDefectChain_boundary (cycle : ProductTwoCycle) :
    SphereProductSingularChainComplex.d 2 1
      (productRoundTripDefectChain cycle.1) = 0 := by
  apply (productChainDiagonalEquiv 1).injective
  rw [map_zero, productChainDiagonalEquiv_boundary,
    productRoundTripDefectChain_diagonal]
  have diagonalClosed :
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1) = 0 := by
    rw [← productChainDiagonalEquiv_boundary, cycle.2, map_zero]
  have law := LinearMap.congr_fun
    (boundary_diagonalRoundTripDefectTwo SphereSSet SphereSSet)
      (productChainDiagonalEquiv 2 cycle.1)
  change diagonalBoundaryTwo SphereSSet SphereSSet
      (diagonalRoundTripDefectTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1)) =
    diagonalRoundTripDefectOne SphereSSet SphereSSet
      (diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1)) at law
  rw [law, diagonalClosed]
  simp [diagonalRoundTripDefectOne]

/-- The exact closed reconstruction defect returned by one genuine product cycle. -/
def productRoundTripDefectCycle (cycle : ProductTwoCycle) : ProductTwoCycle :=
  ⟨productRoundTripDefectChain cycle.1,
    productRoundTripDefectChain_boundary cycle⟩

/-- The explicit genuine degree-three singular chain filling the complete reconstruction defect. -/
def productRoundTripDefectFillerChain (cycle : ProductTwoCycle) : ProductChain 3 :=
  (productChainDiagonalEquiv 3).symm
    (diagonalReconstructionFillerTwo SphereSSet SphereSSet
      (productChainDiagonalEquiv 2 cycle.1))

/-- [proved-derived; formal-checked] The genuine sphere-product separate--shuffle round trip is
chain-homotopic to the identity in degree two, with the complete source occurrence and four-term
degree-three filler retained. -/
theorem productRoundTripDefectFillerChain_boundary (cycle : ProductTwoCycle) :
    SphereProductSingularChainComplex.d 3 2
        (productRoundTripDefectFillerChain cycle) =
      productRoundTripDefectChain cycle.1 := by
  apply (productChainDiagonalEquiv 2).injective
  rw [productChainDiagonalEquiv_boundary_three,
    productRoundTripDefectFillerChain, LinearEquiv.apply_symm_apply,
    productRoundTripDefectChain_diagonal]
  have diagonalClosed :
      diagonalBoundaryTwo SphereSSet SphereSSet
        (productChainDiagonalEquiv 2 cycle.1) = 0 := by
    rw [← productChainDiagonalEquiv_boundary, cycle.2, map_zero]
  exact (diagonalRoundTripDefectTwo_eq_boundary_of_cycle
    (productChainDiagonalEquiv 2 cycle.1) diagonalClosed).symm

/-- [proved-derived; formal-checked] The reconstruction is an actual boundary holon: its source is
the original genuine product cycle, its target is its separated-and-rejoined chain, and its current
is the explicit four-term degree-three filler. -/
def productReconstructionBoundaryHolon :
    Holonics.BoundaryHolon (ProductChain 2) (ProductChain 3) where
  Occurrence := ProductTwoCycle
  source cycle := cycle.1
  target cycle := rejoinedProductChain (separatedProductCycle cycle)
  receive := productRoundTripDefectFillerChain
  boundary := (SphereProductSingularChainComplex.d 3 2).hom.toAddMonoidHom
  returnsBoundary := by
    intro cycle
    change SphereProductSingularChainComplex.d 3 2
        (productRoundTripDefectFillerChain cycle) =
      rejoinedProductChain (separatedProductCycle cycle) - cycle.1
    rw [productRoundTripDefectFillerChain_boundary]
    rfl

section Audit

#print axioms productChainDiagonalEquiv_boundary_generator
#print axioms productChainDiagonalEquiv_boundary_three_generator
#print axioms productChainDiagonalEquiv_boundary
#print axioms productChainDiagonalEquiv_boundary_three
#print axioms separatedProductThreeChain_boundary
#print axioms separatedProductCycle_boundary
#print axioms rejoinedProductThreeChain_boundary
#print axioms rejoinedProductChain_of_separatedBoundary
#print axioms productChainDiagonalEquiv_boundary_rejoined
#print axioms rejoinedProductChain_boundary
#print axioms productRoundTripDefectChain_diagonal
#print axioms productRoundTripDefectChain_boundary
#print axioms productRoundTripDefectFillerChain_boundary

end Audit

end Holonics.Hodge.HodgeProductDiagonal
