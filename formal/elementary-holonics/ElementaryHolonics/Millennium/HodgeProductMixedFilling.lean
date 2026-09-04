import ElementaryHolonics.Millennium.HodgeProductDiagonal
import ElementaryHolonics.Millennium.HodgeSphereChainCurrent
import ElementaryHolonics.Millennium.HodgeCommonStarNormalization
import ElementaryHolonics.Millennium.HodgeSphereLowDegreeHomology
import ElementaryHolonics.Foundation.ProductDegreeTwo
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Exact filling of the decomposable mixed sphere-product current

The Alexander--Whitney receiver retains a genuine `1 × 1` interaction axis.  It cannot be
discarded merely because `H₁(S²; ℚ) = 0`.  Here that degree-one result is transported through the
complete pair-occurrence population: the tensor product of two closed sphere one-currents is the
boundary of an explicit `2 × 1` current.  This is the first source-specific contraction used by
the full degree-two ruling decomposition.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProductMixedFilling

open Simplicial
open Soma.Holonics.DiagonalChainTransport
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeSphereChainCurrent
open Soma.Holonics.Millennium.HodgeSphereProductRulingCycles
open Soma.Holonics.Millennium.HodgeSphereLowDegreeHomology

/-- Exact coefficient product of two finite occurrence populations. -/
def pairCurrent {Left Right : Type*} (left : Current Left) (right : Current Right) :
    Current (Left × Right) :=
  finsuppTensorFinsupp' ℚ Left Right (left ⊗ₜ[ℚ] right)

@[simp]
theorem pairCurrent_generator {Left Right : Type*} (left : Left) (right : Right) :
    pairCurrent (generator left) (generator right) = generator (left, right) := by
  simp [pairCurrent, generator]

@[simp]
theorem pairCurrent_add_left {Left Right : Type*}
    (left₁ left₂ : Current Left) (right : Current Right) :
    pairCurrent (left₁ + left₂) right =
      pairCurrent left₁ right + pairCurrent left₂ right := by
  simp [pairCurrent, TensorProduct.add_tmul]

@[simp]
theorem pairCurrent_add_right {Left Right : Type*}
    (left : Current Left) (right₁ right₂ : Current Right) :
    pairCurrent left (right₁ + right₂) =
      pairCurrent left right₁ + pairCurrent left right₂ := by
  simp [pairCurrent, TensorProduct.tmul_add]

@[simp]
theorem pairCurrent_smul_left {Left Right : Type*}
    (coefficient : ℚ) (left : Current Left) (right : Current Right) :
    pairCurrent (coefficient • left) right = coefficient • pairCurrent left right := by
  simp [pairCurrent, TensorProduct.smul_tmul]

@[simp]
theorem pairCurrent_smul_right {Left Right : Type*}
    (coefficient : ℚ) (left : Current Left) (right : Current Right) :
    pairCurrent left (coefficient • right) = coefficient • pairCurrent left right := by
  simp [pairCurrent, TensorProduct.tmul_smul]

@[simp]
theorem pairCurrent_zero_right {Left Right : Type*} (left : Current Left) :
    pairCurrent left (0 : Current Right) = 0 := by
  simpa using pairCurrent_smul_right (Left := Left) (Right := Right) 0 left 0

@[simp]
theorem pairCurrent_neg_left {Left Right : Type*}
    (left : Current Left) (right : Current Right) :
    pairCurrent (-left) right = -pairCurrent left right := by
  simpa only [neg_smul, one_smul] using
    pairCurrent_smul_left (Left := Left) (Right := Right) (-1) left right

@[simp]
theorem pairCurrent_neg_right {Left Right : Type*}
    (left : Current Left) (right : Current Right) :
    pairCurrent left (-right) = -pairCurrent left right := by
  simpa only [neg_smul, one_smul] using
    pairCurrent_smul_right (Left := Left) (Right := Right) (-1) left right

@[simp]
theorem pairCurrent_sub_right {Left Right : Type*}
    (left : Current Left) (right₁ right₂ : Current Right) :
    pairCurrent left (right₁ - right₂) =
      pairCurrent left right₁ - pairCurrent left right₂ := by
  rw [sub_eq_add_neg, pairCurrent_add_right, pairCurrent_neg_right]
  simp only [sub_eq_add_neg]

/-- [definition] Reverse the presented orientation of a pair current.  This is the exact
polarity change for the pair axis; it changes no occurrence coefficient and forgets no lineage. -/
def flipPair {Left Right : Type*} :
    Current (Left × Right) →ₗ[ℚ] Current (Right × Left) :=
  extend fun pair => generator (pair.2, pair.1)

@[simp]
theorem flipPair_generator {Left Right : Type*} (left : Left) (right : Right) :
    flipPair (generator (left, right)) = generator (right, left) := by
  exact extend_generator _ _

/-- [proved-derived; formal-checked] Reorientation exchanges the complete two incidence
currents, rather than merely renaming generator coordinates. -/
@[simp]
theorem flipPair_pairCurrent {Left Right : Type*}
    (left : Current Left) (right : Current Right) :
    flipPair (pairCurrent left right) = pairCurrent right left := by
  induction left using Finsupp.induction_linear generalizing right with
  | zero => simp [pairCurrent]
  | add left₁ left₂ hleft₁ hleft₂ =>
      simp only [pairCurrent_add_left, map_add, hleft₁, hleft₂,
        pairCurrent_add_right]
  | single leftOccurrence leftCoefficient =>
      induction right using Finsupp.induction_linear with
      | zero => simp [pairCurrent]
      | add right₁ right₂ hright₁ hright₂ =>
          simp only [pairCurrent_add_right, map_add, hright₁, hright₂,
            pairCurrent_add_left]
      | single rightOccurrence rightCoefficient =>
          rw [show Finsupp.single leftOccurrence leftCoefficient =
              leftCoefficient • generator leftOccurrence by simp [generator],
            show Finsupp.single rightOccurrence rightCoefficient =
              rightCoefficient • generator rightOccurrence by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right, map_smul,
            pairCurrent_generator, flipPair_generator]
          module

/-- [proved-derived; formal-checked] Changing pair polarity twice returns the same addressed
current exactly. -/
@[simp]
theorem flipPair_involutive {Left Right : Type*}
    (current : Current (Left × Right)) :
    flipPair (flipPair current) = current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp

/-- [definition] Apply a linear transport to the incidence currently presented first. -/
def mapPairLeft {Left Left' Right : Type*}
    (transport : Current Left →ₗ[ℚ] Current Left') :
    Current (Left × Right) →ₗ[ℚ] Current (Left' × Right) :=
  extend fun pair => pairCurrent (transport (generator pair.1)) (generator pair.2)

/-- [definition] Apply a linear transport to the incidence presented second.  This is not a
second implementation: reverse the pair orientation, use the first-incidence action, then reverse
the receiver orientation back. -/
def mapPairRight {Left Right Right' : Type*}
    (transport : Current Right →ₗ[ℚ] Current Right') :
    Current (Left × Right) →ₗ[ℚ] Current (Left × Right') :=
  flipPair.comp ((mapPairLeft transport).comp flipPair)

@[simp]
theorem mapPairLeft_generator {Left Left' Right : Type*}
    (transport : Current Left →ₗ[ℚ] Current Left') (left : Left) (right : Right) :
    mapPairLeft transport (generator (left, right)) =
      pairCurrent (transport (generator left)) (generator right) := by
  exact extend_generator _ _

@[simp]
theorem mapPairRight_generator {Left Right Right' : Type*}
    (transport : Current Right →ₗ[ℚ] Current Right') (left : Left) (right : Right) :
    mapPairRight transport (generator (left, right)) =
      pairCurrent (generator left) (transport (generator right)) := by
  simp [mapPairRight, LinearMap.comp_apply]

/-- [proved-derived; formal-checked] Pair transport acts on the complete left current, not only
on generators. -/
theorem mapPairLeft_pairCurrent {Left Left' Right : Type*}
    (transport : Current Left →ₗ[ℚ] Current Left')
    (left : Current Left) (right : Current Right) :
    mapPairLeft transport (pairCurrent left right) =
      pairCurrent (transport left) right := by
  induction left using Finsupp.induction_linear generalizing right with
  | zero => simp [pairCurrent]
  | add left₁ left₂ hleft₁ hleft₂ =>
      simp only [pairCurrent_add_left, map_add, hleft₁, hleft₂]
  | single leftOccurrence leftCoefficient =>
      induction right using Finsupp.induction_linear with
      | zero => simp [pairCurrent]
      | add right₁ right₂ hright₁ hright₂ =>
          simp only [pairCurrent_add_right, map_add, hright₁, hright₂]
      | single rightOccurrence rightCoefficient =>
          rw [show Finsupp.single leftOccurrence leftCoefficient =
              leftCoefficient • generator leftOccurrence by simp [generator],
            show Finsupp.single rightOccurrence rightCoefficient =
              rightCoefficient • generator rightOccurrence by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right, map_smul,
            pairCurrent_generator, mapPairLeft_generator]

/-- [proved-derived; formal-checked] Pair transport acts on the complete right current. -/
theorem mapPairRight_pairCurrent {Left Right Right' : Type*}
    (transport : Current Right →ₗ[ℚ] Current Right')
    (left : Current Left) (right : Current Right) :
    mapPairRight transport (pairCurrent left right) =
      pairCurrent left (transport right) := by
  simp [mapPairRight, LinearMap.comp_apply, mapPairLeft_pairCurrent]

/-- [proved-derived; formal-checked] Successive transports on one pair incidence compose. -/
theorem mapPairLeft_comp {Left Middle Target Right : Type*}
    (outer : Current Middle →ₗ[ℚ] Current Target)
    (inner : Current Left →ₗ[ℚ] Current Middle)
    (current : Current (Left × Right)) :
    mapPairLeft outer (mapPairLeft inner current) =
      mapPairLeft (outer.comp inner) current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨leftOccurrence, rightOccurrence⟩
      rw [show Finsupp.single (leftOccurrence, rightOccurrence) coefficient =
          coefficient • generator (leftOccurrence, rightOccurrence) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator,
        mapPairLeft_pairCurrent, LinearMap.comp_apply]

/-- [proved-derived; formal-checked] Successive right-incidence transports compose. -/
theorem mapPairRight_comp {Left Right Middle Target : Type*}
    (outer : Current Middle →ₗ[ℚ] Current Target)
    (inner : Current Right →ₗ[ℚ] Current Middle)
    (current : Current (Left × Right)) :
    mapPairRight outer (mapPairRight inner current) =
      mapPairRight (outer.comp inner) current := by
  simp only [mapPairRight, LinearMap.comp_apply]
  rw [flipPair_involutive, mapPairLeft_comp]

/-- [proved-derived; formal-checked] Acting on the second incidence after reorientation is exactly
reorientation after acting on the presented incidence. -/
theorem mapPairRight_flipPair
    {Left Left' Right : Type*}
    (transport : Current Left →ₗ[ℚ] Current Left')
    (current : Current (Left × Right)) :
    mapPairRight transport (flipPair current) =
      flipPair (mapPairLeft transport current) := by
  simp [mapPairRight, LinearMap.comp_apply]

/-- [proved-derived; formal-checked] Independent incidence transports commute exactly. -/
theorem mapPairLeft_right_commute
    {Left Left' Right Right' : Type*}
    (leftTransport : Current Left →ₗ[ℚ] Current Left')
    (rightTransport : Current Right →ₗ[ℚ] Current Right')
    (current : Current (Left × Right)) :
    mapPairLeft leftTransport (mapPairRight rightTransport current) =
      mapPairRight rightTransport (mapPairLeft leftTransport current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨leftOccurrence, rightOccurrence⟩
      rw [show Finsupp.single (leftOccurrence, rightOccurrence) coefficient =
          coefficient • generator (leftOccurrence, rightOccurrence) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator, mapPairRight_generator,
        mapPairLeft_pairCurrent, mapPairRight_pairCurrent]

/-! ## Exact degree-zero contraction at the geometric ruling basepoint -/

/-- [definition] The coefficient sum of a finite sphere point current. -/
def sphereZeroAugmentation : Current (SphereSimplex 0) →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ (fun _ : SphereSimplex 0 => LinearMap.id)

@[simp]
theorem sphereZeroAugmentation_generator (simplex : SphereSimplex 0) :
    sphereZeroAugmentation (generator simplex) = 1 := by
  simp [sphereZeroAugmentation, generator]

/-- [definition] The zero-simplex at the same geometric basepoint used by both ruling maps. -/
noncomputable def rulingBasepointSimplex : SphereSimplex 0 :=
  TopCat.toSSetObj₀Equiv.symm sphereBasepoint

/-- [definition] A selected addressed edge from the ruling basepoint to every sphere point.
Path-connectedness supplies the occurrence; its endpoints remain part of its dependent type. -/
noncomputable def rulingBasepointEdge (simplex : SphereSimplex 0) :
    SSet.Edge rulingBasepointSimplex simplex := by
  simpa [rulingBasepointSimplex] using
    (Classical.choose
      (sphere_zero_chain_difference_is_boundary sphereBasepoint
        (TopCat.toSSetObj₀Equiv simplex)))

/-- [proved-derived; formal-checked] The selected basepoint edge returns terminal point minus
initial point in the finite-current chart. -/
theorem rulingBasepointEdge_boundary (simplex : SphereSimplex 0) :
    sphereCurrentBoundary 0 (generator (rulingBasepointEdge simplex).edge) =
      generator simplex - generator rulingBasepointSimplex := by
  rw [sphereCurrentBoundary_generator]
  rw [sphereCurrentBoundaryAtom, Fin.sum_univ_two]
  change (-1 : ℚ) ^ (0 : ℕ) •
        generator (face 0 (rulingBasepointEdge simplex).edge) +
      (-1 : ℚ) ^ (1 : ℕ) •
        generator (face 1 (rulingBasepointEdge simplex).edge) = _
  have targetLaw : face 0 (rulingBasepointEdge simplex).edge = simplex := by
    exact (rulingBasepointEdge simplex).tgt_eq
  have sourceLaw : face 1 (rulingBasepointEdge simplex).edge =
      rulingBasepointSimplex := by
    exact (rulingBasepointEdge simplex).src_eq
  rw [targetLaw, sourceLaw]
  norm_num [sub_eq_add_neg]

/-- [definition] Linear extension of all selected point-to-basepoint edges. -/
noncomputable def sphereZeroContraction :
    Current (SphereSimplex 0) →ₗ[ℚ] Current (SphereSimplex 1) :=
  extend fun simplex => generator (rulingBasepointEdge simplex).edge

@[simp]
theorem sphereZeroContraction_generator (simplex : SphereSimplex 0) :
    sphereZeroContraction (generator simplex) =
      generator (rulingBasepointEdge simplex).edge := by
  exact extend_generator _ _

/-- [proved-derived; formal-checked] Exact reduced degree-zero contraction.  The returned scalar
is the coefficient population and the reconstruction fibre is the complete selected edge current. -/
theorem sphereZeroContraction_boundary (current : Current (SphereSimplex 0)) :
    sphereCurrentBoundary 0 (sphereZeroContraction current) =
      current - sphereZeroAugmentation current • generator rulingBasepointSimplex := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, sphereZeroAugmentation_generator,
        sphereZeroContraction_generator]
      rw [rulingBasepointEdge_boundary]
      module

/-! ## A linear filler on the complete degree-one cycle carrier -/

/-- [proved-derived; formal-checked] The finite-current boundary squares to zero in the exact
categorical singular-chain chart. -/
theorem sphereCurrentBoundary_sq (current : Current (SphereSimplex 2)) :
    sphereCurrentBoundary 0 (sphereCurrentBoundary 1 current) = 0 := by
  rw [← sphereChain_current_roundtrip 2 current]
  rw [← sphereChainToCurrent_boundary]
  rw [← sphereChainToCurrent_boundary]
  change sphereChainToCurrent 0
      ((HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 1 0)
        ((HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 2 1)
          (sphereCurrentToChain 2 current))) = 0
  rw [← CategoryTheory.comp_apply, HomologicalComplex.d_comp_d]
  simp

/-- [proved-derived; formal-checked] The source-specific singular boundary is exactly the generic
factor boundary.  This is the chart bridge which lets the generic product-current owner consume
the already constructed sphere contractions without duplicating either boundary law. -/
theorem factorBoundary_sphere_eq_sphereCurrentBoundary (degree : ℕ) :
    factorBoundary SphereSSet degree = sphereCurrentBoundary degree := by
  apply Finsupp.lhom_ext
  intro simplex coefficient
  rw [show Finsupp.single simplex coefficient =
      coefficient • generator simplex by simp [generator]]
  simp only [map_smul, factorBoundary_generator,
    sphereCurrentBoundary_generator]
  rfl

/-- [definition] Closed finite sphere one-currents. -/
noncomputable abbrev SphereOneCycleCurrent :=
  LinearMap.ker (sphereCurrentBoundary 0)

/-- [definition] The genuine two-boundary with codomain restricted to closed one-currents. -/
noncomputable def sphereBoundaryTwoToOneCycles :
    Current (SphereSimplex 2) →ₗ[ℚ] SphereOneCycleCurrent :=
  LinearMap.codRestrict (LinearMap.ker (sphereCurrentBoundary 0))
    (sphereCurrentBoundary 1) sphereCurrentBoundary_sq

/-- [proved-derived; formal-checked] The constructed singular `H₁(S²;ℚ)=0` filler makes the
current boundary onto the complete one-cycle submodule. -/
theorem sphereBoundaryTwoToOneCycles_surjective :
    Function.Surjective sphereBoundaryTwoToOneCycles := by
  intro cycle
  let chain : SphereChain 1 := sphereCurrentToChain 1 cycle.1
  have closed :
      HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 1 0 chain = 0 := by
    apply (sphereChainEquivCurrent 0).injective
    change sphereChainToCurrent 0
        (HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 1 0 chain) =
      sphereChainToCurrent 0 0
    rw [sphereChainToCurrent_boundary]
    dsimp [chain]
    rw [sphereChain_current_roundtrip, cycle.2, map_zero]
  obtain ⟨filling, fillingBoundary⟩ :=
    HodgeSphereDegreeOneFilling.exists_sphereDegreeOneFilling chain closed
  refine ⟨sphereChainToCurrent 2 filling, ?_⟩
  apply Subtype.ext
  change sphereCurrentBoundary 1 (sphereChainToCurrent 2 filling) = cycle.1
  rw [← sphereChainToCurrent_boundary, fillingBoundary,
    sphereChain_current_roundtrip]

/-- [definition] A linear selected filling for every closed finite one-current.  The construction
uses projectivity of rational vector spaces only after source surjectivity is proved above. -/
noncomputable def sphereOneCycleFiller :
    SphereOneCycleCurrent →ₗ[ℚ] Current (SphereSimplex 2) :=
  Classical.choose
    (sphereBoundaryTwoToOneCycles.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr sphereBoundaryTwoToOneCycles_surjective))

/-- [proved-derived; formal-checked] The selected linear filler returns its complete source
one-current exactly. -/
theorem sphereOneCycleFiller_boundary (cycle : SphereOneCycleCurrent) :
    sphereCurrentBoundary 1 (sphereOneCycleFiller cycle) = cycle.1 := by
  have inverseLaw := Classical.choose_spec
    (sphereBoundaryTwoToOneCycles.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr sphereBoundaryTwoToOneCycles_surjective))
  have pointLaw := LinearMap.congr_fun inverseLaw cycle
  exact congrArg Subtype.val pointLaw

/-- [proved-derived; formal-checked] Every sphere one-boundary has zero coefficient population. -/
theorem sphereZeroAugmentation_boundary (current : Current (SphereSimplex 1)) :
    sphereZeroAugmentation (sphereCurrentBoundary 0 current) = 0 := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, sphereCurrentBoundary_generator,
        sphereCurrentBoundaryAtom, map_sum, sphereZeroAugmentation_generator]
      have alternatingSum :
          (∑ omitted : Fin 2, (-1 : ℚ) ^ (omitted : ℕ)) = 0 := by
        rw [Fin.sum_univ_two]
        norm_num
      simp only [smul_eq_mul, mul_one]
      rw [alternatingSum]
      simp

/-- [definition] Remove the exact degree-zero contraction from a one-current.  Its result is a
closed one-current even when the source was not closed. -/
noncomputable def sphereOneCyclePart :
    Current (SphereSimplex 1) →ₗ[ℚ] SphereOneCycleCurrent :=
  LinearMap.codRestrict (LinearMap.ker (sphereCurrentBoundary 0))
    (LinearMap.id - sphereZeroContraction.comp (sphereCurrentBoundary 0))
    (fun current => by
      change sphereCurrentBoundary 0
          (current - sphereZeroContraction (sphereCurrentBoundary 0 current)) = 0
      rw [map_sub, sphereZeroContraction_boundary,
        sphereZeroAugmentation_boundary]
      simp)

/-- [definition] Degree-one contraction on every finite sphere one-current. -/
noncomputable def sphereOneContraction :
    Current (SphereSimplex 1) →ₗ[ℚ] Current (SphereSimplex 2) :=
  sphereOneCycleFiller.comp sphereOneCyclePart

/-- [proved-derived; formal-checked] The degree-one contraction identity
`d h₁ + h₀ d = id` holds on every finite sphere one-current. -/
theorem sphereOneContraction_boundary (current : Current (SphereSimplex 1)) :
    sphereCurrentBoundary 1 (sphereOneContraction current) =
      current - sphereZeroContraction (sphereCurrentBoundary 0 current) := by
  rw [sphereOneContraction, LinearMap.comp_apply,
    sphereOneCycleFiller_boundary]
  rfl

/-- [proved-derived; formal-checked] The genuine singular two-sphere inhabits the source-neutral
low-degree current datum.  Its fields are the geometric ruling basepoint, coefficient
augmentation, selected point paths, and the exact `H₁(S²;ℚ)=0` filling. -/
noncomputable def sphereLowDegreeCurrentDatum :
    LowDegreeCurrentDatum SphereSSet where
  basepoint := rulingBasepointSimplex
  augmentation := sphereZeroAugmentation
  augmentation_basepoint := sphereZeroAugmentation_generator _
  augmentation_boundary_zero := by
    intro edge
    rw [factorBoundary_sphere_eq_sphereCurrentBoundary]
    exact sphereZeroAugmentation_boundary edge
  boundary_boundary_zero := by
    intro current
    rw [factorBoundary_sphere_eq_sphereCurrentBoundary,
      factorBoundary_sphere_eq_sphereCurrentBoundary]
    exact sphereCurrentBoundary_sq current
  h0 := sphereZeroContraction
  h0_boundary := by
    intro current
    rw [factorBoundary_sphere_eq_sphereCurrentBoundary]
    exact sphereZeroContraction_boundary current
  h1 := sphereOneContraction
  h1_boundary_of_closed := by
    intro current closed
    rw [factorBoundary_sphere_eq_sphereCurrentBoundary] at closed ⊢
    rw [sphereOneContraction_boundary, closed, map_zero, sub_zero]

/-- [proved-derived; formal-checked] The generic product contraction is now inhabited by the
genuine two-sphere factor datum at degree zero.  The returned scalar is the product augmentation,
not an erased point count. -/
theorem spherePairDiagonalH0_boundary
    (current : Current (DiagonalOccurrence SphereSSet SphereSSet 0)) :
    diagonalBoundaryOne SphereSSet SphereSSet
        (Soma.Holonics.DiagonalChainTransport.productH0Diagonal
          sphereLowDegreeCurrentDatum sphereLowDegreeCurrentDatum current) =
      current -
        Soma.Holonics.DiagonalChainTransport.productAugmentation
            sphereLowDegreeCurrentDatum sphereLowDegreeCurrentDatum current •
          generator
            (sphereLowDegreeCurrentDatum.basepoint,
              sphereLowDegreeCurrentDatum.basepoint) := by
  exact Soma.Holonics.DiagonalChainTransport.diagonalBoundaryOne_productH0Diagonal
    sphereLowDegreeCurrentDatum sphereLowDegreeCurrentDatum current

/-- [proved-derived; formal-checked] Every closed diagonal one-current of the sphere product has
the explicit coupled product filler: separate, fill both polarized axes, shuffle-return, and
subtract the exact reconstruction reflection. -/
theorem spherePairDiagonalH1_boundary
    (current : Current (DiagonalOccurrence SphereSSet SphereSSet 1))
    (closed : diagonalBoundaryOne SphereSSet SphereSSet current = 0) :
    diagonalBoundaryTwo SphereSSet SphereSSet
        (Soma.Holonics.DiagonalChainTransport.productH1Diagonal
          sphereLowDegreeCurrentDatum sphereLowDegreeCurrentDatum current) = current := by
  exact
    Soma.Holonics.DiagonalChainTransport.diagonalBoundaryTwo_productH1Diagonal_of_closed
      sphereLowDegreeCurrentDatum sphereLowDegreeCurrentDatum current closed

/-- [proved-derived; formal-checked] The degree-one contraction identity transported through
every left incidence of a pair current. -/
theorem mapPairLeft_sphereOneContraction_boundary
    {Right : Type*}
    (current : Current (SphereSimplex 1 × Right)) :
    mapPairLeft (sphereCurrentBoundary 1)
        (mapPairLeft sphereOneContraction current) =
      current -
        mapPairLeft sphereZeroContraction
          (mapPairLeft (sphereCurrentBoundary 0) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator, mapPairLeft_pairCurrent]
      rw [sphereOneContraction_boundary]
      rw [sub_eq_add_neg, pairCurrent_add_left, pairCurrent_neg_left,
        pairCurrent_generator]
      module

/-- [proved-derived; formal-checked] The same degree-one contraction identity transported
through every right incidence. -/
theorem mapPairRight_sphereOneContraction_boundary
    {Left : Type*}
    (current : Current (Left × SphereSimplex 1)) :
    mapPairRight (sphereCurrentBoundary 1)
        (mapPairRight sphereOneContraction current) =
      current -
        mapPairRight sphereZeroContraction
          (mapPairRight (sphereCurrentBoundary 0) current) := by
  simp only [mapPairRight, LinearMap.comp_apply]
  rw [flipPair_involutive,
    mapPairLeft_sphereOneContraction_boundary,
    map_sub, flipPair_involutive]
  simp only [flipPair_involutive]

/-! ## The reduced degree-zero pair fibre

The first coordinate of a pair is not a separate "left" mechanism.  It is the currently
presented incidence.  Augmentation collapses only that presented zero-chain, while the complete
other incidence is retained as its reconstruction fibre.  The opposite orientation is obtained
through `flipPair` above. -/

/-- [definition] Collapse the presented sphere zero-current to its exact coefficient population,
retaining the complete opposite incidence current. -/
def pairFirstAugmentation {Right : Type*} :
    Current (SphereSimplex 0 × Right) →ₗ[ℚ] Current Right :=
  extend fun pair => generator pair.2

/-- [definition] Reinsert a retained current at the geometric ruling basepoint. -/
def pairFirstBase {Right : Type*} :
    Current Right →ₗ[ℚ] Current (SphereSimplex 0 × Right) :=
  extend fun right => generator (rulingBasepointSimplex, right)

@[simp]
theorem pairFirstAugmentation_generator {Right : Type*}
    (left : SphereSimplex 0) (right : Right) :
    pairFirstAugmentation (generator (left, right)) = generator right := by
  exact extend_generator _ _

@[simp]
theorem pairFirstBase_generator {Right : Type*} (right : Right) :
    pairFirstBase (generator right) =
      generator (rulingBasepointSimplex, right) := by
  exact extend_generator _ _

/-- [proved-derived; formal-checked] Pair augmentation is the tensor contraction of the first
zero-current with its coefficient sum; it retains the complete second current. -/
theorem pairFirstAugmentation_pairCurrent {Right : Type*}
    (left : Current (SphereSimplex 0)) (right : Current Right) :
    pairFirstAugmentation (pairCurrent left right) =
      sphereZeroAugmentation left • right := by
  induction left using Finsupp.induction_linear generalizing right with
  | zero => simp [pairCurrent]
  | add left₁ left₂ hleft₁ hleft₂ =>
      simp only [pairCurrent_add_left, map_add, hleft₁, hleft₂]
      module
  | single leftOccurrence leftCoefficient =>
      induction right using Finsupp.induction_linear with
      | zero => simp [pairCurrent]
      | add right₁ right₂ hright₁ hright₂ =>
          simp only [pairCurrent_add_right, map_add, hright₁, hright₂,
            smul_add]
      | single rightOccurrence rightCoefficient =>
          rw [show Finsupp.single leftOccurrence leftCoefficient =
              leftCoefficient • generator leftOccurrence by simp [generator],
            show Finsupp.single rightOccurrence rightCoefficient =
              rightCoefficient • generator rightOccurrence by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right, map_smul,
            pairCurrent_generator, pairFirstAugmentation_generator,
            sphereZeroAugmentation_generator]
          module

/-- [proved-derived; formal-checked] Basepoint insertion reconstructs the exact pure pair
current with the ruling point in the presented coordinate. -/
theorem pairFirstBase_current {Right : Type*} (right : Current Right) :
    pairFirstBase right =
      pairCurrent (generator rulingBasepointSimplex) right := by
  induction right using Finsupp.induction_linear with
  | zero => simp [pairCurrent]
  | add left right hleft hright =>
      simp only [map_add, pairCurrent_add_right, hleft, hright]
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul, pairFirstBase_generator,
        pairCurrent_smul_right, pairCurrent_generator]

/-- [proved-derived; formal-checked] The reduced degree-zero contraction on the presented
incidence is exact, and the only returned residue is its basepoint coefficient fibre. -/
theorem mapPairLeft_sphereZeroContraction_boundary
    {Right : Type*}
    (current : Current (SphereSimplex 0 × Right)) :
    mapPairLeft (sphereCurrentBoundary 0)
        (mapPairLeft sphereZeroContraction current) =
      current - pairFirstBase (pairFirstAugmentation current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp [pairFirstBase]
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator, mapPairLeft_pairCurrent,
        pairFirstAugmentation_generator, pairFirstBase_generator]
      rw [sphereZeroContraction_boundary]
      simp only [sphereZeroAugmentation_generator, one_smul, sub_eq_add_neg,
        pairCurrent_add_left, pairCurrent_neg_left, pairCurrent_generator]
      module

/-- [proved-derived; formal-checked] Transport in the retained incidence commutes with
augmentation of the presented zero-current. -/
theorem pairFirstAugmentation_mapPairRight
    {Right Right' : Type*}
    (transport : Current Right →ₗ[ℚ] Current Right')
    (current : Current (SphereSimplex 0 × Right)) :
    pairFirstAugmentation (mapPairRight transport current) =
      transport (pairFirstAugmentation current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairRight_generator,
        pairFirstAugmentation_pairCurrent,
        sphereZeroAugmentation_generator, one_smul,
        pairFirstAugmentation_generator]

/-- [proved-derived; formal-checked] A boundary in the presented sphere coordinate has zero
augmented population. -/
theorem pairFirstAugmentation_mapPairLeft_boundary
    {Right : Type*}
    (current : Current (SphereSimplex 1 × Right)) :
    pairFirstAugmentation
        (mapPairLeft (sphereCurrentBoundary 0) current) = 0 := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator,
        pairFirstAugmentation_pairCurrent,
        sphereZeroAugmentation_boundary, zero_smul]
      simp

/-- [proved-derived; formal-checked] Two successive sphere boundaries vanish on the presented
incidence of every pair current. -/
theorem mapPairLeft_sphereBoundary_sq
    {Right : Type*}
    (current : Current (SphereSimplex 2 × Right)) :
    mapPairLeft (sphereCurrentBoundary 0)
        (mapPairLeft (sphereCurrentBoundary 1) current) = 0 := by
  rw [mapPairLeft_comp]
  have squareZero :
      (sphereCurrentBoundary 0).comp (sphereCurrentBoundary 1) = 0 := by
    apply LinearMap.ext
    intro sphereCurrent
    exact sphereCurrentBoundary_sq sphereCurrent
  rw [squareZero]
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp [mapPairLeft, pairCurrent]

/-- [proved-derived; formal-checked] The opposite receiver orientation inherits boundary
nilpotence by the same pair flip, with no second boundary implementation. -/
theorem mapPairRight_sphereBoundary_sq
    {Left : Type*}
    (current : Current (Left × SphereSimplex 2)) :
    mapPairRight (sphereCurrentBoundary 0)
        (mapPairRight (sphereCurrentBoundary 1) current) = 0 := by
  simp only [mapPairRight, LinearMap.comp_apply]
  rw [flipPair_involutive, mapPairLeft_sphereBoundary_sq, map_zero]

/-! ## Graded polarity of the total product complex -/

/-- [definition] Reverse the two factors in total degree two.  The middle `1 × 1` axis carries
the unique Koszul minus sign; the outer axes are exchanged without loss. -/
def totalTwoFlip :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) →ₗ[ℚ]
      Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  extend fun occurrence => match occurrence with
    | .left left right => generator (.right right left)
    | .middle left right => -generator (.middle right left)
    | .right left right => generator (.left right left)

/-- [definition] Reverse the two factors in total degree three.  Every degree split has even
degree product, so no degree-three axis receives an additional sign. -/
def totalThreeFlip :
    Current (TotalThreeOccurrence SphereSSet SphereSSet) →ₗ[ℚ]
      Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  extend fun occurrence => match occurrence with
    | .left left right => generator (.right right left)
    | .leftMiddle left right => generator (.rightMiddle right left)
    | .rightMiddle left right => generator (.leftMiddle right left)
    | .right left right => generator (.left right left)

@[simp]
theorem totalTwoFlip_generator
    (occurrence : TotalTwoOccurrence SphereSSet SphereSSet) :
    totalTwoFlip (generator occurrence) = match occurrence with
      | .left left right => generator (.right right left)
      | .middle left right => -generator (.middle right left)
      | .right left right => generator (.left right left) := by
  exact extend_generator _ _

@[simp]
theorem totalThreeFlip_generator
    (occurrence : TotalThreeOccurrence SphereSSet SphereSSet) :
    totalThreeFlip (generator occurrence) = match occurrence with
      | .left left right => generator (.right right left)
      | .leftMiddle left right => generator (.rightMiddle right left)
      | .rightMiddle left right => generator (.leftMiddle right left)
      | .right left right => generator (.left right left) := by
  exact extend_generator _ _

/-- [proved-derived; formal-checked] Graded factor reversal is an exact involution in degree two. -/
@[simp]
theorem totalTwoFlip_involutive
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) :
    totalTwoFlip (totalTwoFlip current) = current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul]
      cases occurrence <;> simp

/-- [proved-derived; formal-checked] Factor reversal is an exact involution in degree three. -/
@[simp]
theorem totalThreeFlip_involutive
    (current : Current (TotalThreeOccurrence SphereSSet SphereSSet)) :
    totalThreeFlip (totalThreeFlip current) = current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul]
      cases occurrence <;> simp

/-- [proved-derived; formal-checked] The graded polarity commutes with the exact total boundary. -/
theorem totalBoundaryThree_flip
    (current : Current (TotalThreeOccurrence SphereSSet SphereSSet)) :
    totalBoundaryThree SphereSSet SphereSSet (totalThreeFlip current) =
      totalTwoFlip
        (totalBoundaryThree SphereSSet SphereSSet current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul]
      cases occurrence <;>
        simp [totalThreeFlip, totalTwoFlip, totalBoundaryThree,
          totalBoundaryThreeAtom] <;>
        module

def middleAxis :
    Current (SphereSimplex 1 × SphereSimplex 1) →ₗ[ℚ]
      Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  extend fun pair => generator (.middle pair.1 pair.2)

def leftAxis :
    Current (SphereSimplex 0 × SphereSimplex 2) →ₗ[ℚ]
      Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  extend fun pair => generator (.left pair.1 pair.2)

def leftMiddleAxis :
    Current (SphereSimplex 1 × SphereSimplex 2) →ₗ[ℚ]
      Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  extend fun pair => generator (.leftMiddle pair.1 pair.2)

/-- [definition] The opposite outer axis is the graded reorientation of the first axis. -/
def rightAxis :
    Current (SphereSimplex 2 × SphereSimplex 0) →ₗ[ℚ]
      Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  totalTwoFlip.comp (leftAxis.comp flipPair)

/-- [definition] The opposite middle axis is derived by the same graded reorientation. -/
def rightMiddleAxis :
    Current (SphereSimplex 2 × SphereSimplex 1) →ₗ[ℚ]
      Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  totalThreeFlip.comp (leftMiddleAxis.comp flipPair)

/-- [definition] The `0 × 3` endpoint axis. -/
def zeroThreeAxis :
    Current (SphereSimplex 0 × SphereSimplex 3) →ₗ[ℚ]
      Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  extend fun pair => generator (.left pair.1 pair.2)

/-- [definition] The `3 × 0` endpoint axis, derived by graded reorientation. -/
def threeZeroAxis :
    Current (SphereSimplex 3 × SphereSimplex 0) →ₗ[ℚ]
      Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  totalThreeFlip.comp (zeroThreeAxis.comp flipPair)

@[simp]
theorem middleAxis_generator (left : SphereSimplex 1) (right : SphereSimplex 1) :
    middleAxis (generator (left, right)) = generator (.middle left right) := by
  exact extend_generator _ _

@[simp]
theorem leftAxis_generator (left : SphereSimplex 0) (right : SphereSimplex 2) :
    leftAxis (generator (left, right)) = generator (.left left right) := by
  exact extend_generator _ _

@[simp]
theorem rightAxis_generator (left : SphereSimplex 2) (right : SphereSimplex 0) :
    rightAxis (generator (left, right)) = generator (.right left right) := by
  simp [rightAxis, LinearMap.comp_apply]

@[simp]
theorem rightMiddleAxis_generator (left : SphereSimplex 2) (right : SphereSimplex 1) :
    rightMiddleAxis (generator (left, right)) = generator (.rightMiddle left right) := by
  simp [rightMiddleAxis, LinearMap.comp_apply, leftMiddleAxis, totalThreeFlip]

@[simp]
theorem leftMiddleAxis_generator (left : SphereSimplex 1) (right : SphereSimplex 2) :
    leftMiddleAxis (generator (left, right)) = generator (.leftMiddle left right) := by
  exact extend_generator _ _

@[simp]
theorem zeroThreeAxis_generator (left : SphereSimplex 0) (right : SphereSimplex 3) :
    zeroThreeAxis (generator (left, right)) = generator (.left left right) := by
  exact extend_generator _ _

@[simp]
theorem threeZeroAxis_generator (left : SphereSimplex 3) (right : SphereSimplex 0) :
    threeZeroAxis (generator (left, right)) = generator (.right left right) := by
  simp [threeZeroAxis, LinearMap.comp_apply, zeroThreeAxis, totalThreeFlip]

/-- [proved-derived; formal-checked] Graded reversal carries the first outer embedding to the
opposite outer embedding. -/
theorem totalTwoFlip_leftAxis
    (current : Current (SphereSimplex 0 × SphereSimplex 2)) :
    totalTwoFlip (leftAxis current) = rightAxis (flipPair current) := by
  rw [rightAxis, LinearMap.comp_apply, LinearMap.comp_apply,
    flipPair_involutive]

/-- [proved-derived; formal-checked] Graded reversal carries the `0 × 3` endpoint embedding to
the derived `3 × 0` embedding. -/
theorem totalThreeFlip_zeroThreeAxis
    (current : Current (SphereSimplex 0 × SphereSimplex 3)) :
    totalThreeFlip (zeroThreeAxis current) = threeZeroAxis (flipPair current) := by
  rw [threeZeroAxis, LinearMap.comp_apply, LinearMap.comp_apply,
    flipPair_involutive]

/-! The three axis projections retain the full pair occurrence on their selected axis and return
zero on the other two.  Together with the inclusions above they are an exact reversible chart,
not an endpoint-only classification. -/

def leftAxisProjection :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) →ₗ[ℚ]
      Current (SphereSimplex 0 × SphereSimplex 2) :=
  extend fun occurrence => match occurrence with
    | .left left right => generator (left, right)
    | .middle _ _ => 0
    | .right _ _ => 0

def middleAxisProjection :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) →ₗ[ℚ]
      Current (SphereSimplex 1 × SphereSimplex 1) :=
  extend fun occurrence => match occurrence with
    | .left _ _ => 0
    | .middle left right => generator (left, right)
    | .right _ _ => 0

def rightAxisProjection :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) →ₗ[ℚ]
      Current (SphereSimplex 2 × SphereSimplex 0) :=
  extend fun occurrence => match occurrence with
    | .left _ _ => 0
    | .middle _ _ => 0
    | .right left right => generator (left, right)

/-- The two total-degree-one receiver projections. -/
def leftOneAxisProjection :
    Current (TotalOneOccurrence SphereSSet SphereSSet) →ₗ[ℚ]
      Current (SphereSimplex 0 × SphereSimplex 1) :=
  extend fun occurrence => match occurrence with
    | .left left right => generator (left, right)
    | .right _ _ => 0

def rightOneAxisProjection :
    Current (TotalOneOccurrence SphereSSet SphereSSet) →ₗ[ℚ]
      Current (SphereSimplex 1 × SphereSimplex 0) :=
  extend fun occurrence => match occurrence with
    | .left _ _ => 0
    | .right left right => generator (left, right)

/-- Boundary in the second factor of the `0 × 2` axis. -/
def leftOuterBoundary :
    Current (SphereSimplex 0 × SphereSimplex 2) →ₗ[ℚ]
      Current (SphereSimplex 0 × SphereSimplex 1) :=
  mapPairRight (sphereCurrentBoundary 1)

/-- Boundary in the first factor of the `1 × 1` axis. -/
def middleFirstBoundary :
    Current (SphereSimplex 1 × SphereSimplex 1) →ₗ[ℚ]
      Current (SphereSimplex 0 × SphereSimplex 1) :=
  mapPairLeft (sphereCurrentBoundary 0)

/-- Boundary in the second factor of the `1 × 1` axis, before the Koszul minus sign. -/
def middleSecondBoundary :
    Current (SphereSimplex 1 × SphereSimplex 1) →ₗ[ℚ]
      Current (SphereSimplex 1 × SphereSimplex 0) :=
  mapPairRight (sphereCurrentBoundary 0)

/-- Boundary in the first factor of the `2 × 0` axis. -/
def rightOuterBoundary :
    Current (SphereSimplex 2 × SphereSimplex 0) →ₗ[ℚ]
      Current (SphereSimplex 1 × SphereSimplex 0) :=
  mapPairLeft (sphereCurrentBoundary 1)

@[simp]
theorem leftAxisProjection_generator
    (occurrence : TotalTwoOccurrence SphereSSet SphereSSet) :
    leftAxisProjection (generator occurrence) = match occurrence with
      | .left left right => generator (left, right)
      | .middle _ _ => 0
      | .right _ _ => 0 := by
  exact extend_generator _ _

@[simp]
theorem middleAxisProjection_generator
    (occurrence : TotalTwoOccurrence SphereSSet SphereSSet) :
    middleAxisProjection (generator occurrence) = match occurrence with
      | .left _ _ => 0
      | .middle left right => generator (left, right)
      | .right _ _ => 0 := by
  exact extend_generator _ _

@[simp]
theorem rightAxisProjection_generator
    (occurrence : TotalTwoOccurrence SphereSSet SphereSSet) :
    rightAxisProjection (generator occurrence) = match occurrence with
      | .left _ _ => 0
      | .middle _ _ => 0
      | .right left right => generator (left, right) := by
  exact extend_generator _ _

@[simp]
theorem leftOneAxisProjection_generator
    (occurrence : TotalOneOccurrence SphereSSet SphereSSet) :
    leftOneAxisProjection (generator occurrence) = match occurrence with
      | .left left right => generator (left, right)
      | .right _ _ => 0 := by
  exact extend_generator _ _

@[simp]
theorem rightOneAxisProjection_generator
    (occurrence : TotalOneOccurrence SphereSSet SphereSSet) :
    rightOneAxisProjection (generator occurrence) = match occurrence with
      | .left _ _ => 0
      | .right left right => generator (left, right) := by
  exact extend_generator _ _

/-- [proved-derived; formal-checked] Every separated total-degree-two current is reconstructed
exactly from its three addressed axes. -/
theorem totalTwoAxisReconstruction
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) :
    leftAxis (leftAxisProjection current) +
        middleAxis (middleAxisProjection current) +
      rightAxis (rightAxisProjection current) = current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add current₁ current₂ hcurrent₁ hcurrent₂ =>
      simp only [map_add]
      calc
        _ = (leftAxis (leftAxisProjection current₁) +
                middleAxis (middleAxisProjection current₁) +
              rightAxis (rightAxisProjection current₁)) +
            (leftAxis (leftAxisProjection current₂) +
                middleAxis (middleAxisProjection current₂) +
              rightAxis (rightAxisProjection current₂)) := by module
        _ = current₁ + current₂ := by rw [hcurrent₁, hcurrent₂]
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul]
      cases occurrence <;> simp

/-- [proved-derived; formal-checked] The left total-degree-one boundary receiver exposes the
coupled `0 × 2` and first-factor `1 × 1` equation. -/
theorem leftOneAxisProjection_totalBoundaryTwo
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) :
    leftOneAxisProjection
        (totalBoundaryTwo SphereSSet SphereSSet current) =
      leftOuterBoundary (leftAxisProjection current) +
        middleFirstBoundary (middleAxisProjection current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul]
      cases occurrence <;>
        simp [totalBoundaryTwo, totalBoundaryTwoAtom, leftOuterBoundary,
          middleFirstBoundary, sphereCurrentBoundary,
          sphereCurrentBoundaryAtom,
          HodgeTwoSphereFundamentalCycle.simplexFace, face,
          Fin.sum_univ_two, Fin.sum_univ_three] <;>
        module

/-- [proved-derived; formal-checked] The right total-degree-one boundary receiver exposes the
Koszul-signed second-factor `1 × 1` term and the `2 × 0` boundary. -/
theorem rightOneAxisProjection_totalBoundaryTwo
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) :
    rightOneAxisProjection
        (totalBoundaryTwo SphereSSet SphereSSet current) =
      -middleSecondBoundary (middleAxisProjection current) +
        rightOuterBoundary (rightAxisProjection current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul]
      cases occurrence <;>
        simp [totalBoundaryTwo, totalBoundaryTwoAtom, middleSecondBoundary,
          rightOuterBoundary, sphereCurrentBoundary,
          sphereCurrentBoundaryAtom,
          HodgeTwoSphereFundamentalCycle.simplexFace, face,
          Fin.sum_univ_two, Fin.sum_univ_three] <;>
        module

/-- [proved-derived; formal-checked] Closure of a separated total two-current returns the two
coupled component equations; no individual axis closure is assumed. -/
theorem coupledAxisBoundaryEquations
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet))
    (closed : totalBoundaryTwo SphereSSet SphereSSet current = 0) :
    leftOuterBoundary (leftAxisProjection current) +
          middleFirstBoundary (middleAxisProjection current) = 0 ∧
      -middleSecondBoundary (middleAxisProjection current) +
          rightOuterBoundary (rightAxisProjection current) = 0 := by
  constructor
  · rw [← leftOneAxisProjection_totalBoundaryTwo, closed, map_zero]
  · rw [← rightOneAxisProjection_totalBoundaryTwo, closed, map_zero]

/-- Pair one two-chain with one one-chain in the `2 × 1` degree-three axis. -/
def rightMiddleCurrent (left : SphereChain 2) (right : SphereChain 1) :
    Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  rightMiddleAxis
    (pairCurrent (sphereChainToCurrent 2 left) (sphereChainToCurrent 1 right))

/-- Pair one one-chain with one two-chain in the distinct `1 × 2` degree-three axis. -/
def leftMiddleCurrent (left : SphereChain 1) (right : SphereChain 2) :
    Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  leftMiddleAxis
    (pairCurrent (sphereChainToCurrent 1 left) (sphereChainToCurrent 2 right))

/-- Pair two one-chains in the retained `1 × 1` interaction axis. -/
def mixedCurrent (left right : SphereChain 1) :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  middleAxis
    (pairCurrent (sphereChainToCurrent 1 left) (sphereChainToCurrent 1 right))

def rightCurrent (left : SphereChain 2) (right : SphereChain 0) :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  rightAxis
    (pairCurrent (sphereChainToCurrent 2 left) (sphereChainToCurrent 0 right))

@[simp]
theorem simplexFace_eq_face {degree : ℕ} (i : Fin (degree + 2))
    (simplex : SphereSimplex (degree + 1)) :
    HodgeTwoSphereFundamentalCycle.simplexFace i simplex = face i simplex := by
  rfl

theorem totalBoundaryThree_rightMiddle_generators
    (left : SphereSimplex 2) (right : SphereSimplex 1) :
    totalBoundaryThree SphereSSet SphereSSet
        (rightMiddleAxis (pairCurrent (generator left) (generator right))) =
      middleAxis (pairCurrent (sphereCurrentBoundary 1 (generator left))
        (generator right)) +
      rightAxis (pairCurrent (generator left)
        (sphereCurrentBoundary 0 (generator right))) := by
  simp only [pairCurrent_generator, rightMiddleAxis_generator,
    totalBoundaryThree, extend_generator, totalBoundaryThreeAtom,
    sphereCurrentBoundary_generator, sphereCurrentBoundaryAtom]
  rw [Fin.sum_univ_three, Fin.sum_univ_two]
  norm_num
  module

theorem totalBoundaryThree_leftMiddle_generators
    (left : SphereSimplex 1) (right : SphereSimplex 2) :
    totalBoundaryThree SphereSSet SphereSSet
        (leftMiddleAxis (pairCurrent (generator left) (generator right))) =
      leftAxis (pairCurrent (sphereCurrentBoundary 0 (generator left))
        (generator right)) -
      middleAxis (pairCurrent (generator left)
        (sphereCurrentBoundary 1 (generator right))) := by
  simp only [pairCurrent_generator, leftMiddleAxis_generator,
    totalBoundaryThree, extend_generator, totalBoundaryThreeAtom,
    sphereCurrentBoundary_generator, sphereCurrentBoundaryAtom]
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num
  module

/-- [proved-derived; formal-checked] Leibniz boundary on an arbitrary retained `1 × 2`
occurrence current. -/
theorem totalBoundaryThree_leftMiddleAxis
    (current : Current (SphereSimplex 1 × SphereSimplex 2)) :
    totalBoundaryThree SphereSSet SphereSSet (leftMiddleAxis current) =
      leftAxis (mapPairLeft (sphereCurrentBoundary 0) current) -
        middleAxis (mapPairRight (sphereCurrentBoundary 1) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, leftMiddleAxis_generator,
        mapPairLeft_generator, mapPairRight_generator]
      have generatorLaw := totalBoundaryThree_leftMiddle_generators left right
      simp only [pairCurrent_generator, leftMiddleAxis_generator] at generatorLaw
      rw [generatorLaw]
      module

/-- [proved-derived; formal-checked] Leibniz boundary on an arbitrary retained `2 × 1`
occurrence current. -/
theorem totalBoundaryThree_rightMiddleAxis
    (current : Current (SphereSimplex 2 × SphereSimplex 1)) :
    totalBoundaryThree SphereSSet SphereSSet (rightMiddleAxis current) =
      middleAxis (mapPairLeft (sphereCurrentBoundary 1) current) +
        rightAxis (mapPairRight (sphereCurrentBoundary 0) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, rightMiddleAxis_generator,
        mapPairLeft_generator, mapPairRight_generator]
      have generatorLaw := totalBoundaryThree_rightMiddle_generators left right
      simp only [pairCurrent_generator, rightMiddleAxis_generator] at generatorLaw
      rw [generatorLaw]
      module

/-- [proved-derived; formal-checked] Boundary on the `0 × 3` endpoint axis is the retained
second-incidence sphere boundary. -/
theorem totalBoundaryThree_zeroThreeAxis
    (current : Current (SphereSimplex 0 × SphereSimplex 3)) :
    totalBoundaryThree SphereSSet SphereSSet (zeroThreeAxis current) =
      leftAxis (mapPairRight (sphereCurrentBoundary 2) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, zeroThreeAxis_generator, mapPairRight_generator]
      simp [totalBoundaryThree, totalBoundaryThreeAtom,
        sphereCurrentBoundary, sphereCurrentBoundaryAtom,
        leftAxis, Fin.sum_univ_four]
      module

/-- [proved-derived; formal-checked] The `3 × 0` endpoint boundary is obtained solely by the
graded polarity involution. -/
theorem totalBoundaryThree_threeZeroAxis
    (current : Current (SphereSimplex 3 × SphereSimplex 0)) :
    totalBoundaryThree SphereSSet SphereSSet (threeZeroAxis current) =
      rightAxis (mapPairLeft (sphereCurrentBoundary 2) current) := by
  rw [threeZeroAxis, LinearMap.comp_apply, LinearMap.comp_apply,
    totalBoundaryThree_flip, totalBoundaryThree_zeroThreeAxis,
    mapPairRight_flipPair, totalTwoFlip_leftAxis, flipPair_involutive]

/-! ## One coupled correction for the polarized outer axes

The mixed `1 × 1` current is removed once.  Its two returned boundary currents are not treated
as independent left/right cases: the second correction is the reorientation needed to cancel the
basepoint residue of the first. -/

/-- [definition] Contract the presented degree-one incidence of the mixed current. -/
def rightMiddleContraction
    (current : Current (SphereSimplex 1 × SphereSimplex 1)) :
    Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  rightMiddleAxis (mapPairLeft sphereOneContraction current)

/-- [definition] Return the exact opposite-orientation correction forced by the first boundary
of the mixed current. -/
def leftMiddleCorrection
    (current : Current (SphereSimplex 1 × SphereSimplex 1)) :
    Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  leftMiddleAxis
    (mapPairLeft sphereZeroContraction
      (mapPairRight sphereOneContraction
        (mapPairLeft (sphereCurrentBoundary 0) current)))

/-- [definition] The single polarized degree-three current which removes the coupled middle
axis and returns one correction to each outer axis. -/
def coupledMiddleCorrection
    (current : Current (SphereSimplex 1 × SphereSimplex 1)) :
    Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  rightMiddleContraction current - leftMiddleCorrection current

/-- [proved-derived; formal-checked] Boundary of the first oriented contraction.  Both returned
faces are retained: the residual mixed basepoint current and the opposite outer correction. -/
theorem rightMiddleContraction_boundary
    (current : Current (SphereSimplex 1 × SphereSimplex 1)) :
    totalBoundaryThree SphereSSet SphereSSet
        (rightMiddleContraction current) =
      middleAxis
          (current -
            mapPairLeft sphereZeroContraction
              (mapPairLeft (sphereCurrentBoundary 0) current)) +
        rightAxis
          (mapPairLeft sphereOneContraction
            (mapPairRight (sphereCurrentBoundary 0) current)) := by
  rw [rightMiddleContraction, totalBoundaryThree_rightMiddleAxis,
    mapPairLeft_sphereOneContraction_boundary]
  rw [← mapPairLeft_right_commute]

/-- [proved-derived; formal-checked] The opposite correction returns exactly the first outer
current and the mixed basepoint current when the first returned boundary is closed. -/
theorem leftMiddleCorrection_boundary
    (current : Current (SphereSimplex 1 × SphereSimplex 1))
    (firstBoundaryClosed :
      mapPairRight (sphereCurrentBoundary 0)
          (mapPairLeft (sphereCurrentBoundary 0) current) = 0) :
    totalBoundaryThree SphereSSet SphereSSet
        (leftMiddleCorrection current) =
      leftAxis
          (mapPairRight sphereOneContraction
            (mapPairLeft (sphereCurrentBoundary 0) current)) -
        middleAxis
          (mapPairLeft sphereZeroContraction
            (mapPairLeft (sphereCurrentBoundary 0) current)) := by
  let firstBoundary :=
    mapPairLeft (sphereCurrentBoundary 0) current
  have firstAugmentation : pairFirstAugmentation firstBoundary = 0 := by
    exact pairFirstAugmentation_mapPairLeft_boundary current
  have liftedAugmentation :
      pairFirstAugmentation
          (mapPairRight sphereOneContraction firstBoundary) = 0 := by
    rw [pairFirstAugmentation_mapPairRight, firstAugmentation, map_zero]
  rw [leftMiddleCorrection, totalBoundaryThree_leftMiddleAxis]
  change leftAxis
      (mapPairLeft (sphereCurrentBoundary 0)
        (mapPairLeft sphereZeroContraction
          (mapPairRight sphereOneContraction firstBoundary))) -
    middleAxis
      (mapPairRight (sphereCurrentBoundary 1)
        (mapPairLeft sphereZeroContraction
          (mapPairRight sphereOneContraction firstBoundary))) = _
  rw [mapPairLeft_sphereZeroContraction_boundary,
    liftedAugmentation, map_zero, sub_zero]
  have commuteOuter :
      mapPairRight (sphereCurrentBoundary 1)
          (mapPairLeft sphereZeroContraction
            (mapPairRight sphereOneContraction firstBoundary)) =
        mapPairLeft sphereZeroContraction
          (mapPairRight (sphereCurrentBoundary 1)
            (mapPairRight sphereOneContraction firstBoundary)) := by
    exact (mapPairLeft_right_commute sphereZeroContraction
      (sphereCurrentBoundary 1)
      (mapPairRight sphereOneContraction firstBoundary)).symm
  rw [commuteOuter]
  rw [mapPairRight_sphereOneContraction_boundary,
    firstBoundaryClosed]
  simp [firstBoundary]

/-- [proved-derived; formal-checked] One polarized correction removes the complete mixed current.
The returned outer terms are exact, signed, and still carry their source incidence currents. -/
theorem coupledMiddleCorrection_boundary
    (current : Current (SphereSimplex 1 × SphereSimplex 1))
    (firstBoundaryClosed :
      mapPairRight (sphereCurrentBoundary 0)
          (mapPairLeft (sphereCurrentBoundary 0) current) = 0) :
    totalBoundaryThree SphereSSet SphereSSet
        (coupledMiddleCorrection current) =
      middleAxis current +
          rightAxis
            (mapPairLeft sphereOneContraction
              (mapPairRight (sphereCurrentBoundary 0) current)) -
        leftAxis
          (mapPairRight sphereOneContraction
            (mapPairLeft (sphereCurrentBoundary 0) current)) := by
  rw [coupledMiddleCorrection, map_sub,
    rightMiddleContraction_boundary,
    leftMiddleCorrection_boundary current firstBoundaryClosed]
  simp only [map_sub]
  module

/-- [proved-derived; formal-checked] Closure of the complete three-axis current forces the first
returned mixed boundary to be closed in the opposite incidence. -/
theorem mixedFirstBoundary_closed_of_totalBoundary
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet))
    (closed : totalBoundaryTwo SphereSSet SphereSSet current = 0) :
    mapPairRight (sphereCurrentBoundary 0)
        (mapPairLeft (sphereCurrentBoundary 0)
          (middleAxisProjection current)) = 0 := by
  have equation := (coupledAxisBoundaryEquations current closed).1
  change mapPairRight (sphereCurrentBoundary 1)
      (leftAxisProjection current) +
    mapPairLeft (sphereCurrentBoundary 0)
      (middleAxisProjection current) = 0 at equation
  have returnedBoundary :
      mapPairLeft (sphereCurrentBoundary 0)
          (middleAxisProjection current) =
        -mapPairRight (sphereCurrentBoundary 1)
          (leftAxisProjection current) := by
    exact eq_neg_of_add_eq_zero_right equation
  rw [returnedBoundary, map_neg,
    mapPairRight_sphereBoundary_sq, neg_zero]

/-- [proved-derived; formal-checked] The opposite returned mixed boundary is closed in the
presented incidence by the same total closure law. -/
theorem mixedSecondBoundary_closed_of_totalBoundary
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet))
    (closed : totalBoundaryTwo SphereSSet SphereSSet current = 0) :
    mapPairLeft (sphereCurrentBoundary 0)
        (mapPairRight (sphereCurrentBoundary 0)
          (middleAxisProjection current)) = 0 := by
  have equation := (coupledAxisBoundaryEquations current closed).2
  change -mapPairRight (sphereCurrentBoundary 0)
      (middleAxisProjection current) +
    mapPairLeft (sphereCurrentBoundary 1)
      (rightAxisProjection current) = 0 at equation
  have returnedBoundary :
      mapPairRight (sphereCurrentBoundary 0)
          (middleAxisProjection current) =
        mapPairLeft (sphereCurrentBoundary 1)
          (rightAxisProjection current) := by
    have reversed := eq_neg_of_add_eq_zero_right equation
    simpa using reversed.symm
  rw [returnedBoundary, mapPairLeft_sphereBoundary_sq]

/-- [definition] The first outer current after the one coupled middle correction. -/
def correctedFirstOuter
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) :
    Current (SphereSimplex 0 × SphereSimplex 2) :=
  leftAxisProjection current +
    mapPairRight sphereOneContraction
      (mapPairLeft (sphereCurrentBoundary 0)
        (middleAxisProjection current))

/-- [definition] The oppositely oriented outer current after the same correction. -/
def correctedSecondOuter
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet)) :
    Current (SphereSimplex 2 × SphereSimplex 0) :=
  rightAxisProjection current -
    mapPairLeft sphereOneContraction
      (mapPairRight (sphereCurrentBoundary 0)
        (middleAxisProjection current))

/-- [proved-derived; formal-checked] The corrected `0 × 2` outer current is closed. -/
theorem correctedFirstOuter_closed
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet))
    (closed : totalBoundaryTwo SphereSSet SphereSSet current = 0) :
    mapPairRight (sphereCurrentBoundary 1)
        (correctedFirstOuter current) = 0 := by
  have equation := (coupledAxisBoundaryEquations current closed).1
  have returnedClosed := mixedFirstBoundary_closed_of_totalBoundary current closed
  rw [correctedFirstOuter, map_add,
    mapPairRight_sphereOneContraction_boundary,
    returnedClosed]
  simpa [leftOuterBoundary, middleFirstBoundary] using equation

/-- [proved-derived; formal-checked] The corrected `2 × 0` outer current is closed. -/
theorem correctedSecondOuter_closed
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet))
    (closed : totalBoundaryTwo SphereSSet SphereSSet current = 0) :
    mapPairLeft (sphereCurrentBoundary 1)
        (correctedSecondOuter current) = 0 := by
  have equation := (coupledAxisBoundaryEquations current closed).2
  have returnedClosed := mixedSecondBoundary_closed_of_totalBoundary current closed
  rw [correctedSecondOuter, map_sub,
    mapPairLeft_sphereOneContraction_boundary,
    returnedClosed]
  change -mapPairRight (sphereCurrentBoundary 0)
      (middleAxisProjection current) +
    mapPairLeft (sphereCurrentBoundary 1)
      (rightAxisProjection current) = 0 at equation
  simpa [sub_eq_add_neg, add_comm] using equation

/-- [proved-derived; formal-checked] Every closed total-degree-two current differs from two
individually closed outer currents by the boundary of the single polarized middle correction. -/
theorem coupledMiddleCorrection_reduces_to_outer
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet))
    (closed : totalBoundaryTwo SphereSSet SphereSSet current = 0) :
    current -
        totalBoundaryThree SphereSSet SphereSSet
          (coupledMiddleCorrection (middleAxisProjection current)) =
      leftAxis (correctedFirstOuter current) +
        rightAxis (correctedSecondOuter current) := by
  have returnedClosed := mixedFirstBoundary_closed_of_totalBoundary current closed
  rw [coupledMiddleCorrection_boundary _ returnedClosed]
  nth_rewrite 1 [← totalTwoAxisReconstruction current]
  simp only [correctedFirstOuter, correctedSecondOuter, map_add, map_sub]
  module

/-! ## Reduction of one outer axis; the opposite axis is obtained by graded polarity -/

/-- [definition] The sphere fundamental cycle in the finite-current chart. -/
def sphereFundamentalCurrent : Current (SphereSimplex 2) :=
  sphereChainToCurrent 2
    HodgeTwoSphereFundamentalCycle.sphereFundamentalCandidate

/-- [definition] The separated current of the geometric second ruling (`point × S²`). -/
def secondRulingSeparatedCurrent :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  leftAxis (pairFirstBase sphereFundamentalCurrent)

/-- [definition] The separated current of the opposite ruling, derived by graded polarity. -/
def firstRulingSeparatedCurrent :
    Current (TotalTwoOccurrence SphereSSet SphereSSet) :=
  totalTwoFlip secondRulingSeparatedCurrent

/-- [definition] Contract the degree-zero presented incidence of a closed `0 × 2` current. -/
def firstOuterZeroCorrection
    (current : Current (SphereSimplex 0 × SphereSimplex 2)) :
    Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
  leftMiddleAxis (mapPairLeft sphereZeroContraction current)

/-- [proved-derived; formal-checked] The degree-zero correction reduces one closed outer current
to its exact basepoint fibre. -/
theorem firstOuterZeroCorrection_boundary
    (current : Current (SphereSimplex 0 × SphereSimplex 2))
    (closed : mapPairRight (sphereCurrentBoundary 1) current = 0) :
    totalBoundaryThree SphereSSet SphereSSet
        (firstOuterZeroCorrection current) =
      leftAxis
        (current - pairFirstBase (pairFirstAugmentation current)) := by
  rw [firstOuterZeroCorrection, totalBoundaryThree_leftMiddleAxis,
    mapPairLeft_sphereZeroContraction_boundary]
  have commuteBoundary :
      mapPairRight (sphereCurrentBoundary 1)
          (mapPairLeft sphereZeroContraction current) =
        mapPairLeft sphereZeroContraction
          (mapPairRight (sphereCurrentBoundary 1) current) := by
    exact (mapPairLeft_right_commute sphereZeroContraction
      (sphereCurrentBoundary 1) current).symm
  rw [commuteBoundary, closed, map_zero, map_zero, sub_zero]

/-- [proved-derived; formal-checked] Closedness transports from a finite sphere two-current to
the genuine categorical singular-chain chart. -/
theorem sphereCurrentToChain_two_closed
    (current : Current (SphereSimplex 2))
    (closed : sphereCurrentBoundary 1 current = 0) :
    HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 2 1
        (sphereCurrentToChain 2 current) = 0 := by
  apply (sphereChainEquivCurrent 1).injective
  change sphereChainToCurrent 1
      (HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 2 1
        (sphereCurrentToChain 2 current)) = sphereChainToCurrent 1 0
  rw [sphereChainToCurrent_boundary, sphereChain_current_roundtrip,
    closed, map_zero]

/-- [proved-derived; formal-checked] Every closed `0 × 2` current is homologous, by an actual
four-axis degree-three current, to one rational multiple of the second ruling current. -/
theorem exists_firstOuterFundamentalReduction
    (current : Current (SphereSimplex 0 × SphereSimplex 2))
    (closed : mapPairRight (sphereCurrentBoundary 1) current = 0) :
    ∃ coefficient : ℚ,
      ∃ filling : Current (TotalThreeOccurrence SphereSSet SphereSSet),
        totalBoundaryThree SphereSSet SphereSSet filling =
          leftAxis current - coefficient • secondRulingSeparatedCurrent := by
  let collapsed := pairFirstAugmentation current
  have collapsedClosed : sphereCurrentBoundary 1 collapsed = 0 := by
    rw [← pairFirstAugmentation_mapPairRight
      (sphereCurrentBoundary 1) current, closed, map_zero]
  let collapsedChain := sphereCurrentToChain 2 collapsed
  have collapsedChainClosed :
      HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 2 1
        collapsedChain = 0 := by
    exact sphereCurrentToChain_two_closed collapsed collapsedClosed
  obtain ⟨lebesgue⟩ :=
    Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling.exists_starLebesgueLabel
  obtain ⟨sphereFilling, coefficient, sphereBoundary⟩ :=
    Soma.Holonics.Millennium.HodgeCommonStarNormalization.exists_commonStarReduction_to_fundamental
      collapsedChain lebesgue collapsedChainClosed
  have sphereCurrentBoundaryLaw :
      sphereCurrentBoundary 2 (sphereChainToCurrent 3 (-sphereFilling)) =
        collapsed - coefficient • sphereFundamentalCurrent := by
    rw [← sphereChainToCurrent_boundary, map_neg, sphereBoundary]
    change (sphereChainEquivCurrent 2)
        (-(coefficient •
            HodgeTwoSphereFundamentalCycle.sphereFundamentalCandidate -
          collapsedChain)) =
      collapsed - coefficient • sphereFundamentalCurrent
    rw [map_neg, map_sub, map_smul]
    rw [show (sphereChainEquivCurrent 2) collapsedChain = collapsed by
      exact sphereChain_current_roundtrip 2 collapsed]
    change -(coefficient • sphereFundamentalCurrent - collapsed) =
      collapsed - coefficient • sphereFundamentalCurrent
    module
  let liftedSphereFilling :
      Current (TotalThreeOccurrence SphereSSet SphereSSet) :=
    zeroThreeAxis
      (pairCurrent (generator rulingBasepointSimplex)
        (sphereChainToCurrent 3 (-sphereFilling)))
  refine ⟨coefficient,
    firstOuterZeroCorrection current + liftedSphereFilling, ?_⟩
  rw [map_add, firstOuterZeroCorrection_boundary current closed]
  change _ + totalBoundaryThree SphereSSet SphereSSet
      (zeroThreeAxis
        (pairCurrent (generator rulingBasepointSimplex)
          (sphereChainToCurrent 3 (-sphereFilling)))) = _
  rw [totalBoundaryThree_zeroThreeAxis,
    mapPairRight_pairCurrent, sphereCurrentBoundaryLaw]
  rw [pairCurrent_sub_right, pairCurrent_smul_right,
    pairFirstBase_current]
  simp only [secondRulingSeparatedCurrent]
  rw [pairFirstBase_current]
  simp only [map_sub, map_smul]
  dsimp [collapsed]
  module

/-- [proved-derived; formal-checked] The opposite outer reduction is not re-proved.  It is the
graded factor reversal of the first reduction, including its complete degree-three witness. -/
theorem exists_secondOuterFundamentalReduction
    (current : Current (SphereSimplex 2 × SphereSimplex 0))
    (closed : mapPairLeft (sphereCurrentBoundary 1) current = 0) :
    ∃ coefficient : ℚ,
      ∃ filling : Current (TotalThreeOccurrence SphereSSet SphereSSet),
        totalBoundaryThree SphereSSet SphereSSet filling =
          rightAxis current - coefficient • firstRulingSeparatedCurrent := by
  have flippedClosed :
      mapPairRight (sphereCurrentBoundary 1) (flipPair current) = 0 := by
    rw [mapPairRight_flipPair, closed, map_zero]
  obtain ⟨coefficient, filling, boundary⟩ :=
    exists_firstOuterFundamentalReduction (flipPair current) flippedClosed
  refine ⟨coefficient, totalThreeFlip filling, ?_⟩
  rw [totalBoundaryThree_flip, boundary, map_sub, map_smul,
    totalTwoFlip_leftAxis, flipPair_involutive]
  rfl

/-- [proved-derived; formal-checked] Every closed separated total-degree-two current has an exact
two-ruling decomposition with one complete degree-three reconstruction current. -/
theorem exists_closedTotalRulingReduction
    (current : Current (TotalTwoOccurrence SphereSSet SphereSSet))
    (closed : totalBoundaryTwo SphereSSet SphereSSet current = 0) :
    ∃ coefficients : Bidegree,
      ∃ filling : Current (TotalThreeOccurrence SphereSSet SphereSSet),
        totalBoundaryThree SphereSSet SphereSSet filling =
          current -
            (coefficients 0 • firstRulingSeparatedCurrent +
              coefficients 1 • secondRulingSeparatedCurrent) := by
  let firstOuter := correctedFirstOuter current
  let secondOuter := correctedSecondOuter current
  have firstOuterClosed :
      mapPairRight (sphereCurrentBoundary 1) firstOuter = 0 := by
    exact correctedFirstOuter_closed current closed
  have secondOuterClosed :
      mapPairLeft (sphereCurrentBoundary 1) secondOuter = 0 := by
    exact correctedSecondOuter_closed current closed
  obtain ⟨secondCoefficient, firstFilling, firstBoundary⟩ :=
    exists_firstOuterFundamentalReduction firstOuter firstOuterClosed
  obtain ⟨firstCoefficient, secondFilling, secondBoundary⟩ :=
    exists_secondOuterFundamentalReduction secondOuter secondOuterClosed
  let coefficients : Bidegree :=
    firstCoefficient • firstFibre + secondCoefficient • secondFibre
  have coefficientFirst : coefficients 0 = firstCoefficient := by
    simp [coefficients, firstFibre, secondFibre]
  have coefficientSecond : coefficients 1 = secondCoefficient := by
    simp [coefficients, firstFibre, secondFibre]
  let middleFilling :=
    coupledMiddleCorrection (middleAxisProjection current)
  have middleBoundary := coupledMiddleCorrection_reduces_to_outer current closed
  refine ⟨coefficients, middleFilling + firstFilling + secondFilling, ?_⟩
  rw [map_add, map_add, firstBoundary, secondBoundary,
    coefficientFirst, coefficientSecond]
  change current -
      totalBoundaryThree SphereSSet SphereSSet middleFilling =
    leftAxis firstOuter + rightAxis secondOuter at middleBoundary
  have reconstructed :
      totalBoundaryThree SphereSSet SphereSSet middleFilling +
          leftAxis firstOuter + rightAxis secondOuter = current := by
    calc
      _ = totalBoundaryThree SphereSSet SphereSSet middleFilling +
          (leftAxis firstOuter + rightAxis secondOuter) := by module
      _ = totalBoundaryThree SphereSSet SphereSSet middleFilling +
          (current -
            totalBoundaryThree SphereSSet SphereSSet middleFilling) := by
              rw [← middleBoundary]
      _ = current := by module
  calc
    _ = (totalBoundaryThree SphereSSet SphereSSet middleFilling +
          leftAxis firstOuter + rightAxis secondOuter) -
        (firstCoefficient • firstRulingSeparatedCurrent +
          secondCoefficient • secondRulingSeparatedCurrent) := by module
    _ = _ := by rw [reconstructed]

/-- [proved-derived; formal-checked] The actual chain boundary on a `2 × 1` interaction obeys
the exact signed product rule and retains both returned axes. -/
theorem totalBoundaryThree_rightMiddleCurrent
    (left : SphereChain 2) (right : SphereChain 1) :
    totalBoundaryThree SphereSSet SphereSSet (rightMiddleCurrent left right) =
      mixedCurrent
          (HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 2 1 left) right +
        rightCurrent left
          (HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 1 0 right) := by
  rw [rightMiddleCurrent, mixedCurrent, rightCurrent,
    totalBoundaryThree_rightMiddleAxis,
    mapPairLeft_pairCurrent, mapPairRight_pairCurrent,
    sphereChainToCurrent_boundary, sphereChainToCurrent_boundary]

/-- [proved-derived; formal-checked] The actual chain boundary on a `1 × 2` interaction obeys
the exact signed product rule and retains both returned axes. -/
theorem totalBoundaryThree_leftMiddleCurrent
    (left : SphereChain 1) (right : SphereChain 2) :
    totalBoundaryThree SphereSSet SphereSSet (leftMiddleCurrent left right) =
      leftAxis (pairCurrent
        (sphereChainToCurrent 0
          (HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 1 0 left))
        (sphereChainToCurrent 2 right)) -
      mixedCurrent left
        (HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 2 1 right) := by
  rw [leftMiddleCurrent, mixedCurrent,
    totalBoundaryThree_leftMiddleAxis,
    mapPairLeft_pairCurrent, mapPairRight_pairCurrent,
    sphereChainToCurrent_boundary, sphereChainToCurrent_boundary]

/-- [proved-derived; formal-checked] Every decomposable `1 × 1` current formed from two closed
sphere one-currents has an explicit separated degree-three filling. -/
theorem exists_mixedCurrentFilling
    (left right : SphereChain 1)
    (leftClosed :
      HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 1 0 left = 0)
    (rightClosed :
      HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex.d 1 0 right = 0) :
    ∃ filling : Current (TotalThreeOccurrence SphereSSet SphereSSet),
      totalBoundaryThree SphereSSet SphereSSet filling = mixedCurrent left right := by
  obtain ⟨leftFilling, leftBoundary⟩ :=
    HodgeSphereDegreeOneFilling.exists_sphereDegreeOneFilling left leftClosed
  refine ⟨rightMiddleCurrent leftFilling right, ?_⟩
  rw [totalBoundaryThree_rightMiddleCurrent, leftBoundary, rightClosed]
  simp [rightCurrent, pairCurrent_zero_right]

section Audit

#print axioms spherePairDiagonalH0_boundary
#print axioms spherePairDiagonalH1_boundary
#print axioms totalBoundaryThree_rightMiddleCurrent
#print axioms exists_mixedCurrentFilling

end Audit

end Soma.Holonics.Millennium.HodgeProductMixedFilling
