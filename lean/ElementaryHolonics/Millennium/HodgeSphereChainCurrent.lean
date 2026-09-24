import ElementaryHolonics.Foundation.DiagonalChainTransport
import ElementaryHolonics.Millennium.HodgeSphereDegreeOneFilling

/-!
# Rational sphere chains as exact finite occurrence currents

The categorical singular-chain coproduct and the free finite current on addressed sphere
simplices are the same carrier.  This file records both directions as one linear equivalence.
It is the common chart needed to apply the degree-one sphere filling theorem coefficientwise in
the separated `1 × 1` axis of the sphere product.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSphereChainCurrent

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Soma.Holonics.DiagonalChainTransport
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly

abbrev SphereSSet : SSet := TopCat.toSSet.obj sphereTopCat

abbrev SphereSimplex (degree : ℕ) := Simplex SphereSSet degree

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

def sphereCurrentCoefficient {degree : ℕ} (simplex : SphereSimplex degree) :
    rationalCoefficient ⟶ ModuleCat.of ℚ (Current (SphereSimplex degree)) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ (generator simplex))

/-- Read the categorical singular coproduct as its complete finite occurrence current. -/
def sphereChainToCurrentMorphism (degree : ℕ) :
    SphereSingularChainComplex.X degree ⟶
      ModuleCat.of ℚ (Current (SphereSimplex degree)) :=
  Limits.Sigma.desc fun simplex => sphereCurrentCoefficient simplex

def sphereChainToCurrent (degree : ℕ) :
    SphereChain degree →ₗ[ℚ] Current (SphereSimplex degree) :=
  (sphereChainToCurrentMorphism degree).hom

/-- Reconstruct the categorical chain from every retained addressed occurrence. -/
def sphereCurrentToChain (degree : ℕ) :
    Current (SphereSimplex degree) →ₗ[ℚ] SphereChain degree :=
  Finsupp.linearCombination ℚ simplexGenerator

@[simp]
theorem sphereChainToCurrent_simplexGenerator {degree : ℕ}
    (simplex : SphereSimplex degree) :
    sphereChainToCurrent degree (simplexGenerator simplex) = generator simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSimplex degree => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => sphereCurrentCoefficient source)) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

@[simp]
theorem sphereCurrentToChain_generator {degree : ℕ}
    (simplex : SphereSimplex degree) :
    sphereCurrentToChain degree (generator simplex) = simplexGenerator simplex := by
  simp [sphereCurrentToChain, generator]

theorem sphereCurrent_chain_roundtrip (degree : ℕ) (chain : SphereChain degree) :
    sphereCurrentToChain degree (sphereChainToCurrent degree chain) = chain := by
  have composite_eq :
      sphereChainToCurrentMorphism degree ≫
          ModuleCat.ofHom (sphereCurrentToChain degree) =
        𝟙 (SphereSingularChainComplex.X degree) := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change sphereCurrentToChain degree
        (sphereChainToCurrent degree
          ((Limits.Sigma.ι
            (fun _ : SphereSimplex degree => rationalCoefficient) simplex) coefficient)) =
      (Limits.Sigma.ι (fun _ : SphereSimplex degree => rationalCoefficient) simplex)
        coefficient
    rw [sigmaInjection_eq_smul_simplexGenerator]
    simp only [map_smul, sphereChainToCurrent_simplexGenerator,
      sphereCurrentToChain_generator]
  exact congrArg (fun morphism => morphism chain) composite_eq

theorem sphereChain_current_roundtrip (degree : ℕ)
    (current : Current (SphereSimplex degree)) :
    sphereChainToCurrent degree (sphereCurrentToChain degree current) = current := by
  let composite : Current (SphereSimplex degree) →ₗ[ℚ]
      Current (SphereSimplex degree) :=
    (sphereChainToCurrent degree).comp (sphereCurrentToChain degree)
  have composite_eq : composite = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro simplex coefficient
    rw [show Finsupp.single simplex coefficient = coefficient • generator simplex by
      simp [generator]]
    simp only [composite, LinearMap.comp_apply, map_smul,
      sphereCurrentToChain_generator, sphereChainToCurrent_simplexGenerator,
      LinearMap.id_apply]
  exact LinearMap.congr_fun composite_eq current

/-- [proved-derived; formal-checked] The actual rational singular chain and its complete finite
addressed occurrence population are linearly equivalent in every degree. -/
def sphereChainEquivCurrent (degree : ℕ) :
    SphereChain degree ≃ₗ[ℚ] Current (SphereSimplex degree) where
  toLinearMap := sphereChainToCurrent degree
  invFun := sphereCurrentToChain degree
  left_inv := sphereCurrent_chain_roundtrip degree
  right_inv := sphereChain_current_roundtrip degree

/-- Alternating singular boundary in the finite-current chart. -/
def sphereCurrentBoundaryAtom {degree : ℕ} (simplex : SphereSimplex (degree + 1)) :
    Current (SphereSimplex degree) :=
  ∑ omitted : Fin (degree + 2), (-1 : ℚ) ^ (omitted : ℕ) •
    generator (simplexFace omitted simplex)

def sphereCurrentBoundary (degree : ℕ) :
    Current (SphereSimplex (degree + 1)) →ₗ[ℚ] Current (SphereSimplex degree) :=
  extend sphereCurrentBoundaryAtom

@[simp]
theorem sphereCurrentBoundary_generator {degree : ℕ}
    (simplex : SphereSimplex (degree + 1)) :
    sphereCurrentBoundary degree (generator simplex) =
      sphereCurrentBoundaryAtom simplex := by
  exact extend_generator sphereCurrentBoundaryAtom simplex

/-- [proved-derived; formal-checked] The change from categorical chains to finite occurrence
currents commutes with the genuine singular boundary in every degree. -/
theorem sphereChainToCurrent_boundary (degree : ℕ) (chain : SphereChain (degree + 1)) :
    sphereChainToCurrent degree
        (SphereSingularChainComplex.d (degree + 1) degree chain) =
      sphereCurrentBoundary degree (sphereChainToCurrent (degree + 1) chain) := by
  let left : SphereSingularChainComplex.X (degree + 1) ⟶
      ModuleCat.of ℚ (Current (SphereSimplex degree)) :=
    SphereSingularChainComplex.d (degree + 1) degree ≫
      sphereChainToCurrentMorphism degree
  let right : SphereSingularChainComplex.X (degree + 1) ⟶
      ModuleCat.of ℚ (Current (SphereSimplex degree)) :=
    sphereChainToCurrentMorphism (degree + 1) ≫
      ModuleCat.ofHom (sphereCurrentBoundary degree)
  have mapsEqual : left = right := by
    apply Limits.Sigma.hom_ext
    intro simplex
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    change sphereChainToCurrent degree
        (SphereSingularChainComplex.d (degree + 1) degree
          ((Limits.Sigma.ι
            (fun _ : SphereSimplex (degree + 1) => rationalCoefficient)
            simplex) coefficient)) =
      sphereCurrentBoundary degree
        (sphereChainToCurrent (degree + 1)
          ((Limits.Sigma.ι
            (fun _ : SphereSimplex (degree + 1) => rationalCoefficient)
            simplex) coefficient))
    rw [sigmaInjection_eq_smul_simplexGenerator]
    simp only [map_smul, boundary_simplexGenerator,
      sphereChainToCurrent_simplexGenerator, sphereCurrentBoundary_generator,
      sphereCurrentBoundaryAtom, map_sum]
  exact congrArg (fun morphism => morphism chain) mapsEqual

section Audit

#print axioms sphereChainEquivCurrent
#print axioms sphereChainToCurrent_boundary

end Audit

end Soma.Holonics.Millennium.HodgeSphereChainCurrent
