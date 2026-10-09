import CMActualDiagonalCartierData
import CMActualFixedStalkLength

/-! The actual product stalk, actual graph stalk map and diagonal germ.
The regular section is transported only through a native affine-stalk
localization. Its restriction to the graph is a separate obligation; no
ambient-regularity-under-pullback principle is used.

agent-inferred: establish the acting ambient ring and scalar map before
reading a Serre multiplicity. The existing actual quotient length is read
over that ring by the proved surjective graph stalk map. This external
helical pair receiver touches faces and placement, cell holonomy and tube;
helix, pair and tower thread remain attached. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

theorem affineSection_germ_regular {X : Scheme} (U : X.Opens)
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) (r : Γ(X, U))
    (hr : IsRegular r) : IsRegular ((X.presheaf.germ U x hx).hom r) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  change IsRegular (algebraMap Γ(X, U) (X.presheaf.stalk x) r)
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  exact IsLocalization.nonZeroDivisors_le_comap
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)
    (isRegular_iff_mem_nonZeroDivisors.mp hr)

theorem cmActualAmbientDiagonal_stalk_regular_principal (x : CMActualAmbientProduct) :
    ∃ (i : CMActualDiagonalAffineIndex) (hx : x ∈ cmActualDiagonalAffineOpen i),
      IsRegular ((CMActualAmbientProduct.presheaf.germ
        (cmActualDiagonalAffineOpen i) x hx).hom (cmActualDiagonalAffineEquation i)) ∧
      (cmComplexDiagonal.ker.ideal
        ⟨cmActualDiagonalAffineOpen i, cmActualDiagonalAffineOpen_isAffine i⟩).map
          (CMActualAmbientProduct.presheaf.germ (cmActualDiagonalAffineOpen i) x hx).hom =
        Ideal.span {((CMActualAmbientProduct.presheaf.germ
          (cmActualDiagonalAffineOpen i) x hx).hom (cmActualDiagonalAffineEquation i))} := by
  obtain ⟨i, hx⟩ := cmActualDiagonalAffineOpen_point_cover x
  refine ⟨i, hx, affineSection_germ_regular _
    (cmActualDiagonalAffineOpen_isAffine i) x hx _
    (cmActualDiagonalAffineEquation_regular i), ?_⟩
  rw [cmActualDiagonalAffineEquation_ideal, Ideal.map_span, Set.image_singleton]

abbrev cmActualYAmbientLocalRing :=
  CMActualAmbientProduct.presheaf.stalk (cmConcreteComplexGraph cmActualYOriginPoint)
abbrev cmActualZAmbientLocalRing :=
  CMActualAmbientProduct.presheaf.stalk (cmConcreteComplexGraph cmActualZOriginPoint)

@[instance_reducible]
def cmActualYGraphStalkAlgebra : Algebra cmActualYAmbientLocalRing cmActualYOriginLocalRing :=
  (cmConcreteComplexGraph.stalkMap cmActualYOriginPoint).hom.toAlgebra

@[instance_reducible]
def cmActualZGraphStalkAlgebra : Algebra cmActualZAmbientLocalRing cmActualZOriginLocalRing :=
  (cmConcreteComplexGraph.stalkMap cmActualZOriginPoint).hom.toAlgebra

attribute [local instance] cmActualYGraphStalkAlgebra cmActualZGraphStalkAlgebra

theorem cmActualYGraphStalk_surjective :
    Function.Surjective (cmConcreteComplexGraph.stalkMap cmActualYOriginPoint).hom := by
  let : IsClosedImmersion cmConcreteComplexGraph := cmConcreteGraph_closedImmersion
  exact cmConcreteComplexGraph.stalkMap_surjective cmActualYOriginPoint

theorem cmActualZGraphStalk_surjective :
    Function.Surjective (cmConcreteComplexGraph.stalkMap cmActualZOriginPoint).hom := by
  let : IsClosedImmersion cmConcreteComplexGraph := cmConcreteGraph_closedImmersion
  exact cmConcreteComplexGraph.stalkMap_surjective cmActualZOriginPoint

theorem cmActualYCutQuotient_ambient_length_one :
    Module.length cmActualYAmbientLocalRing
      (cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) = 1 := by
  have hs := Module.length_eq_of_surjective
    (S := cmActualYAmbientLocalRing) (R := cmActualYOriginLocalRing)
    (M := cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) (by
      change Function.Surjective (cmConcreteComplexGraph.stalkMap cmActualYOriginPoint).hom
      exact cmActualYGraphStalk_surjective)
  exact hs.trans cmActualYStalkLengthOne

theorem cmActualZCutQuotient_ambient_length_one :
    Module.length cmActualZAmbientLocalRing
      (cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) = 1 := by
  have hs := Module.length_eq_of_surjective
    (S := cmActualZAmbientLocalRing) (R := cmActualZOriginLocalRing)
    (M := cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) (by
      change Function.Surjective (cmConcreteComplexGraph.stalkMap cmActualZOriginPoint).hom
      exact cmActualZGraphStalk_surjective)
  exact hs.trans cmActualZStalkLengthOne

#print axioms affineSection_germ_regular
#print axioms cmActualAmbientDiagonal_stalk_regular_principal
#print axioms cmActualYGraphStalkAlgebra
#print axioms cmActualZGraphStalkAlgebra
#print axioms cmActualYGraphStalk_surjective
#print axioms cmActualZGraphStalk_surjective
#print axioms cmActualYCutQuotient_ambient_length_one
#print axioms cmActualZCutQuotient_ambient_length_one
end Holonics.Hodge.CMGraphSource
