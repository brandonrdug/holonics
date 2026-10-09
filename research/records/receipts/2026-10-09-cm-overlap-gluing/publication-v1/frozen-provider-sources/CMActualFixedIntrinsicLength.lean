import CMActualFixedIntrinsicStalk

/-! The ambient-to-intrinsic comparison is linear for the actual inclusion
stalk map. Restricting scalars along that proved-surjective map preserves
length. Thus the accepted ambient quotient length is the intrinsic length
of the actual graph--diagonal pullback stalk, with no coefficient-field
length substituted for either local length.

agent-inferred: retain the inclusion scalar action explicitly before using
the intrinsic length as an intersection multiplicity. The avoided recorded
failure is an unjoined comparison entering a new consumer. This external
helical pair receiver touches faces and placement, cell holonomy and tube;
helix, pair and tower remain attached. No degree or Hodge pairing is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

@[instance_reducible]
def cmActualYFixedStalkAlgebra : Algebra cmActualYOriginLocalRing cmActualYFixedLocalRing :=
  cmActualYOriginToFixedStalk.hom.toAlgebra

@[instance_reducible]
def cmActualZFixedStalkAlgebra : Algebra cmActualZOriginLocalRing cmActualZFixedLocalRing :=
  cmActualZOriginToFixedStalk.hom.toAlgebra

attribute [local instance] cmActualYFixedStalkAlgebra cmActualZFixedStalkAlgebra

def cmActualYQuotientToFixedStalkAlgEquiv :
    (cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) ≃ₐ[cmActualYOriginLocalRing]
      cmActualYFixedLocalRing :=
  AlgEquiv.ofRingEquiv (f := cmActualYQuotientToFixedStalk) fun a => by
    change cmActualYQuotientToFixedStalk (Ideal.Quotient.mk cmActualYOriginStalkIdeal a) =
      cmActualYOriginToFixedStalk.hom a
    exact cmActualYQuotientToFixedStalk_mk a

def cmActualZQuotientToFixedStalkAlgEquiv :
    (cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) ≃ₐ[cmActualZOriginLocalRing]
      cmActualZFixedLocalRing :=
  AlgEquiv.ofRingEquiv (f := cmActualZQuotientToFixedStalk) fun a => by
    change cmActualZQuotientToFixedStalk (Ideal.Quotient.mk cmActualZOriginStalkIdeal a) =
      cmActualZOriginToFixedStalk.hom a
    exact cmActualZQuotientToFixedStalk_mk a

theorem cmActualYFixedStalkLength_over_ambient :
    Module.length cmActualYOriginLocalRing cmActualYFixedLocalRing = 1 := by
  calc
    Module.length cmActualYOriginLocalRing cmActualYFixedLocalRing =
        Module.length cmActualYOriginLocalRing
          (cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) :=
      cmActualYQuotientToFixedStalkAlgEquiv.toLinearEquiv.length_eq.symm
    _ = 1 := cmActualYStalkLengthOne

theorem cmActualZFixedStalkLength_over_ambient :
    Module.length cmActualZOriginLocalRing cmActualZFixedLocalRing = 1 := by
  calc
    Module.length cmActualZOriginLocalRing cmActualZFixedLocalRing =
        Module.length cmActualZOriginLocalRing
          (cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) :=
      cmActualZQuotientToFixedStalkAlgEquiv.toLinearEquiv.length_eq.symm
    _ = 1 := cmActualZStalkLengthOne

theorem cmActualYFixedIntrinsicLengthOne :
    Module.length cmActualYFixedLocalRing cmActualYFixedLocalRing = 1 := by
  have hscalar := Module.length_eq_of_surjective
    (S := cmActualYOriginLocalRing) (R := cmActualYFixedLocalRing)
    (M := cmActualYFixedLocalRing) (by
      change Function.Surjective cmActualYOriginToFixedStalk.hom
      exact cmActualYOriginToFixedStalk_surjective)
  exact hscalar.symm.trans cmActualYFixedStalkLength_over_ambient

theorem cmActualZFixedIntrinsicLengthOne :
    Module.length cmActualZFixedLocalRing cmActualZFixedLocalRing = 1 := by
  have hscalar := Module.length_eq_of_surjective
    (S := cmActualZOriginLocalRing) (R := cmActualZFixedLocalRing)
    (M := cmActualZFixedLocalRing) (by
      change Function.Surjective cmActualZOriginToFixedStalk.hom
      exact cmActualZOriginToFixedStalk_surjective)
  exact hscalar.symm.trans cmActualZFixedStalkLength_over_ambient

theorem cmActualFixedIntrinsicLengthOne (q : CMProjectiveFixedScheme) :
    Module.length (CMProjectiveFixedScheme.presheaf.stalk q)
      (CMProjectiveFixedScheme.presheaf.stalk q) = 1 := by
  rcases actualFixed_two_point_population q with h | h
  · rw [h]
    exact cmActualYFixedIntrinsicLengthOne
  · rw [h]
    exact cmActualZFixedIntrinsicLengthOne

#print axioms cmActualYQuotientToFixedStalkAlgEquiv
#print axioms cmActualZQuotientToFixedStalkAlgEquiv
#print axioms cmActualYFixedIntrinsicLengthOne
#print axioms cmActualZFixedIntrinsicLengthOne
#print axioms cmActualFixedIntrinsicLengthOne
end Holonics.Hodge.CMGraphSource
