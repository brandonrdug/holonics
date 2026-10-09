import CMActualFixedOriginSupport

/-! Join each accepted ambient quotient to the intrinsic stalk of the actual
fixed scheme. The point comparison is the equality of actual scheme maps,
and the intrinsic residue isomorphism is constructed from the actual open
immersion Spec C -> Fix. Its composition with the actual inclusion stalk map
is the accepted ambient residue receiver. Thus the first isomorphism theorem
constructs the quotient comparison, including its ambient scalar action.

agent-inferred: retain the scalar square before any sum of intrinsic lengths.
The avoided recorded failure is carrying a located comparison into a new
consumer without repairing its operands. This is an external helical pair
receiver at faces and placement, cell holonomy and tube; helix, pair and tower
remain attached. No local quotient isomorphism is assumed. No intersection
product, divisor degree or Hodge-class pairing is supplied by this source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

instance yActualFixedPoint_isOpenImmersion : IsOpenImmersion yActualFixedPoint := by
  dsimp only [yActualFixedPoint]
  infer_instance

instance zActualFixedPoint_isOpenImmersion : IsOpenImmersion zActualFixedPoint := by
  dsimp only [zActualFixedPoint]
  infer_instance

abbrev cmActualYFixedPoint := yActualFixedPoint (IsLocalRing.closedPoint ℂ)
abbrev cmActualZFixedPoint := zActualFixedPoint (IsLocalRing.closedPoint ℂ)
abbrev cmActualYFixedLocalRing := CMProjectiveFixedScheme.presheaf.stalk cmActualYFixedPoint
abbrev cmActualZFixedLocalRing := CMProjectiveFixedScheme.presheaf.stalk cmActualZFixedPoint

def cmActualYFixedLocalRingIso : cmActualYFixedLocalRing ≅ CommRingCat.of ℂ :=
  asIso (yActualFixedPoint.stalkMap (IsLocalRing.closedPoint ℂ)) ≪≫
    stalkClosedPointIso (CommRingCat.of ℂ)

def cmActualZFixedLocalRingIso : cmActualZFixedLocalRing ≅ CommRingCat.of ℂ :=
  asIso (zActualFixedPoint.stalkMap (IsLocalRing.closedPoint ℂ)) ≪≫
    stalkClosedPointIso (CommRingCat.of ℂ)

def cmActualYOriginLocalRingTransport :
    cmActualYOriginLocalRing ≅
      CMProjectiveCubic.presheaf.stalk (cmFixedInclusion cmActualYFixedPoint) :=
  eqToIso (congrArg (fun p => CMProjectiveCubic.presheaf.stalk p)
    cmActualYOriginPoint_eq_fixed)

def cmActualZOriginLocalRingTransport :
    cmActualZOriginLocalRing ≅
      CMProjectiveCubic.presheaf.stalk (cmFixedInclusion cmActualZFixedPoint) :=
  eqToIso (congrArg (fun p => CMProjectiveCubic.presheaf.stalk p)
    cmActualZOriginPoint_eq_fixed)

def cmActualYOriginToFixedStalk : cmActualYOriginLocalRing ⟶ cmActualYFixedLocalRing :=
  cmActualYOriginLocalRingTransport.hom ≫ cmFixedInclusion.stalkMap cmActualYFixedPoint

def cmActualZOriginToFixedStalk : cmActualZOriginLocalRing ⟶ cmActualZFixedLocalRing :=
  cmActualZOriginLocalRingTransport.hom ≫ cmFixedInclusion.stalkMap cmActualZFixedPoint

theorem stalkClosedPointTo_transport {X : Scheme} {u v : Spec (CommRingCat.of ℂ) ⟶ X}
    (h : u = v) :
    (eqToIso (congrArg (fun p => X.presheaf.stalk p)
      (congrArg (fun f => f (IsLocalRing.closedPoint ℂ)) h))).hom ≫
        Scheme.stalkClosedPointTo v = Scheme.stalkClosedPointTo u := by
  subst v
  simp

theorem cmActualYOriginToFixedStalk_residue_comp :
    cmActualYOriginToFixedStalk ≫ cmActualYFixedLocalRingIso.hom =
      cmActualYOriginResidueMap := by
  change (cmActualYOriginLocalRingTransport.hom ≫
    cmFixedInclusion.stalkMap cmActualYFixedPoint) ≫
      Scheme.stalkClosedPointTo yActualFixedPoint =
        Scheme.stalkClosedPointTo
          (Spec.map (CommRingCat.ofHom yRestrictedOriginLift.toRingHom) ≫
            cmActualRestrictedYCurveOpen)
  rw [Category.assoc, ← Scheme.stalkClosedPointTo_comp]
  exact stalkClosedPointTo_transport cmActualYOrigin_inclusion_map

theorem cmActualZOriginToFixedStalk_residue_comp :
    cmActualZOriginToFixedStalk ≫ cmActualZFixedLocalRingIso.hom =
      cmActualZOriginResidueMap := by
  change (cmActualZOriginLocalRingTransport.hom ≫
    cmFixedInclusion.stalkMap cmActualZFixedPoint) ≫
      Scheme.stalkClosedPointTo zActualFixedPoint =
        Scheme.stalkClosedPointTo
          (Spec.map (CommRingCat.ofHom cmActualZOriginLift.toRingHom) ≫
            cmActualRestrictedZCurveOpen)
  rw [Category.assoc, ← Scheme.stalkClosedPointTo_comp]
  exact stalkClosedPointTo_transport cmActualZOrigin_inclusion_map

theorem cmActualYOriginToFixedStalk_kernel :
    RingHom.ker cmActualYOriginToFixedStalk.hom = cmActualYOriginStalkIdeal := by
  calc
    RingHom.ker cmActualYOriginToFixedStalk.hom =
        RingHom.ker (cmActualYOriginToFixedStalk ≫ cmActualYFixedLocalRingIso.hom).hom :=
      (RingHom.ker_comp_of_injective cmActualYOriginToFixedStalk.hom
        cmActualYFixedLocalRingIso.commRingCatIsoToRingEquiv.injective).symm
    _ = RingHom.ker cmActualYOriginResidueMap.hom :=
      congrArg (fun f => RingHom.ker f.hom) cmActualYOriginToFixedStalk_residue_comp
    _ = cmActualYOriginStalkIdeal := cmActualYResidueMap_kernel

theorem cmActualZOriginToFixedStalk_kernel :
    RingHom.ker cmActualZOriginToFixedStalk.hom = cmActualZOriginStalkIdeal := by
  calc
    RingHom.ker cmActualZOriginToFixedStalk.hom =
        RingHom.ker (cmActualZOriginToFixedStalk ≫ cmActualZFixedLocalRingIso.hom).hom :=
      (RingHom.ker_comp_of_injective cmActualZOriginToFixedStalk.hom
        cmActualZFixedLocalRingIso.commRingCatIsoToRingEquiv.injective).symm
    _ = RingHom.ker cmActualZOriginResidueMap.hom :=
      congrArg (fun f => RingHom.ker f.hom) cmActualZOriginToFixedStalk_residue_comp
    _ = cmActualZOriginStalkIdeal := cmActualZResidueMap_kernel

theorem cmActualYOriginToFixedStalk_surjective :
    Function.Surjective cmActualYOriginToFixedStalk.hom := by
  intro b
  obtain ⟨a, ha⟩ := cmActualYResidueMap_surjective (cmActualYFixedLocalRingIso.hom.hom b)
  refine ⟨a, cmActualYFixedLocalRingIso.commRingCatIsoToRingEquiv.injective ?_⟩
  change cmActualYFixedLocalRingIso.hom.hom (cmActualYOriginToFixedStalk.hom a) =
    cmActualYFixedLocalRingIso.hom.hom b
  exact (congrArg (fun f => f.hom a) cmActualYOriginToFixedStalk_residue_comp).trans ha

theorem cmActualZOriginToFixedStalk_surjective :
    Function.Surjective cmActualZOriginToFixedStalk.hom := by
  intro b
  obtain ⟨a, ha⟩ := cmActualZResidueMap_surjective (cmActualZFixedLocalRingIso.hom.hom b)
  refine ⟨a, cmActualZFixedLocalRingIso.commRingCatIsoToRingEquiv.injective ?_⟩
  change cmActualZFixedLocalRingIso.hom.hom (cmActualZOriginToFixedStalk.hom a) =
    cmActualZFixedLocalRingIso.hom.hom b
  exact (congrArg (fun f => f.hom a) cmActualZOriginToFixedStalk_residue_comp).trans ha

def cmActualYQuotientToFixedStalk :
    (cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) ≃+* cmActualYFixedLocalRing :=
  (Ideal.quotEquivOfEq cmActualYOriginToFixedStalk_kernel.symm).trans
    (RingHom.quotientKerEquivOfSurjective cmActualYOriginToFixedStalk_surjective)

def cmActualZQuotientToFixedStalk :
    (cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) ≃+* cmActualZFixedLocalRing :=
  (Ideal.quotEquivOfEq cmActualZOriginToFixedStalk_kernel.symm).trans
    (RingHom.quotientKerEquivOfSurjective cmActualZOriginToFixedStalk_surjective)

theorem cmActualYQuotientToFixedStalk_mk (a : cmActualYOriginLocalRing) :
    cmActualYQuotientToFixedStalk (Ideal.Quotient.mk cmActualYOriginStalkIdeal a) =
      cmActualYOriginToFixedStalk.hom a := by
  simp only [cmActualYQuotientToFixedStalk, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem cmActualZQuotientToFixedStalk_mk (a : cmActualZOriginLocalRing) :
    cmActualZQuotientToFixedStalk (Ideal.Quotient.mk cmActualZOriginStalkIdeal a) =
      cmActualZOriginToFixedStalk.hom a := by
  simp only [cmActualZQuotientToFixedStalk, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem cmActualYQuotientToFixedStalk_smul (a : cmActualYOriginLocalRing)
    (x : cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) :
    cmActualYQuotientToFixedStalk (a • x) =
      cmActualYOriginToFixedStalk.hom a * cmActualYQuotientToFixedStalk x := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul,
    cmActualYQuotientToFixedStalk_mk]

theorem cmActualZQuotientToFixedStalk_smul (a : cmActualZOriginLocalRing)
    (x : cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) :
    cmActualZQuotientToFixedStalk (a • x) =
      cmActualZOriginToFixedStalk.hom a * cmActualZQuotientToFixedStalk x := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul,
    cmActualZQuotientToFixedStalk_mk]

#print axioms cmActualYFixedLocalRingIso
#print axioms cmActualZFixedLocalRingIso
#print axioms cmActualYOriginToFixedStalk_residue_comp
#print axioms cmActualZOriginToFixedStalk_residue_comp
#print axioms cmActualYOriginToFixedStalk_kernel
#print axioms cmActualZOriginToFixedStalk_kernel
#print axioms cmActualYOriginToFixedStalk_surjective
#print axioms cmActualZOriginToFixedStalk_surjective
#print axioms cmActualYQuotientToFixedStalk
#print axioms cmActualZQuotientToFixedStalk
#print axioms cmActualYQuotientToFixedStalk_smul
#print axioms cmActualZQuotientToFixedStalk_smul
end Holonics.Hodge.CMGraphSource
