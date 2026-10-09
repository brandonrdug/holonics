import CMResidueStalkBridge
import CMActualFixedCartierData

/-! The actual restricted origin receivers induce maps on the actual
projective stalks. Their kernels are proved to be the germ extensions of
the actual fixed inclusion's ideal, and their surjectivity constructs the
quotient-to-C isomorphisms. Module.length is over each projective local
ring, not over the coordinate coefficient field.

agent-inferred: specialize the constructed stalk bridge to the already
checked Y(a) and Z(v) restrictions and actual origin lifts. No intersection
degree, cycle class, Hodge pairing or rational Hodge-carrier rank follows.
The helical pair interaction and its receiver faces, cell holonomy and tube
stay attached; helix, pair and tower thread remain attached. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry IsLocalRing TopologicalSpace
namespace Holonics.Hodge.CMGraphSource

theorem cmActualYOriginLift_kernel :
    RingHom.ker yRestrictedOriginLift.toRingHom = Ideal.span {yRestrictedA} := by
  change RingHom.ker yRestrictedOriginLift = Ideal.span {yRestrictedA}
  rw [yRestrictedOriginLift_ker_eq_fixedIdeal, yRestrictedFixedIdeal_eq_spanA]

theorem cmActualZOrigin_factor_unit : IsUnit (originReceiver (u ^ 2 - 1)) := by
  have h : originReceiver (u ^ 2 - 1) = -1 := by simp [originReceiver_u]
  rw [h]
  exact isUnit_one.neg

def cmActualZOriginLift : ActualRestrictedZRing →ₐ[ℂ] ℂ :=
  restrictedOriginLift originReceiver (u ^ 2 - 1) cmActualZOrigin_factor_unit

theorem cmActualZOriginLift_kernel :
    RingHom.ker cmActualZOriginLift.toRingHom =
      Ideal.span {algebraMap CurveRing ActualRestrictedZRing v} := by
  exact (restrictedOriginLift_ker_map originReceiver (u ^ 2 - 1)
    cmActualZOrigin_factor_unit).trans actualRestrictedZ_originKernel_map_eq_v

abbrev cmActualYOriginPoint : CMProjectiveCubic :=
  spectrumResiduePoint (.of YRestrictedQAway) cmActualRestrictedYCurveOpen
    yRestrictedOriginLift.toRingHom

abbrev cmActualZOriginPoint : CMProjectiveCubic :=
  spectrumResiduePoint (.of ActualRestrictedZRing) cmActualRestrictedZCurveOpen
    cmActualZOriginLift.toRingHom

abbrev cmActualYOriginLocalRing := CMProjectiveCubic.presheaf.stalk cmActualYOriginPoint
abbrev cmActualZOriginLocalRing := CMProjectiveCubic.presheaf.stalk cmActualZOriginPoint

abbrev cmActualYOriginStalkIdeal : Ideal cmActualYOriginLocalRing :=
  spectrumImageStalkIdeal cmFixedInclusion.ker (.of YRestrictedQAway)
    cmActualRestrictedYCurveOpen yRestrictedOriginLift.toRingHom

abbrev cmActualZOriginStalkIdeal : Ideal cmActualZOriginLocalRing :=
  spectrumImageStalkIdeal cmFixedInclusion.ker (.of ActualRestrictedZRing)
    cmActualRestrictedZCurveOpen cmActualZOriginLift.toRingHom

abbrev cmActualYOriginResidueMap : cmActualYOriginLocalRing ⟶ .of ℂ :=
  spectrumResidueMap (.of YRestrictedQAway) cmActualRestrictedYCurveOpen
    yRestrictedOriginLift.toRingHom

abbrev cmActualZOriginResidueMap : cmActualZOriginLocalRing ⟶ .of ℂ :=
  spectrumResidueMap (.of ActualRestrictedZRing) cmActualRestrictedZCurveOpen
    cmActualZOriginLift.toRingHom

theorem cmActualYResidueMap_kernel :
    RingHom.ker cmActualYOriginResidueMap.hom = cmActualYOriginStalkIdeal :=
  spectrumImageStalkIdeal_kernel cmFixedInclusion.ker (.of YRestrictedQAway)
    cmActualRestrictedYCurveOpen yRestrictedOriginLift.toRingHom yRestrictedA
    cmActualFixedYRestricted_regular_equation.1 cmActualYOriginLift_kernel

theorem cmActualZResidueMap_kernel :
    RingHom.ker cmActualZOriginResidueMap.hom = cmActualZOriginStalkIdeal :=
  spectrumImageStalkIdeal_kernel cmFixedInclusion.ker (.of ActualRestrictedZRing)
    cmActualRestrictedZCurveOpen cmActualZOriginLift.toRingHom
    (algebraMap CurveRing ActualRestrictedZRing v)
    cmActualFixedZRestricted_regular_equation.1 cmActualZOriginLift_kernel

theorem cmActualYOriginLift_surjective : Function.Surjective yRestrictedOriginLift :=
  restrictedOriginLift_surjective yOriginReceiver yRestrictedQ yRestrictedQ_origin_isUnit

theorem cmActualZOriginLift_surjective : Function.Surjective cmActualZOriginLift :=
  restrictedOriginLift_surjective originReceiver (u ^ 2 - 1) cmActualZOrigin_factor_unit

theorem cmActualYResidueMap_surjective : Function.Surjective cmActualYOriginResidueMap.hom :=
  spectrumResidueMap_surjective (.of YRestrictedQAway) cmActualRestrictedYCurveOpen
    yRestrictedOriginLift.toRingHom cmActualYOriginLift_surjective

theorem cmActualZResidueMap_surjective : Function.Surjective cmActualZOriginResidueMap.hom :=
  spectrumResidueMap_surjective (.of ActualRestrictedZRing) cmActualRestrictedZCurveOpen
    cmActualZOriginLift.toRingHom cmActualZOriginLift_surjective

def cmActualYStalkQuotientEquiv :
    (cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) ≃+* ℂ :=
  spectrumStalkQuotientEquiv cmFixedInclusion.ker (.of YRestrictedQAway)
    cmActualRestrictedYCurveOpen yRestrictedOriginLift.toRingHom yRestrictedA
    cmActualFixedYRestricted_regular_equation.1 cmActualYOriginLift_kernel
    cmActualYOriginLift_surjective

def cmActualZStalkQuotientEquiv :
    (cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) ≃+* ℂ :=
  spectrumStalkQuotientEquiv cmFixedInclusion.ker (.of ActualRestrictedZRing)
    cmActualRestrictedZCurveOpen cmActualZOriginLift.toRingHom
    (algebraMap CurveRing ActualRestrictedZRing v)
    cmActualFixedZRestricted_regular_equation.1 cmActualZOriginLift_kernel
    cmActualZOriginLift_surjective

theorem cmActualYStalkLengthOne :
    Module.length cmActualYOriginLocalRing
      (cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) = 1 :=
  spectrumStalkQuotient_length_one cmFixedInclusion.ker (.of YRestrictedQAway)
    cmActualRestrictedYCurveOpen yRestrictedOriginLift.toRingHom yRestrictedA
    cmActualFixedYRestricted_regular_equation.1 cmActualYOriginLift_kernel
    cmActualYOriginLift_surjective

theorem cmActualZStalkLengthOne :
    Module.length cmActualZOriginLocalRing
      (cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) = 1 :=
  spectrumStalkQuotient_length_one cmFixedInclusion.ker (.of ActualRestrictedZRing)
    cmActualRestrictedZCurveOpen cmActualZOriginLift.toRingHom
    (algebraMap CurveRing ActualRestrictedZRing v)
    cmActualFixedZRestricted_regular_equation.1 cmActualZOriginLift_kernel
    cmActualZOriginLift_surjective

theorem cmActualFixedCartier_and_origin_stalk_lengths :
    (Opens.grothendieckTopology CMProjectiveCubic).CoversTop cmActualFixedAffineOpen ∧
    (∀ i, IsRegular (cmActualFixedAffineEquation i)) ∧
    (∀ i, cmFixedInclusion.ker.ideal
      ⟨cmActualFixedAffineOpen i, cmActualFixedAffineOpen_isAffine i⟩ =
        Ideal.span {cmActualFixedAffineEquation i}) ∧
    Module.length cmActualYOriginLocalRing
      (cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) = 1 ∧
    Module.length cmActualZOriginLocalRing
      (cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) = 1 :=
  ⟨cmActualFixedAffineOpen_coversTop, cmActualFixedAffineEquation_regular,
    cmActualFixedAffineEquation_ideal, cmActualYStalkLengthOne, cmActualZStalkLengthOne⟩

#print axioms cmActualYOriginLift_kernel
#print axioms cmActualZOriginLift_kernel
#print axioms cmActualYResidueMap_kernel
#print axioms cmActualZResidueMap_kernel
#print axioms cmActualYResidueMap_surjective
#print axioms cmActualZResidueMap_surjective
#print axioms cmActualYStalkQuotientEquiv
#print axioms cmActualZStalkQuotientEquiv
#print axioms cmActualYStalkLengthOne
#print axioms cmActualZStalkLengthOne
#print axioms cmActualFixedCartier_and_origin_stalk_lengths
end Holonics.Hodge.CMGraphSource
