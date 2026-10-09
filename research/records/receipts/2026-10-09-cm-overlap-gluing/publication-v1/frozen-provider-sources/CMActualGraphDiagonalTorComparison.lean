import CMActualAmbientCartierStalkJoin
import CMCartierStalkNaturality
import CMCartierScalarResolution
import CMCartierTorZeroQuotient
import Mathlib.Algebra.BigOperators.Finprod

/-! Actual derived tensor comparison at the two graph–diagonal points.
The ambient local ring is the product stalk, the curve module uses the
actual graph stalk map, and the diagonal quotient uses the actual diagonal
germ. Both regularity statements are proved separately. The graph sends
the ambient generator to the restricted generator by the proved scheme
square, not by an assumed local isomorphism.

agent-inferred: compute native Tor directly from the checked regular
two-term resolution. No regular-local-ring, Noetherian, Chow or Hodge
comparison is imported or postulated. The external helical pair receiver
touches faces and placement, cell holonomy and tube, with helix, pair and
tower thread retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

attribute [local instance] cmActualYGraphStalkAlgebra cmActualZGraphStalkAlgebra

theorem cmActualYGraphStalk_diagonal_image :
    (cmConcreteComplexGraph.stalkMap cmActualYOriginPoint).hom
        cmActualYAmbientDiagonalGerm = cmActualYImageEquationGerm := by
  have hc := congrArg (fun f : CommRingCat.of YProductRing ⟶
      CommRingCat.of YRestrictedQAway => f.hom yDiagonalAEquation)
    yAmbientQToRestricted_comp
  change yAmbientQToRestricted
    (algebraMap YProductRing (Localization.Away yDiagonalQ) yDiagonalAEquation) =
      yRestrictedMap yDiagonalAEquation at hc
  have h := spectrumImage_stalkMap_naturality cmActualRestrictedYCurveOpen
    yDiagonalQAmbientOpen (CommRingCat.ofHom yAmbientQToRestricted)
    cmConcreteComplexGraph yAmbientQ_actual_graph_square
    (specResiduePoint (.of YRestrictedQAway) yRestrictedOriginLift.toRingHom)
    (algebraMap YProductRing (Localization.Away yDiagonalQ) yDiagonalAEquation)
  simpa only [spectrumImageAmbientGerm, spectrumImageChartGerm,
    cmActualYAmbientDiagonalGerm, cmActualYImageEquationGerm,
    cmActualDiagonalAffineOpen, cmActualDiagonalAffineEquation,
    cmActualYImageEquationSection, cmActualYOriginPoint, spectrumResiduePoint,
    CommRingCat.hom_ofHom, hc] using h

theorem cmActualZGraphStalk_diagonal_image :
    (cmConcreteComplexGraph.stalkMap cmActualZOriginPoint).hom
        cmActualZAmbientDiagonalGerm = cmActualZImageEquationGerm := by
  have hc := congrArg (fun f : CommRingCat.of ProductRing ⟶
      CommRingCat.of ActualRestrictedZRing => f.hom diagonalVEquation)
    zAmbientFactorToRestricted_comp
  change zAmbientFactorToRestricted
    (algebraMap ProductRing (Localization.Away diagonalCubicFactor) diagonalVEquation) =
      zRestrictedMap diagonalVEquation at hc
  have h := spectrumImage_stalkMap_naturality cmActualRestrictedZCurveOpen
    zDiagonalFactorAmbientOpen (CommRingCat.ofHom zAmbientFactorToRestricted)
    cmConcreteComplexGraph zAmbientFactor_actual_graph_square
    (specResiduePoint (.of ActualRestrictedZRing) cmActualZOriginLift.toRingHom)
    (algebraMap ProductRing (Localization.Away diagonalCubicFactor) diagonalVEquation)
  simpa only [spectrumImageAmbientGerm, spectrumImageChartGerm,
    cmActualZAmbientDiagonalGerm, cmActualZImageEquationGerm,
    cmActualDiagonalAffineOpen, cmActualDiagonalAffineEquation,
    cmActualZImageEquationSection, cmActualZOriginPoint, spectrumResiduePoint,
    CommRingCat.hom_ofHom, hc] using h

theorem cmActualYDiagonal_action_regular :
    IsSMulRegular cmActualYOriginLocalRing cmActualYAmbientDiagonalGerm := by
  change Function.Injective (fun x : cmActualYOriginLocalRing =>
    (cmConcreteComplexGraph.stalkMap cmActualYOriginPoint).hom
      cmActualYAmbientDiagonalGerm * x)
  rw [cmActualYGraphStalk_diagonal_image]
  exact cmActualYImageEquationGerm_regular.left

theorem cmActualZDiagonal_action_regular :
    IsSMulRegular cmActualZOriginLocalRing cmActualZAmbientDiagonalGerm := by
  change Function.Injective (fun x : cmActualZOriginLocalRing =>
    (cmConcreteComplexGraph.stalkMap cmActualZOriginPoint).hom
      cmActualZAmbientDiagonalGerm * x)
  rw [cmActualZGraphStalk_diagonal_image]
  exact cmActualZImageEquationGerm_regular.left

theorem cmActualYDiagonalIdeal_map :
    (Ideal.span {cmActualYAmbientDiagonalGerm}).map
      (algebraMap cmActualYAmbientLocalRing cmActualYOriginLocalRing) =
        cmActualYOriginStalkIdeal := by
  change (Ideal.span {cmActualYAmbientDiagonalGerm}).map
    (cmConcreteComplexGraph.stalkMap cmActualYOriginPoint).hom = _
  rw [Ideal.map_span, Set.image_singleton, cmActualYGraphStalk_diagonal_image]
  exact cmActualYOriginStalkIdeal_span_imageEquation.symm

theorem cmActualZDiagonalIdeal_map :
    (Ideal.span {cmActualZAmbientDiagonalGerm}).map
      (algebraMap cmActualZAmbientLocalRing cmActualZOriginLocalRing) =
        cmActualZOriginStalkIdeal := by
  change (Ideal.span {cmActualZAmbientDiagonalGerm}).map
    (cmConcreteComplexGraph.stalkMap cmActualZOriginPoint).hom = _
  rw [Ideal.map_span, Set.image_singleton, cmActualZGraphStalk_diagonal_image]
  exact cmActualZOriginStalkIdeal_span_imageEquation.symm

abbrev cmActualYGraphDiagonalTor (n : ℕ) :=
  (((Tor (ModuleCat cmActualYAmbientLocalRing) n).obj
    (ModuleCat.of cmActualYAmbientLocalRing cmActualYOriginLocalRing)).obj
      (ModuleCat.of cmActualYAmbientLocalRing
        (cmActualYAmbientLocalRing ⧸ Ideal.span {cmActualYAmbientDiagonalGerm})))

abbrev cmActualZGraphDiagonalTor (n : ℕ) :=
  (((Tor (ModuleCat cmActualZAmbientLocalRing) n).obj
    (ModuleCat.of cmActualZAmbientLocalRing cmActualZOriginLocalRing)).obj
      (ModuleCat.of cmActualZAmbientLocalRing
        (cmActualZAmbientLocalRing ⧸ Ideal.span {cmActualZAmbientDiagonalGerm})))

theorem cmActualYGraphDiagonal_higherTor_isZero (n : ℕ) :
    IsZero (cmActualYGraphDiagonalTor (n + 1)) :=
  higherTorIdealQuotient_isZero cmActualYAmbientLocalRing
    cmActualYAmbientDiagonalGerm cmActualYOriginLocalRing
    cmActualYAmbientDiagonalGerm_regular cmActualYDiagonal_action_regular n

theorem cmActualZGraphDiagonal_higherTor_isZero (n : ℕ) :
    IsZero (cmActualZGraphDiagonalTor (n + 1)) :=
  higherTorIdealQuotient_isZero cmActualZAmbientLocalRing
    cmActualZAmbientDiagonalGerm cmActualZOriginLocalRing
    cmActualZAmbientDiagonalGerm_regular cmActualZDiagonal_action_regular n

theorem cmActualYGraphDiagonal_TorZero_length :
    Module.length cmActualYAmbientLocalRing (cmActualYGraphDiagonalTor 0) = 1 := by
  rw [cartierTorZeroQuotient_length, cmActualYDiagonalIdeal_map]
  exact cmActualYCutQuotient_ambient_length_one

theorem cmActualZGraphDiagonal_TorZero_length :
    Module.length cmActualZAmbientLocalRing (cmActualZGraphDiagonalTor 0) = 1 := by
  rw [cartierTorZeroQuotient_length, cmActualZDiagonalIdeal_map]
  exact cmActualZCutQuotient_ambient_length_one

theorem cmActualYGraphDiagonal_Tor_length (n : ℕ) :
    Module.length cmActualYAmbientLocalRing (cmActualYGraphDiagonalTor n) =
      if n = 0 then 1 else 0 := by
  cases n with
  | zero => simpa using cmActualYGraphDiagonal_TorZero_length
  | succ n =>
    simpa only [Nat.succ_ne_zero, if_false] using
      ((Module.length_eq_zero_iff (R := cmActualYAmbientLocalRing)).mpr
        (ModuleCat.subsingleton_of_isZero (cmActualYGraphDiagonal_higherTor_isZero n)))

theorem cmActualZGraphDiagonal_Tor_length (n : ℕ) :
    Module.length cmActualZAmbientLocalRing (cmActualZGraphDiagonalTor n) =
      if n = 0 then 1 else 0 := by
  cases n with
  | zero => simpa using cmActualZGraphDiagonal_TorZero_length
  | succ n =>
    simpa only [Nat.succ_ne_zero, if_false] using
      ((Module.length_eq_zero_iff (R := cmActualZAmbientLocalRing)).mpr
        (ModuleCat.subsingleton_of_isZero (cmActualZGraphDiagonal_higherTor_isZero n)))

/-- The local Serre alternating Tor-length sum of the actual pair.
All positive-degree terms vanish by the proved resolution. -/
def cmActualYGraphDiagonalSerreMultiplicity : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    (Module.length cmActualYAmbientLocalRing (cmActualYGraphDiagonalTor n)).toNat

def cmActualZGraphDiagonalSerreMultiplicity : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    (Module.length cmActualZAmbientLocalRing (cmActualZGraphDiagonalTor n)).toNat

theorem cmActualYGraphDiagonalSerreMultiplicity_eq_length :
    cmActualYGraphDiagonalSerreMultiplicity =
      (Module.length cmActualYAmbientLocalRing
        (cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal)).toNat := by
  unfold cmActualYGraphDiagonalSerreMultiplicity
  rw [finsum_eq_single _ 0 (fun n hn => by
    simp only [cmActualYGraphDiagonal_Tor_length, if_neg hn,
      ENat.toNat_zero, Nat.cast_zero, mul_zero])]
  simp only [cmActualYGraphDiagonal_TorZero_length,
    cmActualYCutQuotient_ambient_length_one, ENat.toNat_one, Nat.cast_one,
    pow_zero, mul_one]

theorem cmActualZGraphDiagonalSerreMultiplicity_eq_length :
    cmActualZGraphDiagonalSerreMultiplicity =
      (Module.length cmActualZAmbientLocalRing
        (cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal)).toNat := by
  unfold cmActualZGraphDiagonalSerreMultiplicity
  rw [finsum_eq_single _ 0 (fun n hn => by
    simp only [cmActualZGraphDiagonal_Tor_length, if_neg hn,
      ENat.toNat_zero, Nat.cast_zero, mul_zero])]
  simp only [cmActualZGraphDiagonal_TorZero_length,
    cmActualZCutQuotient_ambient_length_one, ENat.toNat_one, Nat.cast_one,
    pow_zero, mul_one]

#print axioms cmActualYGraphStalk_diagonal_image
#print axioms cmActualZGraphStalk_diagonal_image
#print axioms cmActualYDiagonal_action_regular
#print axioms cmActualZDiagonal_action_regular
#print axioms cmActualYDiagonalIdeal_map
#print axioms cmActualZDiagonalIdeal_map
#print axioms cmActualYGraphDiagonal_higherTor_isZero
#print axioms cmActualZGraphDiagonal_higherTor_isZero
#print axioms cmActualYGraphDiagonal_TorZero_length
#print axioms cmActualZGraphDiagonal_TorZero_length
#print axioms cmActualYGraphDiagonal_Tor_length
#print axioms cmActualZGraphDiagonal_Tor_length
#print axioms cmActualYGraphDiagonalSerreMultiplicity_eq_length
#print axioms cmActualZGraphDiagonalSerreMultiplicity_eq_length
end Holonics.Hodge.CMGraphSource
