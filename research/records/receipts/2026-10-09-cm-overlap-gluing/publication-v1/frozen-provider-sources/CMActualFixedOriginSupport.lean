import CMActualFixedStalkLength
import CMActualFixedOverlapEmpty

/-! The two actual restricted residue receivers are compared with the
inclusions supplied by the actual fixed-chart quotient isomorphisms. The
comparison is an equality of scheme maps before it is read at a point.
The actual fixed support is then enumerated by these distinct points.

agent-inferred: first join maps and support, before any sum of local lengths.
The avoided recorded failure is moving a located cause into a consumer
without its comparison. This external helical pair receiver touches faces
and placement, cell holonomy and tube; helix, pair and tower remain attached.
No intersection-degree or Hodge-pairing comparison is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

local instance : IsClosedImmersion cmFixedInclusion :=
  cmFixedInclusion_closedImmersion

def yActualFixedPoint : Spec (.of ℂ) ⟶ CMProjectiveFixedScheme :=
  yGlobalFixedPullbackPointIso.inv ≫ yFixedOpenMap

def zActualFixedPoint : Spec (.of ℂ) ⟶ CMProjectiveFixedScheme :=
  zGlobalFixedPullbackPointIso.inv ≫ zFixedOpenMap

theorem cmYFixedCoordinate_comp_origin :
    CommRingCat.ofHom (Ideal.Quotient.mk yFixedDifferenceIdeal) ≫
      CommRingCat.ofHom yFixedCoordinatePointEquiv.toRingHom =
        CommRingCat.ofHom yOriginReceiver.toRingHom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change yFixedCoordinatePointEquiv (Ideal.Quotient.mk yFixedDifferenceIdeal r) = _
  change yZeroPointCoordinateEquiv
    (Ideal.quotEquivOfEq yFixedDifferenceIdeal_eq_origin
      (Ideal.Quotient.mk yFixedDifferenceIdeal r)) = _
  rw [Ideal.quotEquivOfEq_mk]
  change yOriginQuotientReceiver (Ideal.Quotient.mk yZeroPointIdeal r) = _
  rw [yOriginQuotientReceiver, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

theorem cmZFixedCoordinate_comp_origin :
    CommRingCat.ofHom (Ideal.Quotient.mk zFixedDifferenceIdeal) ≫
      CommRingCat.ofHom zFixedCoordinatePointEquiv.toRingHom =
        CommRingCat.ofHom zOriginReceiver.toRingHom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change zFixedCoordinatePointEquiv (Ideal.Quotient.mk zFixedDifferenceIdeal r) = _
  change zZeroPointCoordinateEquiv
    (Ideal.quotEquivOfEq zFixedDifferenceIdeal_eq_origin
      (Ideal.Quotient.mk zFixedDifferenceIdeal r)) = _
  rw [Ideal.quotEquivOfEq_mk]
  change zOriginQuotientReceiver (Ideal.Quotient.mk zZeroPointIdeal r) = _
  rw [zOriginQuotientReceiver, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

theorem cmZOriginReceivers_eq : zOriginReceiver = originReceiver := by
  apply curveRing_hom_ext
  · change zOriginReceiver zU = originReceiver u
    rw [zOriginReceiver_u, originReceiver_u]
  · change zOriginReceiver zV = originReceiver v
    rw [zOriginReceiver_v, originReceiver_v]

theorem cmActualYRestrictedOrigin_comp :
    CommRingCat.ofHom (algebraMap YChartCubicRing YRestrictedQAway) ≫
      CommRingCat.ofHom yRestrictedOriginLift.toRingHom =
        CommRingCat.ofHom yOriginReceiver.toRingHom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simp [yRestrictedOriginLift, restrictedOriginLift]

theorem cmActualZRestrictedOrigin_comp :
    CommRingCat.ofHom (algebraMap CurveRing ActualRestrictedZRing) ≫
      CommRingCat.ofHom cmActualZOriginLift.toRingHom =
        CommRingCat.ofHom zOriginReceiver.toRingHom := by
  rw [cmZOriginReceivers_eq]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simp [cmActualZOriginLift, restrictedOriginLift]

theorem cmActualYFixedPoint_inclusion_map :
    yActualFixedPoint ≫ cmFixedInclusion =
      Spec.map (CommRingCat.ofHom yOriginReceiver.toRingHom) ≫
        yCurveChartInclusion := by
  change ((Spec.map (CommRingCat.ofHom yFixedCoordinatePointEquiv.toRingHom) ≫
    yActualFixedChartQuotientIso.inv) ≫
    pullback.fst cmFixedInclusion
      (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι)) ≫ cmFixedInclusion = _
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc yActualFixedChartQuotientIso.inv,
    yActualFixedChartQuotientIso_inv_inclusion, ← Spec.map_comp_assoc,
    cmYFixedCoordinate_comp_origin]
  rfl

theorem cmActualZFixedPoint_inclusion_map :
    zActualFixedPoint ≫ cmFixedInclusion =
      Spec.map (CommRingCat.ofHom zOriginReceiver.toRingHom) ≫
        zCurveChartInclusion := by
  change ((Spec.map (CommRingCat.ofHom zFixedCoordinatePointEquiv.toRingHom) ≫
    zActualFixedChartQuotientIso.inv) ≫
    pullback.fst cmFixedInclusion
      (zReducedCubicChartIso.inv ≫ zCubicOpen.ι)) ≫ cmFixedInclusion = _
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc zActualFixedChartQuotientIso.inv,
    zActualFixedChartQuotientIso_inv_inclusion, ← Spec.map_comp_assoc,
    cmZFixedCoordinate_comp_origin]
  rfl

theorem cmActualYOrigin_inclusion_map :
    Spec.map (CommRingCat.ofHom yRestrictedOriginLift.toRingHom) ≫
      cmActualRestrictedYCurveOpen = yActualFixedPoint ≫ cmFixedInclusion := by
  rw [cmActualYFixedPoint_inclusion_map]
  change Spec.map (CommRingCat.ofHom yRestrictedOriginLift.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom
      (algebraMap YChartCubicRing YRestrictedQAway)) ≫ yCurveChartInclusion) = _
  rw [← Spec.map_comp_assoc, cmActualYRestrictedOrigin_comp]

theorem cmActualZOrigin_inclusion_map :
    Spec.map (CommRingCat.ofHom cmActualZOriginLift.toRingHom) ≫
      cmActualRestrictedZCurveOpen = zActualFixedPoint ≫ cmFixedInclusion := by
  rw [cmActualZFixedPoint_inclusion_map]
  change Spec.map (CommRingCat.ofHom cmActualZOriginLift.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom
      (algebraMap CurveRing ActualRestrictedZRing)) ≫ zCurveChartInclusion) = _
  rw [← Spec.map_comp_assoc, cmActualZRestrictedOrigin_comp]

theorem cmActualYOriginPoint_eq_fixed :
    cmActualYOriginPoint =
      cmFixedInclusion (yActualFixedPoint (IsLocalRing.closedPoint ℂ)) :=
  congrArg (fun f => f (IsLocalRing.closedPoint ℂ)) cmActualYOrigin_inclusion_map

theorem cmActualZOriginPoint_eq_fixed :
    cmActualZOriginPoint =
      cmFixedInclusion (zActualFixedPoint (IsLocalRing.closedPoint ℂ)) :=
  congrArg (fun f => f (IsLocalRing.closedPoint ℂ)) cmActualZOrigin_inclusion_map

theorem actualFixed_two_point_population (p : CMProjectiveFixedScheme) :
    p = yActualFixedPoint (IsLocalRing.closedPoint ℂ) ∨
      p = zActualFixedPoint (IsLocalRing.closedPoint ℂ) := by
  have hp : p ∈ yFixedOpenMap.opensRange ⊔ zFixedOpenMap.opensRange :=
    actualFixed_opens_cover.symm ▸
      (show p ∈ (⊤ : CMProjectiveFixedScheme.Opens) from trivial)
  rcases hp with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · left
    change yFixedOpenMap q =
      yFixedOpenMap (yGlobalFixedPullbackPointIso.inv (IsLocalRing.closedPoint ℂ))
    apply congrArg (fun q => yFixedOpenMap q)
    exact (yGlobalFixedPullbackPointIso.schemeIsoToHomeo.toEquiv.symm_apply_apply q).symm.trans
      (congrArg (fun r => yGlobalFixedPullbackPointIso.inv r) (Subsingleton.elim _ _))
  · right
    change zFixedOpenMap q =
      zFixedOpenMap (zGlobalFixedPullbackPointIso.inv (IsLocalRing.closedPoint ℂ))
    apply congrArg (fun q => zFixedOpenMap q)
    exact (zGlobalFixedPullbackPointIso.schemeIsoToHomeo.toEquiv.symm_apply_apply q).symm.trans
      (congrArg (fun r => zGlobalFixedPullbackPointIso.inv r) (Subsingleton.elim _ _))

theorem actualFixed_two_points_distinct :
    yActualFixedPoint (IsLocalRing.closedPoint ℂ) ≠
      zActualFixedPoint (IsLocalRing.closedPoint ℂ) := by
  intro h
  have hp : yActualFixedPoint (IsLocalRing.closedPoint ℂ) ∈
      yFixedOpenMap.opensRange ⊓ zFixedOpenMap.opensRange :=
    ⟨⟨yGlobalFixedPullbackPointIso.inv (IsLocalRing.closedPoint ℂ), rfl⟩,
      ⟨zGlobalFixedPullbackPointIso.inv (IsLocalRing.closedPoint ℂ), h.symm⟩⟩
  rw [disjoint_iff.mp actualFixed_opens_disjoint] at hp
  exact hp

theorem cmActualOriginPoints_distinct : cmActualYOriginPoint ≠ cmActualZOriginPoint := by
  rw [cmActualYOriginPoint_eq_fixed, cmActualZOriginPoint_eq_fixed]
  intro h
  exact actualFixed_two_points_distinct (cmFixedInclusion.isClosedEmbedding.injective h)

theorem cmActualFixed_support_eq_two_origins :
    (cmFixedInclusion.ker.support : Set CMProjectiveCubic) =
      {cmActualYOriginPoint, cmActualZOriginPoint} := by
  rw [Scheme.Hom.support_ker,
    cmFixedInclusion.isClosedEmbedding.isClosed_range.closure_eq]
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rcases actualFixed_two_point_population p with hp | hp
    · rw [hp, ← cmActualYOriginPoint_eq_fixed]
      exact Set.mem_insert _ _
    · rw [hp, ← cmActualZOriginPoint_eq_fixed]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · intro hx
    rcases hx with rfl | hx
    · exact ⟨yActualFixedPoint (IsLocalRing.closedPoint ℂ),
        cmActualYOriginPoint_eq_fixed.symm⟩
    · rcases hx with rfl
      exact ⟨zActualFixedPoint (IsLocalRing.closedPoint ℂ),
        cmActualZOriginPoint_eq_fixed.symm⟩

/-- The actual regular-principal fixed ideal has exactly these two support
points, with the measured multiplicity over each ambient local ring. This
consumes the map comparison and support enumeration before any degree sum. -/
theorem cmActualFixedCartier_two_origin_multiplicities :
    (Opens.grothendieckTopology CMProjectiveCubic).CoversTop cmActualFixedAffineOpen ∧
    (∀ i, IsRegular (cmActualFixedAffineEquation i)) ∧
    (∀ i, cmFixedInclusion.ker.ideal
      ⟨cmActualFixedAffineOpen i, cmActualFixedAffineOpen_isAffine i⟩ =
        Ideal.span {cmActualFixedAffineEquation i}) ∧
    (cmFixedInclusion.ker.support : Set CMProjectiveCubic) =
      {cmActualYOriginPoint, cmActualZOriginPoint} ∧
    cmActualYOriginPoint ≠ cmActualZOriginPoint ∧
    Module.length cmActualYOriginLocalRing
      (cmActualYOriginLocalRing ⧸ cmActualYOriginStalkIdeal) = 1 ∧
    Module.length cmActualZOriginLocalRing
      (cmActualZOriginLocalRing ⧸ cmActualZOriginStalkIdeal) = 1 :=
  ⟨cmActualFixedAffineOpen_coversTop, cmActualFixedAffineEquation_regular,
    cmActualFixedAffineEquation_ideal, cmActualFixed_support_eq_two_origins,
    cmActualOriginPoints_distinct, cmActualYStalkLengthOne, cmActualZStalkLengthOne⟩

#print axioms cmActualYOrigin_inclusion_map
#print axioms cmActualZOrigin_inclusion_map
#print axioms cmActualYOriginPoint_eq_fixed
#print axioms cmActualZOriginPoint_eq_fixed
#print axioms actualFixed_two_point_population
#print axioms actualFixed_two_points_distinct
#print axioms cmActualOriginPoints_distinct
#print axioms cmActualFixed_support_eq_two_origins
#print axioms cmActualFixedCartier_two_origin_multiplicities
end Holonics.Hodge.CMGraphSource
