import CMActualRestrictedChartCartierData
import CMGlobalAmbientFaceCover
import CMGlobalRegularEquationCover

/-! The smaller fixed-point opens cover the actual fixed support.

The actual chart ideal comparisons are consumed with denominator units in
their actual difference-ideal quotients. The quotient inclusion factors
through the specified localization spectrum map, so its support lies in
that principal open. Full Y/Z curve coverage supplies the charts, not the
principal-open conclusion.

agent-inferred: construct this factorization through Away.lift rather than
infer support coverage from coordinate length or an abstract point count.
The recorded failure avoided is a source map whose consumer was assumed.
The helical pair interaction stays attached through its navigator faces,
cell holonomy and tube; no intersection or Hodge pairing is asserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
universe u

theorem cmActualFixedY_Q_quotient_unit :
    IsUnit (Ideal.Quotient.mk yFixedDifferenceIdeal yRestrictedQ) := by
  have hmem : yRestrictedQ - 1 ∈ yFixedDifferenceIdeal := by
    rw [yFixedDifferenceIdeal_eq_origin, ← yOriginReceiver_ker_eq_zeroPointIdeal]
    change yOriginReceiver (yRestrictedQ - 1) = 0
    rw [map_sub, map_one, yRestrictedQ_origin_eq_one, sub_self]
  have hzero : Ideal.Quotient.mk yFixedDifferenceIdeal (yRestrictedQ - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_sub, map_one] at hzero
  rw [sub_eq_zero.mp hzero]
  exact isUnit_one

theorem cmActualFixedZ_factor_quotient_unit :
    IsUnit (Ideal.Quotient.mk zFixedDifferenceIdeal (u ^ 2 - 1)) := by
  have hu : u ∈ zFixedDifferenceIdeal := by
    rw [cmActualFixedZDifference_eq_fixedIdeal]
    exact u_mem_fixedIdeal
  have hzero : Ideal.Quotient.mk zFixedDifferenceIdeal u = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hu
  have hfactor : Ideal.Quotient.mk zFixedDifferenceIdeal (u ^ 2 - 1) = -1 := by
    rw [map_sub, map_pow, map_one, hzero]
    norm_num
  rw [hfactor]
  exact isUnit_one.neg

/-- The actual quotient inclusion factors through the actual localization
map when the denominator is a unit in that quotient. -/
theorem coordinateQuotientSupport_mem_awayRange {R : CommRingCat.{u}}
    (J : Ideal R) (s : R) (hs : IsUnit (Ideal.Quotient.mk J s))
    (x : Spec R)
    (hx : x ∈ (Scheme.IdealSheafData.ofIdealTop
      (J.map (Scheme.ΓSpecIso R).inv.hom)).support) :
    x ∈ (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away s)))).opensRange := by
  let q : Spec (.of (R ⧸ J)) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have hker : q.ker = Scheme.IdealSheafData.ofIdealTop
      (J.map (Scheme.ΓSpecIso R).inv.hom) := by
    dsimp only [q]
    rw [specMap_idealSheaf_coordinates, CommRingCat.hom_ofHom, Ideal.mk_ker]
  have hqx : x ∈ (q.ker.support : Set (Spec R)) := by
    rw [hker]
    exact hx
  rw [Scheme.Hom.support_ker, q.isClosedEmbedding.isClosed_range.closure_eq] at hqx
  obtain ⟨z, rfl⟩ := hqx
  let L : Localization.Away s →+* (R ⧸ J) :=
    IsLocalization.Away.lift (g := Ideal.Quotient.mk J) s hs
  have hcomp : CommRingCat.ofHom (algebraMap R (Localization.Away s)) ≫
      CommRingCat.ofHom L = CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    apply CommRingCat.hom_ext
    change L.comp (algebraMap R (Localization.Away s)) = Ideal.Quotient.mk J
    exact IsLocalization.Away.lift_comp s hs
  have hq : q = Spec.map (CommRingCat.ofHom L) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) := by
    rw [← Spec.map_comp, hcomp]
  refine ⟨Spec.map (CommRingCat.ofHom L) z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hq]
  rfl

/-- Consume the actual ideal restriction and the quotient factorization at
the actual curve chart inclusion. -/
theorem coordinateIdealSupport_refines_away {R : CommRingCat.{u}} {X : Scheme.{u}}
    (I : X.IdealSheafData) (J : Ideal R) (j : Spec R ⟶ X) [IsOpenImmersion j]
    (hj : I.comap j = Scheme.IdealSheafData.ofIdealTop
      (J.map (Scheme.ΓSpecIso R).inv.hom))
    (s : R) (hs : IsUnit (Ideal.Quotient.mk J s))
    (x : Spec R) (hx : j x ∈ I.support) :
    j x ∈ (ambientAwayOpen j s).opensRange := by
  have hlocal : x ∈ (I.comap j).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  rw [hj] at hlocal
  obtain ⟨z, hz⟩ := coordinateQuotientSupport_mem_awayRange J s hs x hlocal
  refine ⟨z, ?_⟩
  change j (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) z) = j x
  exact congrArg j hz

theorem cmActualFixedY_support_refines_Q (x : Spec (.of YChartCubicRing))
    (hx : yCurveChartInclusion x ∈ cmFixedInclusion.ker.support) :
    yCurveChartInclusion x ∈ cmActualRestrictedYCurveOpen.opensRange := by
  exact coordinateIdealSupport_refines_away
    (R := CommRingCat.of YChartCubicRing) (X := CMProjectiveCubic)
    cmFixedInclusion.ker yFixedDifferenceIdeal yCurveChartInclusion
    cmActualFixedY_ideal_coordinates yRestrictedQ cmActualFixedY_Q_quotient_unit x hx

theorem cmActualFixedZ_support_refines_factor (x : Spec (.of CurveRing))
    (hx : zCurveChartInclusion x ∈ cmFixedInclusion.ker.support) :
    zCurveChartInclusion x ∈ cmActualRestrictedZCurveOpen.opensRange := by
  exact coordinateIdealSupport_refines_away
    (R := CommRingCat.of CurveRing) (X := CMProjectiveCubic)
    cmFixedInclusion.ker zFixedDifferenceIdeal zCurveChartInclusion
    cmActualFixedZ_ideal_coordinates (u ^ 2 - 1) cmActualFixedZ_factor_quotient_unit x hx

theorem cmActualFixed_restricted_support_cover (x : CMProjectiveCubic)
    (hx : x ∈ cmFixedInclusion.ker.support) :
    x ∈ cmActualRestrictedYCurveOpen.opensRange ∨
      x ∈ cmActualRestrictedZCurveOpen.opensRange := by
  rcases actual_curve_chart_range_cover x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl (cmActualFixedY_support_refines_Q y hx)
  · exact Or.inr (cmActualFixedZ_support_refines_factor z hx)

theorem cmActualFixed_restricted_complement_cover (x : CMProjectiveCubic) :
    x ∈ cmActualRestrictedYCurveOpen.opensRange ∨
      x ∈ cmActualRestrictedZCurveOpen.opensRange ∨
        x ∈ idealComplementOpen cmFixedInclusion.ker := by
  by_cases hx : x ∈ cmFixedInclusion.ker.support
  · rcases cmActualFixed_restricted_support_cover x hx with hY | hZ
    · exact Or.inl hY
    · exact Or.inr (Or.inl hZ)
  · exact Or.inr (Or.inr hx)

#print axioms cmActualFixedY_Q_quotient_unit
#print axioms cmActualFixedZ_factor_quotient_unit
#print axioms coordinateQuotientSupport_mem_awayRange
#print axioms coordinateIdealSupport_refines_away
#print axioms cmActualFixedY_support_refines_Q
#print axioms cmActualFixedZ_support_refines_factor
#print axioms cmActualFixed_restricted_support_cover
#print axioms cmActualFixed_restricted_complement_cover
end Holonics.Hodge.CMGraphSource
