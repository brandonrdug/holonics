import CMActualFixedIdealJoin
import CMYActualFixedPointMap
import CMZActualFixedPointIso
import CMYAmbientProduct
import CMZAmbientProduct
import CMSpecKernelCoordinates
import CMOpenCoordinateExtension

/-! The actual projective fixed inclusion, restricted to its actual curve
charts, has the previously constructed affine difference-quotient ideal.
The quotient comparison is consumed through its inclusion equation. Its
localization is then transported through the actual spectrum open map.

The recovered fixed-chart dependencies have historical passing objects;
the new consumers require their own sealed checks against those exact inputs.
No smoothness, intersection-degree, or cohomological comparison is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
universe u

local instance : IsClosedImmersion cmFixedInclusion :=
  cmFixedInclusion_closedImmersion

private theorem closedPullbackKernelSnd {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (j : Y ⟶ Z) [IsClosedImmersion f] :
    (pullback.snd f j).ker = f.ker.comap j := by
  calc
    (pullback.snd f j).ker =
        ((pullbackSymmetry f j).hom ≫ pullback.fst j f).ker := by
      rw [pullbackSymmetry_hom_comp_fst]
    _ = (pullback.fst j f).ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = f.ker.comap j := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion f j

/-- The chart's transported action is the constructed affine CM action, so
its difference ideal is the existing fixed ideal on the very same ring. -/
theorem cmActualFixedZDifference_eq_fixedIdeal :
    zFixedDifferenceIdeal = fixedIdeal := by
  have hz : zIotaCoordinateRing = iota.toRingHom :=
    congrArg (fun f : CurveRing →ₐ[ℂ] CurveRing => f.toRingHom)
      zIotaAlgebraMap_eq_source
  change Ideal.span (Set.range fun a : CurveRing => zIotaCoordinateRing a - a) = _
  rw [hz]
  rfl

theorem cmActualFixedY_ideal_coordinates :
    cmFixedInclusion.ker.comap yCurveChartInclusion =
      Scheme.IdealSheafData.ofIdealTop
        (yFixedDifferenceIdeal.map (Scheme.ΓSpecIso (.of YChartCubicRing)).inv.hom) := by
  change cmFixedInclusion.ker.comap
      (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) = _
  rw [← closedPullbackKernelSnd,
    ← Scheme.Hom.ker_comp_of_isIso yActualFixedChartQuotientIso.inv,
    yActualFixedChartQuotientIso_inv_inclusion,
    specMap_idealSheaf_coordinates, CommRingCat.hom_ofHom, Ideal.mk_ker]

theorem cmActualFixedZ_ideal_coordinates :
    cmFixedInclusion.ker.comap zCurveChartInclusion =
      Scheme.IdealSheafData.ofIdealTop
        (zFixedDifferenceIdeal.map (Scheme.ΓSpecIso (.of CurveRing)).inv.hom) := by
  change cmFixedInclusion.ker.comap
      (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) = _
  rw [← closedPullbackKernelSnd,
    ← Scheme.Hom.ker_comp_of_isIso zActualFixedChartQuotientIso.inv,
    zActualFixedChartQuotientIso_inv_inclusion,
    specMap_idealSheaf_coordinates, CommRingCat.hom_ofHom, Ideal.mk_ker]

/-- The actual Y-chart equation restricts through a specified affine open
spectrum map. This equality retains the real projective inclusion. -/
theorem cmActualFixedY_ideal_coordinates_restrict {S : CommRingCat}
    (f : CommRingCat.of YChartCubicRing ⟶ S) [IsOpenImmersion (Spec.map f)] :
    cmFixedInclusion.ker.comap (Spec.map f ≫ yCurveChartInclusion) =
      Scheme.IdealSheafData.ofIdealTop
        ((yFixedDifferenceIdeal.map f.hom).map (Scheme.ΓSpecIso S).inv.hom) := by
  rw [Scheme.IdealSheafData.comap_comp, cmActualFixedY_ideal_coordinates,
    specOpen_coordinateIdeal_comap]

theorem cmActualFixedZ_ideal_coordinates_restrict {S : CommRingCat}
    (f : CommRingCat.of CurveRing ⟶ S) [IsOpenImmersion (Spec.map f)] :
    cmFixedInclusion.ker.comap (Spec.map f ≫ zCurveChartInclusion) =
      Scheme.IdealSheafData.ofIdealTop
        ((zFixedDifferenceIdeal.map f.hom).map (Scheme.ΓSpecIso S).inv.hom) := by
  rw [Scheme.IdealSheafData.comap_comp, cmActualFixedZ_ideal_coordinates,
    specOpen_coordinateIdeal_comap]

#print axioms cmActualFixedY_ideal_coordinates
#print axioms cmActualFixedZDifference_eq_fixedIdeal
#print axioms cmActualFixedZ_ideal_coordinates
#print axioms cmActualFixedY_ideal_coordinates_restrict
#print axioms cmActualFixedZ_ideal_coordinates_restrict
end Holonics.Hodge.CMGraphSource
