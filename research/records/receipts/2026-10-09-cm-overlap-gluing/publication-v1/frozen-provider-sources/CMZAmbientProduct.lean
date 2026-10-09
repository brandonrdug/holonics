import CMZComplexBaseOnly
import CMZChartAction
import CMZScalarMap
import CMProjectiveFixedPullback
import CMGraphRegular
import Mathlib.AlgebraicGeometry.Pullbacks

/-! The actual Z x_C Z tensor spectrum is an open subscheme of the actual
projective E x_C E. Its graph and diagonal maps are compared through the
actual projections and actual complex base. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

abbrev CMActualAmbientProduct : Scheme := pullback cmConcreteCubicBase cmConcreteCubicBase
abbrev zCurveChartBase : Spec (.of CurveRing) ⟶ cmComplexPoint :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ CurveRing))
def zCurveChartInclusion : Spec (.of CurveRing) ⟶ CMProjectiveCubic :=
  zReducedCubicChartIso.inv ≫ zCubicOpen.ι
instance zCurveChartInclusion_open : IsOpenImmersion zCurveChartInclusion := by
  dsimp only [zCurveChartInclusion]
  infer_instance
@[reassoc] theorem zCurveChart_complex_base :
    zCurveChartInclusion ≫ cmConcreteCubicBase = zCurveChartBase := zActualChart_complex_base

theorem zIotaAlgebraMap_eq_source : zIotaAlgebraMap = iota := by
  apply curveRing_hom_ext
  · change zIotaCoordinateRing (AdjoinRoot.of squareCurve.toAffine.polynomial Polynomial.X) = iota u
    rw [zIotaCoordinateRing_u]
    exact (phasePullback_u Complex.I Complex.I_sq).symm
  · change zIotaCoordinateRing (AdjoinRoot.root squareCurve.toAffine.polynomial) = iota v
    rw [zIotaCoordinateRing_v]
    simpa only [CurveRing, v, iota, Algebra.smul_def,
      WeierstrassCurve.Affine.CoordinateRing.instAlgebra] using
      (phasePullback_v Complex.I Complex.I_sq).symm

@[reassoc] theorem zCurveChart_iota_square :
    Spec.map (CommRingCat.ofHom iota.toRingHom) ≫ zCurveChartInclusion =
      zCurveChartInclusion ≫ cubicIota.hom := by
  rw [← zIotaAlgebraMap_eq_source]
  change Spec.map (CommRingCat.ofHom zIotaCoordinateRing) ≫
    (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) =
      (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) ≫ cubicIotaHom
  rw [Category.assoc]
  exact zCubicChart_iota_inclusion_square.symm

def zProductChartInclusion : Spec (.of ProductRing) ⟶ CMActualAmbientProduct :=
  (pullbackSpecIso ℂ CurveRing CurveRing).inv ≫
    pullback.map zCurveChartBase zCurveChartBase cmConcreteCubicBase cmConcreteCubicBase
      zCurveChartInclusion zCurveChartInclusion (𝟙 cmComplexPoint)
      (by rw [Category.comp_id, zCurveChart_complex_base])
      (by rw [Category.comp_id, zCurveChart_complex_base])
instance zProductChartInclusion_open : IsOpenImmersion zProductChartInclusion := by
  dsimp only [zProductChartInclusion]
  infer_instance

@[reassoc] theorem zProductChart_first_projection :
    zProductChartInclusion ≫ pullback.fst cmConcreteCubicBase cmConcreteCubicBase =
      Spec.map (CommRingCat.ofHom graphLeft.toRingHom) ≫ zCurveChartInclusion := by
  dsimp only [zProductChartInclusion]
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]
  rfl
@[reassoc] theorem zProductChart_second_projection :
    zProductChartInclusion ≫ pullback.snd cmConcreteCubicBase cmConcreteCubicBase =
      Spec.map (CommRingCat.ofHom graphRight.toRingHom) ≫ zCurveChartInclusion := by
  dsimp only [zProductChartInclusion]
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd]
  rfl

#print axioms zProductChartInclusion_open

def zTensorGraph : Spec (.of CurveRing) ⟶ Spec (.of ProductRing) :=
  Spec.map (CommRingCat.ofHom graphReceiver.toRingHom)
def zDiagonalReceiver : ProductRing →ₐ[ℂ] CurveRing := Algebra.TensorProduct.lmul' ℂ
def zTensorDiagonal : Spec (.of CurveRing) ⟶ Spec (.of ProductRing) :=
  Spec.map (CommRingCat.ofHom zDiagonalReceiver.toRingHom)

@[reassoc] theorem zTensorGraph_actual_square :
    zTensorGraph ≫ zProductChartInclusion = zCurveChartInclusion ≫ cmConcreteComplexGraph := by
  dsimp only [zTensorGraph]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [zProductChart_first_projection,
      ← Spec.map_comp_assoc, cmConcreteComplexGraph_first_projection]
    have h : CommRingCat.ofHom graphLeft.toRingHom ≫
        CommRingCat.ofHom graphReceiver.toRingHom = 𝟙 (CommRingCat.of CurveRing) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact graphReceiver_left a
    rw [h, Spec.map_id, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc]
    rw [zProductChart_second_projection,
      ← Spec.map_comp_assoc, cmConcreteComplexGraph_second_projection]
    have h : CommRingCat.ofHom graphRight.toRingHom ≫
        CommRingCat.ofHom graphReceiver.toRingHom = CommRingCat.ofHom iota.toRingHom := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact graphReceiver_right a
    rw [h, zCurveChart_iota_square]
@[reassoc] theorem zTensorDiagonal_actual_square :
    zTensorDiagonal ≫ zProductChartInclusion = zCurveChartInclusion ≫ cmComplexDiagonal := by
  dsimp only [zTensorDiagonal]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [zProductChart_first_projection, ← Spec.map_comp_assoc]
    have h : CommRingCat.ofHom graphLeft.toRingHom ≫
        CommRingCat.ofHom zDiagonalReceiver.toRingHom = 𝟙 (CommRingCat.of CurveRing) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      simp [zDiagonalReceiver, graphLeft]
    rw [h, Spec.map_id, Category.id_comp]
    simp only [Category.assoc, cmComplexDiagonal, pullback.diagonal_fst, Category.comp_id]
  · simp only [Category.assoc]
    rw [zProductChart_second_projection, ← Spec.map_comp_assoc]
    have h : CommRingCat.ofHom graphRight.toRingHom ≫
        CommRingCat.ofHom zDiagonalReceiver.toRingHom = 𝟙 (CommRingCat.of CurveRing) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      simp [zDiagonalReceiver, graphRight]
    rw [h, Spec.map_id, Category.id_comp]
    simp only [Category.assoc, cmComplexDiagonal, pullback.diagonal_snd, Category.comp_id]

#print axioms zIotaAlgebraMap_eq_source
#print axioms zProductChartInclusion_open
#print axioms zTensorGraph_actual_square
#print axioms zTensorDiagonal_actual_square
end Holonics.Hodge.CMGraphSource
