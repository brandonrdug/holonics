import CMYAmbientEquations
import CMYComplexBaseOnly
import CMYChartAction
import CMZAmbientProduct

/-! The actual Y x_C Y tensor spectrum is an open subscheme of the actual
projective E x_C E. Its graph and diagonal maps are compared through the
actual projections and actual complex base. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

abbrev yCurveChartBase : Spec (.of YChartCubicRing) ⟶ cmComplexPoint :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ YChartCubicRing))
def yCurveChartInclusion : Spec (.of YChartCubicRing) ⟶ CMProjectiveCubic :=
  yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι
instance yCurveChartInclusion_open : IsOpenImmersion yCurveChartInclusion := by
  dsimp only [yCurveChartInclusion]
  infer_instance
@[reassoc] theorem yCurveChart_complex_base :
    yCurveChartInclusion ≫ cmConcreteCubicBase = yCurveChartBase := yActualChart_complex_base

@[reassoc] theorem yCurveChart_iota_square :
    Spec.map (CommRingCat.ofHom yIotaAlgebraMap.toRingHom) ≫ yCurveChartInclusion =
      yCurveChartInclusion ≫ cubicIota.hom := by
  change Spec.map (CommRingCat.ofHom yIotaCoordinateRing) ≫
    (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) =
      (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) ≫ cubicIotaHom
  rw [Category.assoc]
  exact yCubicChart_iota_inclusion_square.symm

def yProductChartInclusion : Spec (.of YProductRing) ⟶ CMActualAmbientProduct :=
  (pullbackSpecIso ℂ YChartCubicRing YChartCubicRing).inv ≫
    pullback.map yCurveChartBase yCurveChartBase cmConcreteCubicBase cmConcreteCubicBase
      yCurveChartInclusion yCurveChartInclusion (𝟙 cmComplexPoint)
      (by rw [Category.comp_id, yCurveChart_complex_base])
      (by rw [Category.comp_id, yCurveChart_complex_base])
instance yProductChartInclusion_open : IsOpenImmersion yProductChartInclusion := by
  dsimp only [yProductChartInclusion]
  infer_instance

@[reassoc] theorem yProductChart_first_projection :
    yProductChartInclusion ≫ pullback.fst cmConcreteCubicBase cmConcreteCubicBase =
      Spec.map (CommRingCat.ofHom yLeft.toRingHom) ≫ yCurveChartInclusion := by
  dsimp only [yProductChartInclusion]
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]
  rfl
@[reassoc] theorem yProductChart_second_projection :
    yProductChartInclusion ≫ pullback.snd cmConcreteCubicBase cmConcreteCubicBase =
      Spec.map (CommRingCat.ofHom yRight.toRingHom) ≫ yCurveChartInclusion := by
  dsimp only [yProductChartInclusion]
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd]
  rfl

#print axioms yProductChartInclusion_open

def yTensorGraph : Spec (.of YChartCubicRing) ⟶ Spec (.of YProductRing) :=
  Spec.map (CommRingCat.ofHom yGraphReceiver.toRingHom)
def yTensorDiagonal : Spec (.of YChartCubicRing) ⟶ Spec (.of YProductRing) :=
  Spec.map (CommRingCat.ofHom yDiagonalReceiver.toRingHom)

@[reassoc] theorem yTensorGraph_actual_square :
    yTensorGraph ≫ yProductChartInclusion = yCurveChartInclusion ≫ cmConcreteComplexGraph := by
  dsimp only [yTensorGraph]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [yProductChart_first_projection,
      ← Spec.map_comp_assoc, cmConcreteComplexGraph_first_projection]
    have h : CommRingCat.ofHom yLeft.toRingHom ≫
        CommRingCat.ofHom yGraphReceiver.toRingHom = 𝟙 (CommRingCat.of YChartCubicRing) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact yGraphReceiver_left a
    rw [h, Spec.map_id, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc]
    rw [yProductChart_second_projection,
      ← Spec.map_comp_assoc, cmConcreteComplexGraph_second_projection]
    have h : CommRingCat.ofHom yRight.toRingHom ≫
        CommRingCat.ofHom yGraphReceiver.toRingHom = CommRingCat.ofHom yIotaAlgebraMap.toRingHom := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact yGraphReceiver_right a
    rw [h, yCurveChart_iota_square]
@[reassoc] theorem yTensorDiagonal_actual_square :
    yTensorDiagonal ≫ yProductChartInclusion = yCurveChartInclusion ≫ cmComplexDiagonal := by
  dsimp only [yTensorDiagonal]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [yProductChart_first_projection, ← Spec.map_comp_assoc]
    have h : CommRingCat.ofHom yLeft.toRingHom ≫
        CommRingCat.ofHom yDiagonalReceiver.toRingHom = 𝟙 (CommRingCat.of YChartCubicRing) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      simp [yDiagonalReceiver, yLeft]
    rw [h, Spec.map_id, Category.id_comp]
    simp only [Category.assoc, cmComplexDiagonal, pullback.diagonal_fst, Category.comp_id]
  · simp only [Category.assoc]
    rw [yProductChart_second_projection, ← Spec.map_comp_assoc]
    have h : CommRingCat.ofHom yRight.toRingHom ≫
        CommRingCat.ofHom yDiagonalReceiver.toRingHom = 𝟙 (CommRingCat.of YChartCubicRing) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      simp [yDiagonalReceiver, yRight]
    rw [h, Spec.map_id, Category.id_comp]
    simp only [Category.assoc, cmComplexDiagonal, pullback.diagonal_snd, Category.comp_id]

#print axioms yProductChartInclusion_open
#print axioms yTensorGraph_actual_square
#print axioms yTensorDiagonal_actual_square
end Holonics.Hodge.CMGraphSource
