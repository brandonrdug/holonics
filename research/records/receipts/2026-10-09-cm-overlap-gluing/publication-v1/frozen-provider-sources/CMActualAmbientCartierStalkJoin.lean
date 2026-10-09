import CMActualAmbientCartierStalk
import CMActualRestrictedYEquation
import CMActualRestrictedZEquation
import CMYAmbientProduct
import CMZAmbientProduct
import CMActualYRegularFaces
import CMActualZRegularFaces

/-! Actual local-chart factorization at the two fixed origins.

This chart join constructs the ambient localized chart points from the
actual origin receivers and proves that the actual graph maps them to the
actual ambient stalk points. The Y and Z restricted equations stay attached
to the checked actual graph squares. No desired point equality, stalk map,
kernel, quotient equivalence, or Tor vanishing is assumed.

The external computational object is the helical pair interaction; this join
touches faces and placement, cell holonomy, and tube, keeping helix, pair,
and tower thread attached. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

def yAmbientQToRestricted : Localization.Away yDiagonalQ →+* YRestrictedQAway :=
  IsLocalization.Away.lift (g := yRestrictedMap) yDiagonalQ yRestrictedQ_isUnit

theorem yAmbientQToRestricted_comp :
    CommRingCat.ofHom (algebraMap YProductRing (Localization.Away yDiagonalQ)) ≫
      CommRingCat.ofHom yAmbientQToRestricted =
        CommRingCat.ofHom yRestrictedMap := by
  apply CommRingCat.hom_ext
  change yAmbientQToRestricted.comp
      (algebraMap YProductRing (Localization.Away yDiagonalQ)) = yRestrictedMap
  exact IsLocalization.Away.lift_comp yDiagonalQ yRestrictedQ_isUnit

theorem yRestricted_actual_graph_square :
    Spec.map (CommRingCat.ofHom yRestrictedMap) ≫ yProductChartInclusion =
      cmActualRestrictedYCurveOpen ≫ cmConcreteComplexGraph := by
  change Spec.map (CommRingCat.ofHom yGraphReceiver.toRingHom ≫
      CommRingCat.ofHom (algebraMap YChartCubicRing YRestrictedQAway)) ≫ yProductChartInclusion =
    (Spec.map (CommRingCat.ofHom (algebraMap YChartCubicRing YRestrictedQAway)) ≫ yCurveChartInclusion) ≫
      cmConcreteComplexGraph
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (CommRingCat.ofHom (algebraMap YChartCubicRing YRestrictedQAway)) ≫
    yTensorGraph ≫ yProductChartInclusion = _
  rw [yTensorGraph_actual_square, Category.assoc]

theorem yAmbientQ_actual_graph_square :
    Spec.map (CommRingCat.ofHom yAmbientQToRestricted) ≫ yDiagonalQAmbientOpen =
      cmActualRestrictedYCurveOpen ≫ cmConcreteComplexGraph := by
  calc
    Spec.map (CommRingCat.ofHom yAmbientQToRestricted) ≫ yDiagonalQAmbientOpen =
        Spec.map (CommRingCat.ofHom yRestrictedMap) ≫ yProductChartInclusion := by
          dsimp only [yDiagonalQAmbientOpen, ambientAwayOpen]
          rw [← Spec.map_comp_assoc]
          rw [yAmbientQToRestricted_comp]
    _ = cmActualRestrictedYCurveOpen ≫ cmConcreteComplexGraph :=
      yRestricted_actual_graph_square

def yAmbientQOriginPoint : Spec (.of (Localization.Away yDiagonalQ)) :=
  Spec.map (CommRingCat.ofHom yAmbientQToRestricted)
    (specResiduePoint (.of YRestrictedQAway) yRestrictedOriginLift.toRingHom)

theorem yAmbientQOriginPoint_actual_image :
    yDiagonalQAmbientOpen yAmbientQOriginPoint =
      cmConcreteComplexGraph cmActualYOriginPoint := by
  have h := congrArg (fun f => f
      (specResiduePoint (.of YRestrictedQAway) yRestrictedOriginLift.toRingHom))
      yAmbientQ_actual_graph_square
  change yDiagonalQAmbientOpen yAmbientQOriginPoint =
    cmConcreteComplexGraph cmActualYOriginPoint at h
  exact h

def zRestrictedMap : ProductRing →+* ActualRestrictedZRing :=
  (algebraMap CurveRing ActualRestrictedZRing).comp graphReceiver.toRingHom

theorem zRestrictedDenominator_unit : IsUnit (zRestrictedMap diagonalCubicFactor) := by
  change IsUnit (algebraMap CurveRing ActualRestrictedZRing
    (graphReceiver diagonalCubicFactor))
  rw [graphReceiver_diagonal_factor]
  exact IsLocalization.Away.algebraMap_isUnit (u ^ 2 - 1)

def zAmbientFactorToRestricted :
    Localization.Away diagonalCubicFactor →+* ActualRestrictedZRing :=
  IsLocalization.Away.lift (g := zRestrictedMap) diagonalCubicFactor
    zRestrictedDenominator_unit

theorem zAmbientFactorToRestricted_comp :
    CommRingCat.ofHom (algebraMap ProductRing
      (Localization.Away diagonalCubicFactor)) ≫
      CommRingCat.ofHom zAmbientFactorToRestricted =
        CommRingCat.ofHom zRestrictedMap := by
  apply CommRingCat.hom_ext
  change zAmbientFactorToRestricted.comp
      (algebraMap ProductRing (Localization.Away diagonalCubicFactor)) = zRestrictedMap
  exact IsLocalization.Away.lift_comp diagonalCubicFactor zRestrictedDenominator_unit

theorem zRestricted_actual_graph_square :
    Spec.map (CommRingCat.ofHom zRestrictedMap) ≫ zProductChartInclusion =
      cmActualRestrictedZCurveOpen ≫ cmConcreteComplexGraph := by
  change Spec.map (CommRingCat.ofHom graphReceiver.toRingHom ≫
      CommRingCat.ofHom (algebraMap CurveRing ActualRestrictedZRing)) ≫ zProductChartInclusion =
    (Spec.map (CommRingCat.ofHom (algebraMap CurveRing ActualRestrictedZRing)) ≫ zCurveChartInclusion) ≫
      cmConcreteComplexGraph
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (CommRingCat.ofHom (algebraMap CurveRing ActualRestrictedZRing)) ≫
    zTensorGraph ≫ zProductChartInclusion = _
  rw [zTensorGraph_actual_square, Category.assoc]

theorem zAmbientFactor_actual_graph_square :
    Spec.map (CommRingCat.ofHom zAmbientFactorToRestricted) ≫ zDiagonalFactorAmbientOpen =
      cmActualRestrictedZCurveOpen ≫ cmConcreteComplexGraph := by
  calc
    Spec.map (CommRingCat.ofHom zAmbientFactorToRestricted) ≫
        zDiagonalFactorAmbientOpen =
        Spec.map (CommRingCat.ofHom zRestrictedMap) ≫ zProductChartInclusion := by
          dsimp only [zDiagonalFactorAmbientOpen, ambientAwayOpen]
          rw [← Spec.map_comp_assoc]
          rw [zAmbientFactorToRestricted_comp]
    _ = cmActualRestrictedZCurveOpen ≫ cmConcreteComplexGraph :=
      zRestricted_actual_graph_square





def zAmbientFactorOriginPoint : Spec (.of (Localization.Away diagonalCubicFactor)) :=
  Spec.map (CommRingCat.ofHom zAmbientFactorToRestricted)
    (specResiduePoint (.of ActualRestrictedZRing) cmActualZOriginLift.toRingHom)

theorem zAmbientFactorOriginPoint_actual_image :
    zDiagonalFactorAmbientOpen zAmbientFactorOriginPoint =
      cmConcreteComplexGraph cmActualZOriginPoint := by
  have h := congrArg (fun f => f
      (specResiduePoint (.of ActualRestrictedZRing) cmActualZOriginLift.toRingHom))
      zAmbientFactor_actual_graph_square
  change zDiagonalFactorAmbientOpen zAmbientFactorOriginPoint =
    cmConcreteComplexGraph cmActualZOriginPoint at h
  exact h

theorem yActualGraphPoint_mem_QOpen :
    cmConcreteComplexGraph cmActualYOriginPoint ∈
      cmActualDiagonalAffineOpen .A := by
  simpa only [cmActualDiagonalAffineOpen, Scheme.Hom.image_top_eq_opensRange] using
    (show cmConcreteComplexGraph cmActualYOriginPoint ∈
        yDiagonalQAmbientOpen.opensRange from
      ⟨yAmbientQOriginPoint, yAmbientQOriginPoint_actual_image⟩)

theorem zActualGraphPoint_mem_factorOpen :
    cmConcreteComplexGraph cmActualZOriginPoint ∈
      cmActualDiagonalAffineOpen .V := by
  simpa only [cmActualDiagonalAffineOpen, Scheme.Hom.image_top_eq_opensRange] using
    (show cmConcreteComplexGraph cmActualZOriginPoint ∈
        zDiagonalFactorAmbientOpen.opensRange from
      ⟨zAmbientFactorOriginPoint, zAmbientFactorOriginPoint_actual_image⟩)

abbrev cmActualYAmbientDiagonalGerm : cmActualYAmbientLocalRing :=
  (CMActualAmbientProduct.presheaf.germ (cmActualDiagonalAffineOpen .A)
    (cmConcreteComplexGraph cmActualYOriginPoint) yActualGraphPoint_mem_QOpen).hom
      (cmActualDiagonalAffineEquation .A)

abbrev cmActualZAmbientDiagonalGerm : cmActualZAmbientLocalRing :=
  (CMActualAmbientProduct.presheaf.germ (cmActualDiagonalAffineOpen .V)
    (cmConcreteComplexGraph cmActualZOriginPoint) zActualGraphPoint_mem_factorOpen).hom
      (cmActualDiagonalAffineEquation .V)

theorem cmActualYAmbientDiagonalGerm_regular :
    IsRegular cmActualYAmbientDiagonalGerm := by
  exact affineSection_germ_regular _ (cmActualDiagonalAffineOpen_isAffine .A)
    (cmConcreteComplexGraph cmActualYOriginPoint) yActualGraphPoint_mem_QOpen _
    (cmActualDiagonalAffineEquation_regular .A)

theorem cmActualZAmbientDiagonalGerm_regular :
    IsRegular cmActualZAmbientDiagonalGerm := by
  exact affineSection_germ_regular _ (cmActualDiagonalAffineOpen_isAffine .V)
    (cmConcreteComplexGraph cmActualZOriginPoint) zActualGraphPoint_mem_factorOpen _
    (cmActualDiagonalAffineEquation_regular .V)

theorem cmActualYAmbientDiagonalGerm_principal :
    (cmComplexDiagonal.ker.ideal
      ⟨cmActualDiagonalAffineOpen .A, cmActualDiagonalAffineOpen_isAffine .A⟩).map
        (CMActualAmbientProduct.presheaf.germ (cmActualDiagonalAffineOpen .A)
          (cmConcreteComplexGraph cmActualYOriginPoint) yActualGraphPoint_mem_QOpen).hom =
      Ideal.span {cmActualYAmbientDiagonalGerm} := by
  rw [cmActualDiagonalAffineEquation_ideal, Ideal.map_span, Set.image_singleton]

theorem cmActualZAmbientDiagonalGerm_principal :
    (cmComplexDiagonal.ker.ideal
      ⟨cmActualDiagonalAffineOpen .V, cmActualDiagonalAffineOpen_isAffine .V⟩).map
        (CMActualAmbientProduct.presheaf.germ (cmActualDiagonalAffineOpen .V)
          (cmConcreteComplexGraph cmActualZOriginPoint) zActualGraphPoint_mem_factorOpen).hom =
      Ideal.span {cmActualZAmbientDiagonalGerm} := by
  rw [cmActualDiagonalAffineEquation_ideal, Ideal.map_span, Set.image_singleton]

theorem yRestricted_diagonal_image_regular :
    IsRegular (yRestrictedMap yDiagonalAEquation) := by
  have h : yRestrictedMap yDiagonalAEquation =
      algebraMap ℂ YRestrictedQAway (Complex.I - 1) * yRestrictedA := by
    change algebraMap YChartCubicRing YRestrictedQAway
      (yGraphReceiver yDiagonalAEquation) = _
    rw [yRestrictedGraphDiagonalA, map_mul,
      ← IsScalarTower.algebraMap_apply ℂ YChartCubicRing YRestrictedQAway]
  rw [h]
  exact yRestrictedI_minus_one_isUnit.isRegular.mul yRestrictedA_regular

theorem yRestricted_diagonal_image_span :
    Ideal.span {yRestrictedMap yDiagonalAEquation} =
      Ideal.span {yRestrictedA} := by
  have h : yRestrictedMap yDiagonalAEquation =
      algebraMap ℂ YRestrictedQAway (Complex.I - 1) * yRestrictedA := by
    change algebraMap YChartCubicRing YRestrictedQAway
      (yGraphReceiver yDiagonalAEquation) = _
    rw [yRestrictedGraphDiagonalA, map_mul,
      ← IsScalarTower.algebraMap_apply ℂ YChartCubicRing YRestrictedQAway]
  rw [h]
  exact Ideal.span_singleton_mul_left_unit yRestrictedI_minus_one_isUnit yRestrictedA


theorem zRestrictedI_minus_one_isUnit :
    IsUnit (algebraMap ℂ ActualRestrictedZRing (Complex.I - 1)) := by
  apply IsUnit.map
  apply isUnit_iff_ne_zero.mpr
  intro he
  have him := congrArg Complex.im he
  norm_num at him

theorem zRestricted_diagonal_image_regular :
    IsRegular (zRestrictedMap diagonalVEquation) := by
  have h : zRestrictedMap diagonalVEquation =
      algebraMap ℂ ActualRestrictedZRing (Complex.I - 1) *
        algebraMap CurveRing ActualRestrictedZRing v := by
    change algebraMap CurveRing ActualRestrictedZRing
      (graphReceiver diagonalVEquation) = _
    rw [graphReceiver_diagonal_v, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply ℂ CurveRing ActualRestrictedZRing]
  rw [h]
  exact zRestrictedI_minus_one_isUnit.isRegular.mul actualRestrictedZ_v_regular

theorem zRestricted_diagonal_image_span :
    Ideal.span {zRestrictedMap diagonalVEquation} =
      Ideal.span {algebraMap CurveRing ActualRestrictedZRing v} := by
  have h : zRestrictedMap diagonalVEquation =
      algebraMap ℂ ActualRestrictedZRing (Complex.I - 1) *
        algebraMap CurveRing ActualRestrictedZRing v := by
    change algebraMap CurveRing ActualRestrictedZRing
      (graphReceiver diagonalVEquation) = _
    rw [graphReceiver_diagonal_v, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply ℂ CurveRing ActualRestrictedZRing]
  rw [h]
  exact Ideal.span_singleton_mul_left_unit zRestrictedI_minus_one_isUnit _


abbrev cmActualYFixedEquationSection :
    Γ(CMProjectiveCubic, cmActualRestrictedYCurveOpen ''ᵁ ⊤) :=
  spectrumImageEquation (.of YRestrictedQAway) cmActualRestrictedYCurveOpen yRestrictedA

abbrev cmActualYImageEquationSection :
    Γ(CMProjectiveCubic, cmActualRestrictedYCurveOpen ''ᵁ ⊤) :=
  spectrumImageEquation (.of YRestrictedQAway) cmActualRestrictedYCurveOpen
    (yRestrictedMap yDiagonalAEquation)

abbrev cmActualZFixedEquationSection :
    Γ(CMProjectiveCubic, cmActualRestrictedZCurveOpen ''ᵁ ⊤) :=
  spectrumImageEquation (.of ActualRestrictedZRing) cmActualRestrictedZCurveOpen
    (algebraMap CurveRing ActualRestrictedZRing v)

abbrev cmActualZImageEquationSection :
    Γ(CMProjectiveCubic, cmActualRestrictedZCurveOpen ''ᵁ ⊤) :=
  spectrumImageEquation (.of ActualRestrictedZRing) cmActualRestrictedZCurveOpen
    (zRestrictedMap diagonalVEquation)

theorem cmActualYFixedEquationSection_regular :
    IsRegular cmActualYFixedEquationSection :=
  spectrumImageEquation_regular (.of YRestrictedQAway) cmActualRestrictedYCurveOpen
    yRestrictedA cmActualFixedYRestricted_regular_equation.2

theorem cmActualZFixedEquationSection_regular :
    IsRegular cmActualZFixedEquationSection :=
  spectrumImageEquation_regular (.of ActualRestrictedZRing) cmActualRestrictedZCurveOpen
    (algebraMap CurveRing ActualRestrictedZRing v)
    cmActualFixedZRestricted_regular_equation.2

theorem cmActualYImageEquationSection_regular :
    IsRegular cmActualYImageEquationSection :=
  spectrumImageEquation_regular (.of YRestrictedQAway)
    cmActualRestrictedYCurveOpen (yRestrictedMap yDiagonalAEquation)
    yRestricted_diagonal_image_regular

theorem cmActualZImageEquationSection_regular :
    IsRegular cmActualZImageEquationSection :=
  spectrumImageEquation_regular (.of ActualRestrictedZRing)
    cmActualRestrictedZCurveOpen (zRestrictedMap diagonalVEquation)
    zRestricted_diagonal_image_regular



abbrev cmActualYFixedEquationGerm : cmActualYOriginLocalRing :=
  (CMProjectiveCubic.presheaf.germ
    (cmActualRestrictedYCurveOpen ''ᵁ ⊤) cmActualYOriginPoint
      (by exact ⟨specResiduePoint (.of YRestrictedQAway)
      yRestrictedOriginLift.toRingHom, trivial, rfl⟩)).hom cmActualYFixedEquationSection

abbrev cmActualYImageEquationGerm : cmActualYOriginLocalRing :=
  (CMProjectiveCubic.presheaf.germ
    (cmActualRestrictedYCurveOpen ''ᵁ ⊤) cmActualYOriginPoint
    (by exact ⟨specResiduePoint (.of YRestrictedQAway)
      yRestrictedOriginLift.toRingHom, trivial, rfl⟩)).hom cmActualYImageEquationSection

abbrev cmActualZFixedEquationGerm : cmActualZOriginLocalRing :=
  (CMProjectiveCubic.presheaf.germ
    (cmActualRestrictedZCurveOpen ''ᵁ ⊤) cmActualZOriginPoint
      (by exact ⟨specResiduePoint (.of ActualRestrictedZRing)
      cmActualZOriginLift.toRingHom, trivial, rfl⟩)).hom cmActualZFixedEquationSection

abbrev cmActualZImageEquationGerm : cmActualZOriginLocalRing :=
  (CMProjectiveCubic.presheaf.germ
    (cmActualRestrictedZCurveOpen ''ᵁ ⊤) cmActualZOriginPoint
    (by exact ⟨specResiduePoint (.of ActualRestrictedZRing)
      cmActualZOriginLift.toRingHom, trivial, rfl⟩)).hom cmActualZImageEquationSection

theorem cmActualYFixedEquationGerm_regular : IsRegular cmActualYFixedEquationGerm := by
  exact affineSection_germ_regular _
    ((isAffineOpen_top _).image_of_isOpenImmersion cmActualRestrictedYCurveOpen)
    cmActualYOriginPoint (by
      exact ⟨specResiduePoint (.of YRestrictedQAway)
        yRestrictedOriginLift.toRingHom, trivial, rfl⟩)
    cmActualYFixedEquationSection cmActualYFixedEquationSection_regular

theorem cmActualZFixedEquationGerm_regular : IsRegular cmActualZFixedEquationGerm := by
  exact affineSection_germ_regular _
    ((isAffineOpen_top _).image_of_isOpenImmersion cmActualRestrictedZCurveOpen)
    cmActualZOriginPoint (by
      exact ⟨specResiduePoint (.of ActualRestrictedZRing)
        cmActualZOriginLift.toRingHom, trivial, rfl⟩)
    cmActualZFixedEquationSection cmActualZFixedEquationSection_regular

theorem cmActualYImageEquationGerm_regular : IsRegular cmActualYImageEquationGerm := by
  exact affineSection_germ_regular _
    ((isAffineOpen_top _).image_of_isOpenImmersion cmActualRestrictedYCurveOpen)
    cmActualYOriginPoint (by
      exact ⟨specResiduePoint (.of YRestrictedQAway)
        yRestrictedOriginLift.toRingHom, trivial, rfl⟩)
    cmActualYImageEquationSection cmActualYImageEquationSection_regular

theorem cmActualZImageEquationGerm_regular : IsRegular cmActualZImageEquationGerm := by
  exact affineSection_germ_regular _
    ((isAffineOpen_top _).image_of_isOpenImmersion cmActualRestrictedZCurveOpen)
    cmActualZOriginPoint (by
      exact ⟨specResiduePoint (.of ActualRestrictedZRing)
        cmActualZOriginLift.toRingHom, trivial, rfl⟩)
    cmActualZImageEquationSection cmActualZImageEquationSection_regular



theorem cmActualYOriginStalkIdeal_span_fixedEquation :
    cmActualYOriginStalkIdeal = Ideal.span {cmActualYFixedEquationGerm} := by
  change spectrumImageStalkIdeal cmFixedInclusion.ker (.of YRestrictedQAway)
    cmActualRestrictedYCurveOpen yRestrictedOriginLift.toRingHom = _
  rw [spectrumImageStalkIdeal, spectrumImageEquation_ideal
    cmFixedInclusion.ker (.of YRestrictedQAway) cmActualRestrictedYCurveOpen
    yRestrictedA cmActualFixedYRestricted_regular_equation.1,
    Ideal.map_span, Set.image_singleton]

theorem cmActualZOriginStalkIdeal_span_fixedEquation :
    cmActualZOriginStalkIdeal = Ideal.span {cmActualZFixedEquationGerm} := by
  change spectrumImageStalkIdeal cmFixedInclusion.ker (.of ActualRestrictedZRing)
    cmActualRestrictedZCurveOpen cmActualZOriginLift.toRingHom = _
  rw [spectrumImageStalkIdeal, spectrumImageEquation_ideal
    cmFixedInclusion.ker (.of ActualRestrictedZRing) cmActualRestrictedZCurveOpen
    (algebraMap CurveRing ActualRestrictedZRing v)
    cmActualFixedZRestricted_regular_equation.1,
    Ideal.map_span, Set.image_singleton]



private theorem spectrumImageEquation_span_eq {X : Scheme} (R : CommRingCat)
    (j : Spec R ⟶ X) [IsOpenImmersion j] (r t : R)
    (h : Ideal.span {r} = Ideal.span {t}) :
    Ideal.span {spectrumImageEquation R j r} =
      Ideal.span {spectrumImageEquation R j t} := by
  have hmap := congrArg (fun I : Ideal R =>
    (I.map (Scheme.ΓSpecIso R).inv.hom).map (j.appIso ⊤).inv.hom) h
  simpa only [Ideal.map_span, Set.image_singleton, spectrumImageEquation] using hmap

theorem cmActualYOriginStalkIdeal_span_imageEquation :
    cmActualYOriginStalkIdeal = Ideal.span {cmActualYImageEquationGerm} := by
  have hsec := spectrumImageEquation_span_eq (.of YRestrictedQAway) cmActualRestrictedYCurveOpen
    (yRestrictedMap yDiagonalAEquation) (yRestrictedA) yRestricted_diagonal_image_span
  have hgerm := congrArg (fun I : Ideal Γ(CMProjectiveCubic,
      cmActualRestrictedYCurveOpen ''ᵁ ⊤) => I.map
    (CMProjectiveCubic.presheaf.germ (cmActualRestrictedYCurveOpen ''ᵁ ⊤)
      cmActualYOriginPoint (by
        exact ⟨specResiduePoint (.of YRestrictedQAway) yRestrictedOriginLift.toRingHom, trivial, rfl⟩)).hom) hsec
  rw [cmActualYOriginStalkIdeal_span_fixedEquation]
  simpa only [Ideal.map_span, Set.image_singleton] using hgerm.symm

theorem cmActualZOriginStalkIdeal_span_imageEquation :
    cmActualZOriginStalkIdeal = Ideal.span {cmActualZImageEquationGerm} := by
  have hsec := spectrumImageEquation_span_eq (.of ActualRestrictedZRing) cmActualRestrictedZCurveOpen
    (zRestrictedMap diagonalVEquation) (algebraMap CurveRing ActualRestrictedZRing v) zRestricted_diagonal_image_span
  have hgerm := congrArg (fun I : Ideal Γ(CMProjectiveCubic,
      cmActualRestrictedZCurveOpen ''ᵁ ⊤) => I.map
    (CMProjectiveCubic.presheaf.germ (cmActualRestrictedZCurveOpen ''ᵁ ⊤)
      cmActualZOriginPoint (by
        exact ⟨specResiduePoint (.of ActualRestrictedZRing) cmActualZOriginLift.toRingHom, trivial, rfl⟩)).hom) hsec
  rw [cmActualZOriginStalkIdeal_span_fixedEquation]
  simpa only [Ideal.map_span, Set.image_singleton] using hgerm.symm

#print axioms yAmbientQ_actual_graph_square
#print axioms zAmbientFactor_actual_graph_square
#print axioms yAmbientQOriginPoint_actual_image
#print axioms zAmbientFactorOriginPoint_actual_image
#print axioms cmActualYAmbientDiagonalGerm_regular
#print axioms cmActualZAmbientDiagonalGerm_regular
#print axioms cmActualYAmbientDiagonalGerm_principal
#print axioms cmActualZAmbientDiagonalGerm_principal
#print axioms cmActualYImageEquationGerm_regular
#print axioms cmActualZImageEquationGerm_regular
#print axioms cmActualYOriginStalkIdeal_span_imageEquation
#print axioms cmActualZOriginStalkIdeal_span_imageEquation
end Holonics.Hodge.CMGraphSource
