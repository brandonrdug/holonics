import CMYScalarMap
import CMAffineEqualizer

/-!
The ideal of differences of the actual transported Y coordinate map is
exactly the origin ideal. Its quotient is the coefficient field, with both
inverse maps constructed. This consumes the actual chart map rather than
identifying an independently defined iota without proof.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace Holonics.Hodge.CMGraphSource

abbrev yB : YChartCubicRing := AdjoinRoot.of yMonicCubic X
abbrev yA : YChartCubicRing := AdjoinRoot.root yMonicCubic
def yZeroPointIdeal : Ideal YChartCubicRing := Ideal.span ({yB, yA} : Set _)
abbrev yFixedDifferenceIdeal : Ideal YChartCubicRing :=
  affineDifferenceIdeal yIotaCoordinateRing (RingHom.id YChartCubicRing)

theorem yB_mem_fixedDifferenceIdeal : yB ∈ yFixedDifferenceIdeal := by
  have hd : yIotaCoordinateRing yB - yB ∈ yFixedDifferenceIdeal :=
    Ideal.subset_span ⟨yB, rfl⟩
  have hi : -Complex.I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hm := yFixedDifferenceIdeal.mul_mem_left
    (algebraMap ℂ YChartCubicRing ((-Complex.I - 1)⁻¹)) hd
  have he : algebraMap ℂ YChartCubicRing ((-Complex.I - 1)⁻¹) *
      (yIotaCoordinateRing yB - yB) = yB := by
    rw [yIotaCoordinateRing_b]
    calc
      _ = algebraMap ℂ YChartCubicRing ((-Complex.I - 1)⁻¹) *
          (algebraMap ℂ YChartCubicRing (-Complex.I - 1) * yB) := by
        rw [map_sub, map_one]
        ring
      _ = yB := by rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, one_mul]
  rwa [he] at hm


theorem yA_mem_fixedDifferenceIdeal : yA ∈ yFixedDifferenceIdeal := by
  have hd : yIotaCoordinateRing yA - yA ∈ yFixedDifferenceIdeal :=
    Ideal.subset_span ⟨yA, rfl⟩
  have hi : Complex.I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hm := yFixedDifferenceIdeal.mul_mem_left
    (algebraMap ℂ YChartCubicRing ((Complex.I - 1)⁻¹)) hd
  have he : algebraMap ℂ YChartCubicRing ((Complex.I - 1)⁻¹) *
      (yIotaCoordinateRing yA - yA) = yA := by
    rw [yIotaCoordinateRing_a]
    calc
      _ = algebraMap ℂ YChartCubicRing ((Complex.I - 1)⁻¹) *
          (algebraMap ℂ YChartCubicRing (Complex.I - 1) * yA) := by
        rw [map_sub, map_one]
        ring
      _ = yA := by rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, one_mul]
  rwa [he] at hm

theorem yFixedDifferenceIdeal_eq_origin : yFixedDifferenceIdeal = yZeroPointIdeal := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    let π : YChartCubicRing →ₐ[ℂ] YChartCubicRing ⧸ yZeroPointIdeal :=
      Ideal.Quotient.mkₐ ℂ yZeroPointIdeal
    have hu : π yB = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hv : π yA = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hc : π.comp yIotaAlgebraMap = π := by
      apply yCoordinateAlgebraMap_ext
      · change π (yIotaCoordinateRing yB) = π yB
        rw [yIotaCoordinateRing_b, map_mul, hu, mul_zero]
      · change π (yIotaCoordinateRing yA) = π yA
        rw [yIotaCoordinateRing_a, map_mul, hv, mul_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π (yIotaCoordinateRing a - a) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (AlgHom.congr_fun hc a)
  · apply Ideal.span_le.mpr
    rintro a (ha | ha)
    · exact ha ▸ yB_mem_fixedDifferenceIdeal
    · exact (Set.mem_singleton_iff.mp ha) ▸ yA_mem_fixedDifferenceIdeal

def yOriginCoefficient : ℂ[X] →ₐ[ℂ] ℂ := aeval (0 : ℂ)
theorem yOrigin_relation : yMonicCubic.eval₂ yOriginCoefficient (0 : ℂ) = 0 := by
  simp [yMonicCubic, yOriginCoefficient]

def yOriginReceiver : YChartCubicRing →ₐ[ℂ] ℂ :=
  AdjoinRoot.liftAlgHom yMonicCubic yOriginCoefficient 0 yOrigin_relation
@[simp] theorem yOriginReceiver_u : yOriginReceiver yB = 0 := by
  rw [yOriginReceiver, AdjoinRoot.liftAlgHom_of]
  exact aeval_X (0 : ℂ)
@[simp] theorem yOriginReceiver_v : yOriginReceiver yA = 0 := by
  rw [yOriginReceiver, AdjoinRoot.liftAlgHom_root]

theorem yZeroPointIdeal_le_originKernel : yZeroPointIdeal ≤ RingHom.ker yOriginReceiver := by
  apply Ideal.span_le.mpr
  rintro a (ha | ha)
  · change yOriginReceiver a = 0
    rw [ha, yOriginReceiver_u]
  · change yOriginReceiver a = 0
    rw [Set.mem_singleton_iff.mp ha, yOriginReceiver_v]

def yOriginQuotientReceiver : (YChartCubicRing ⧸ yZeroPointIdeal) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ yZeroPointIdeal yOriginReceiver (fun _ h => yZeroPointIdeal_le_originKernel h)
theorem yOriginQuotient_comp_scalars :
    yOriginQuotientReceiver.comp (Algebra.ofId ℂ (YChartCubicRing ⧸ yZeroPointIdeal)) =
      AlgHom.id ℂ ℂ := by ext
theorem yScalars_comp_originQuotient :
    (Algebra.ofId ℂ (YChartCubicRing ⧸ yZeroPointIdeal)).comp yOriginQuotientReceiver =
      AlgHom.id ℂ (YChartCubicRing ⧸ yZeroPointIdeal) := by
  apply Ideal.Quotient.algHom_ext
  apply yCoordinateAlgebraMap_ext
  · change algebraMap ℂ (YChartCubicRing ⧸ yZeroPointIdeal) (yOriginReceiver yB) =
      Ideal.Quotient.mk yZeroPointIdeal yB
    rw [yOriginReceiver_u, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm
  · change algebraMap ℂ (YChartCubicRing ⧸ yZeroPointIdeal) (yOriginReceiver yA) =
      Ideal.Quotient.mk yZeroPointIdeal yA
    rw [yOriginReceiver_v, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm

def yZeroPointCoordinateEquiv : (YChartCubicRing ⧸ yZeroPointIdeal) ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofAlgHom yOriginQuotientReceiver (Algebra.ofId ℂ _)
    yOriginQuotient_comp_scalars yScalars_comp_originQuotient
def yFixedCoordinatePointEquiv : (YChartCubicRing ⧸ yFixedDifferenceIdeal) ≃+* ℂ :=
  (Ideal.quotEquivOfEq yFixedDifferenceIdeal_eq_origin).trans yZeroPointCoordinateEquiv.toRingEquiv

#print axioms yFixedDifferenceIdeal_eq_origin
#print axioms yZeroPointCoordinateEquiv
#print axioms yFixedCoordinatePointEquiv
end Holonics.Hodge.CMGraphSource
