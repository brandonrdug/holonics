import CMZScalarMap
import CMAffineEqualizer

/-!
The ideal of differences of the actual transported Z coordinate map is
exactly the origin ideal. Its quotient is the coefficient field, with both
inverse maps constructed. This consumes the actual chart map rather than
identifying an independently defined iota without proof.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace Holonics.Hodge.CMGraphSource

abbrev zU : ZChartSquareRing := AdjoinRoot.of squareCurve.toAffine.polynomial X
abbrev zV : ZChartSquareRing := AdjoinRoot.root squareCurve.toAffine.polynomial
def zZeroPointIdeal : Ideal ZChartSquareRing := Ideal.span ({zU, zV} : Set _)
abbrev zFixedDifferenceIdeal : Ideal ZChartSquareRing :=
  affineDifferenceIdeal zIotaCoordinateRing (RingHom.id ZChartSquareRing)

theorem zU_mem_fixedDifferenceIdeal : zU ∈ zFixedDifferenceIdeal := by
  have hd : zIotaCoordinateRing zU - zU ∈ zFixedDifferenceIdeal :=
    Ideal.subset_span ⟨zU, rfl⟩
  have hm := zFixedDifferenceIdeal.mul_mem_left (algebraMap ℂ ZChartSquareRing (-(1 / 2 : ℂ))) hd
  have he : algebraMap ℂ ZChartSquareRing (-(1 / 2 : ℂ)) *
      (zIotaCoordinateRing zU - zU) = zU := by
    rw [zIotaCoordinateRing_u]
    calc
      _ = algebraMap ℂ ZChartSquareRing (-(1 / 2 : ℂ)) *
          (algebraMap ℂ ZChartSquareRing (-2 : ℂ) * zU) := by
        norm_num only [map_neg, map_ofNat]
        dsimp only [zU]
        ring
      _ = zU := by rw [← mul_assoc, ← map_mul]; norm_num
  rwa [he] at hm

theorem zV_mem_fixedDifferenceIdeal : zV ∈ zFixedDifferenceIdeal := by
  have hd : zIotaCoordinateRing zV - zV ∈ zFixedDifferenceIdeal :=
    Ideal.subset_span ⟨zV, rfl⟩
  have hi : Complex.I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hm := zFixedDifferenceIdeal.mul_mem_left
    (algebraMap ℂ ZChartSquareRing ((Complex.I - 1)⁻¹)) hd
  have he : algebraMap ℂ ZChartSquareRing ((Complex.I - 1)⁻¹) *
      (zIotaCoordinateRing zV - zV) = zV := by
    rw [zIotaCoordinateRing_v]
    calc
      _ = algebraMap ℂ ZChartSquareRing ((Complex.I - 1)⁻¹) *
          (algebraMap ℂ ZChartSquareRing (Complex.I - 1) * zV) := by
        rw [map_sub, map_one]
        ring
      _ = zV := by rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, one_mul]
  rwa [he] at hm

theorem zFixedDifferenceIdeal_eq_origin : zFixedDifferenceIdeal = zZeroPointIdeal := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    let π : ZChartSquareRing →ₐ[ℂ] ZChartSquareRing ⧸ zZeroPointIdeal :=
      Ideal.Quotient.mkₐ ℂ zZeroPointIdeal
    have hu : π zU = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hv : π zV = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hc : π.comp zIotaAlgebraMap = π := by
      apply zCoordinateAlgebraMap_ext
      · change π (zIotaCoordinateRing zU) = π zU
        rw [zIotaCoordinateRing_u, map_neg, hu, neg_zero]
      · change π (zIotaCoordinateRing zV) = π zV
        rw [zIotaCoordinateRing_v, map_mul, hv, mul_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π (zIotaCoordinateRing a - a) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (AlgHom.congr_fun hc a)
  · apply Ideal.span_le.mpr
    rintro a (ha | ha)
    · exact ha ▸ zU_mem_fixedDifferenceIdeal
    · exact (Set.mem_singleton_iff.mp ha) ▸ zV_mem_fixedDifferenceIdeal

def zOriginCoefficient : ℂ[X] →ₐ[ℂ] ℂ := aeval (0 : ℂ)
theorem zOrigin_relation : squareCurve.toAffine.polynomial.eval₂ zOriginCoefficient (0 : ℂ) = 0 := by
  have hp : squareCurve.toAffine.polynomial = X ^ 2 - C (X ^ 3 - X) := by
    simp [WeierstrassCurve.Affine.polynomial, squareCurve, sub_eq_add_neg]
  rw [hp]
  simp only [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, map_sub, map_pow,
    zOriginCoefficient, AlgHom.coe_toRingHom, aeval_X]
  norm_num
def zOriginReceiver : ZChartSquareRing →ₐ[ℂ] ℂ :=
  AdjoinRoot.liftAlgHom squareCurve.toAffine.polynomial zOriginCoefficient 0 zOrigin_relation
@[simp] theorem zOriginReceiver_u : zOriginReceiver zU = 0 := by
  rw [zOriginReceiver, AdjoinRoot.liftAlgHom_of]
  exact aeval_X (0 : ℂ)
@[simp] theorem zOriginReceiver_v : zOriginReceiver zV = 0 := by
  rw [zOriginReceiver, AdjoinRoot.liftAlgHom_root]

theorem zZeroPointIdeal_le_originKernel : zZeroPointIdeal ≤ RingHom.ker zOriginReceiver := by
  apply Ideal.span_le.mpr
  rintro a (ha | ha)
  · change zOriginReceiver a = 0
    rw [ha, zOriginReceiver_u]
  · change zOriginReceiver a = 0
    rw [Set.mem_singleton_iff.mp ha, zOriginReceiver_v]

def zOriginQuotientReceiver : (ZChartSquareRing ⧸ zZeroPointIdeal) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ zZeroPointIdeal zOriginReceiver (fun _ h => zZeroPointIdeal_le_originKernel h)
theorem zOriginQuotient_comp_scalars :
    zOriginQuotientReceiver.comp (Algebra.ofId ℂ (ZChartSquareRing ⧸ zZeroPointIdeal)) =
      AlgHom.id ℂ ℂ := by ext
theorem zScalars_comp_originQuotient :
    (Algebra.ofId ℂ (ZChartSquareRing ⧸ zZeroPointIdeal)).comp zOriginQuotientReceiver =
      AlgHom.id ℂ (ZChartSquareRing ⧸ zZeroPointIdeal) := by
  apply Ideal.Quotient.algHom_ext
  apply zCoordinateAlgebraMap_ext
  · change algebraMap ℂ (ZChartSquareRing ⧸ zZeroPointIdeal) (zOriginReceiver zU) =
      Ideal.Quotient.mk zZeroPointIdeal zU
    rw [zOriginReceiver_u, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm
  · change algebraMap ℂ (ZChartSquareRing ⧸ zZeroPointIdeal) (zOriginReceiver zV) =
      Ideal.Quotient.mk zZeroPointIdeal zV
    rw [zOriginReceiver_v, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm

def zZeroPointCoordinateEquiv : (ZChartSquareRing ⧸ zZeroPointIdeal) ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofAlgHom zOriginQuotientReceiver (Algebra.ofId ℂ _)
    zOriginQuotient_comp_scalars zScalars_comp_originQuotient
def zFixedCoordinatePointEquiv : (ZChartSquareRing ⧸ zFixedDifferenceIdeal) ≃+* ℂ :=
  (Ideal.quotEquivOfEq zFixedDifferenceIdeal_eq_origin).trans zZeroPointCoordinateEquiv.toRingEquiv

#print axioms zFixedDifferenceIdeal_eq_origin
#print axioms zZeroPointCoordinateEquiv
#print axioms zFixedCoordinatePointEquiv
end Holonics.Hodge.CMGraphSource
