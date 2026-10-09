import CMYAmbientEquations

/-! Both denominator faces cover the genuine affine graph and diagonal.
The source receivers and partial-derivative identities are constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Holonics.Hodge.CMGraphSource

theorem yScalarPhase_sq : (algebraMap ℂ YChartCubicRing Complex.I) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]

@[simp] theorem yGraphReceiver_P : yGraphReceiver yGraphP = -yPartialA := by
  simp only [yGraphP, map_sub, map_add, map_mul, map_pow, yGraphReceiver_right,
    yGraphReceiver_left, yIotaAlgebraMap_a, yIotaAlgebraMap_b, Algebra.smul_def,
    show yGraphReceiver yAmbientPhase = algebraMap ℂ YChartCubicRing Complex.I from
      yGraphReceiver.commutes Complex.I, map_neg, neg_mul]
  unfold yPartialA
  ring_nf
  rw [yScalarPhase_sq]
  ring
@[simp] theorem yGraphReceiver_Q : yGraphReceiver yGraphQ = -yPartialB := by
  simp only [yGraphQ, map_sub, map_add, map_mul, map_one, yGraphReceiver_right,
    yGraphReceiver_left, yIotaAlgebraMap_b, Algebra.smul_def,
    show yGraphReceiver yAmbientPhase = algebraMap ℂ YChartCubicRing Complex.I from
      yGraphReceiver.commutes Complex.I, map_neg, neg_mul]
  unfold yPartialB
  ring_nf
  rw [yScalarPhase_sq]
  ring
@[simp] theorem yDiagonalReceiver_P : yDiagonalReceiver yDiagonalP = yPartialA := by
  simp only [yDiagonalP, map_sub, map_add, map_mul, map_pow,
    yDiagonalReceiver_right, yDiagonalReceiver_left]
  unfold yPartialA
  ring
@[simp] theorem yDiagonalReceiver_Q : yDiagonalReceiver yDiagonalQ = -yPartialB := by
  simp only [yDiagonalQ, map_add, map_mul, map_one,
    yDiagonalReceiver_right, yDiagonalReceiver_left]
  unfold yPartialB
  ring

theorem yGraph_faces_cover :
    Ideal.span ({yGraphReceiver yGraphP, yGraphReceiver yGraphQ} : Set YChartCubicRing) = ⊤ := by
  rw [yGraphReceiver_P, yGraphReceiver_Q]
  apply top_unique
  rw [← yDerivative_ideal_top]
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · simpa only [neg_neg, SetLike.mem_coe] using (Ideal.span ({-yPartialA,-yPartialB} : Set YChartCubicRing)).neg_mem
      (Ideal.subset_span (Set.mem_insert _ _))
  · rcases Set.mem_singleton_iff.mp hp with rfl
    simpa only [neg_neg, SetLike.mem_coe] using (Ideal.span ({-yPartialA,-yPartialB} : Set YChartCubicRing)).neg_mem
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem yDiagonal_faces_cover :
    Ideal.span ({yDiagonalReceiver yDiagonalP, yDiagonalReceiver yDiagonalQ} : Set YChartCubicRing) = ⊤ := by
  rw [yDiagonalReceiver_P, yDiagonalReceiver_Q]
  apply top_unique
  rw [← yDerivative_ideal_top]
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · rcases Set.mem_singleton_iff.mp hp with rfl
    simpa only [neg_neg, SetLike.mem_coe] using (Ideal.span ({yPartialA,-yPartialB} : Set YChartCubicRing)).neg_mem
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

#print axioms yGraphReceiver_P
#print axioms yGraphReceiver_Q
#print axioms yDiagonalReceiver_P
#print axioms yDiagonalReceiver_Q
#print axioms yGraph_faces_cover
#print axioms yDiagonal_faces_cover
end Holonics.Hodge.CMGraphSource
