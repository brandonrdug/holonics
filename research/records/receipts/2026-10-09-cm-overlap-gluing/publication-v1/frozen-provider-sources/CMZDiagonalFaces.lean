import CMZDiagonalLocal
import CMChartDerivativeCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Holonics.Hodge.CMGraphSource
abbrev DiagonalVAway := Localization.Away diagonalVSum

theorem diagonalIdeal_on_vsum_face :
    diagonalIdeal.map (algebraMap ProductRing DiagonalVAway) =
      Ideal.span {algebraMap ProductRing DiagonalVAway diagonalUEquation} := by
  rw [diagonalIdeal_eq_two_equations, diagonalTwoEquationIdeal, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  exact two_equations_principal_of_unit _ diagonalUEquation diagonalVEquation
    diagonalCubicFactor diagonalVSum diagonal_difference_relation
    (IsLocalization.Away.algebraMap_isUnit _)

theorem diagonalUEquation_regular_on_vsum_face :
    IsRegular (algebraMap ProductRing DiagonalVAway diagonalUEquation) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers diagonalVSum)
    DiagonalVAway (isRegular_iff_mem_nonZeroDivisors.mp diagonalUEquation_regular)

@[simp] theorem diagonalReceiver_cubic_factor :
    diagonalReceiver diagonalCubicFactor = -zPartialU := by
  simp only [diagonalCubicFactor, map_sub, map_add, map_mul, map_pow, map_one,
    diagonalReceiver_right, diagonalReceiver_left]
  unfold zPartialU
  ring
@[simp] theorem diagonalReceiver_vsum : diagonalReceiver diagonalVSum = zPartialV := by
  simp only [diagonalVSum, map_add, diagonalReceiver_left, diagonalReceiver_right]
  unfold zPartialV
  ring

theorem diagonal_principal_faces_cover :
    Ideal.span ({diagonalReceiver diagonalCubicFactor, diagonalReceiver diagonalVSum} : Set CurveRing) = ⊤ := by
  rw [diagonalReceiver_cubic_factor, diagonalReceiver_vsum]
  apply top_unique
  rw [← zDerivative_ideal_top]
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · simpa only [neg_neg, SetLike.mem_coe] using
      (Ideal.span ({-zPartialU,zPartialV} : Set CurveRing)).neg_mem
        (Ideal.subset_span (Set.mem_insert _ _))
  · rcases Set.mem_singleton_iff.mp hp with rfl
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

#print axioms diagonalIdeal_on_vsum_face
#print axioms diagonalUEquation_regular_on_vsum_face
#print axioms diagonal_principal_faces_cover
end Holonics.Hodge.CMGraphSource
