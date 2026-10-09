import CMGraphLocalEquations

/-!
Actual localized graph ideals, not assigned divisor classes. On the two
principal faces established to cover the affine graph, its ideal has one
of the displayed generators. A Cartier-divisor theorem additionally needs
these generators to be non-zero-divisors in the relevant surface rings.
-/
noncomputable section
namespace Holonics.Hodge.CMGraphSource

theorem two_equations_principal_of_unit {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g h c w : R) (he : g * c = h * w) (hw : IsUnit (f w)) :
    (Ideal.span {f g, f h} : Ideal S) = Ideal.span {f g} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact Ideal.subset_span (Set.mem_singleton _)
    · rcases Set.mem_singleton_iff.mp hp with rfl
      apply (Ideal.mul_unit_mem_iff_mem (Ideal.span {f g}) hw).mp
      have hm : f g * f c ∈ (Ideal.span {f g} : Ideal S) :=
        Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
      simpa only [← map_mul, he] using hm
  · apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact Ideal.subset_span (Set.mem_insert _ _)

abbrev GraphVAway := Localization.Away graphVSum
abbrev GraphFactorAway := Localization.Away graphCubicFactor

theorem graphIdeal_on_vsum_face :
    graphIdeal.map (algebraMap ProductRing GraphVAway) =
      Ideal.span {algebraMap ProductRing GraphVAway graphXEquation} := by
  rw [graphIdeal_eq_two_equations, graphTwoEquationIdeal, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  exact two_equations_principal_of_unit (algebraMap ProductRing GraphVAway)
    graphXEquation graphVEquation graphCubicFactor graphVSum graph_difference_relation
    (IsLocalization.Away.algebraMap_isUnit graphVSum)

theorem graphIdeal_on_cubic_factor_face :
    graphIdeal.map (algebraMap ProductRing GraphFactorAway) =
      Ideal.span {algebraMap ProductRing GraphFactorAway graphVEquation} := by
  rw [graphIdeal_eq_two_equations, graphTwoEquationIdeal, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rw [Ideal.span_pair_comm]
  exact two_equations_principal_of_unit (algebraMap ProductRing GraphFactorAway)
    graphVEquation graphXEquation graphVSum graphCubicFactor graph_difference_relation.symm
    (IsLocalization.Away.algebraMap_isUnit graphCubicFactor)

#print axioms graphIdeal_on_vsum_face
#print axioms graphIdeal_on_cubic_factor_face
end Holonics.Hodge.CMGraphSource
