import CMZChartEquation

/-!
The actual degree-zero Y localization is identified with C[a,b] by an
explicit homogeneous swap of Y and Z. The normalized cubic is computed
in this localization. Its reduced ideal-sheaf comparison remains separate.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open HomogeneousLocalization
open scoped Graded
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev yCoordinate : HomogeneousRing := MvPolynomial.X 1
abbrev YChartAway := Away CMGrading yCoordinate
def swapYZ : HomogeneousRing ≃ₐ[ℂ] HomogeneousRing :=
  MvPolynomial.renameEquiv ℂ (Equiv.swap (1 : Fin 3) 2)
def gradedSwapYZ : CMGrading →+*ᵍ CMGrading where
  __ := swapYZ.toRingEquiv.toRingHom
  map_mem hp := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    exact hp.rename_isHomogeneous

@[simp] theorem swapYZ_y : gradedSwapYZ yCoordinate = zCoordinate := by
  simp [gradedSwapYZ, swapYZ, yCoordinate, zCoordinate]
@[simp] theorem swapYZ_z : gradedSwapYZ zCoordinate = yCoordinate := by
  simp [gradedSwapYZ, swapYZ, yCoordinate, zCoordinate]
@[simp] theorem swapYZ_x : gradedSwapYZ (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [gradedSwapYZ, swapYZ, Equiv.swap_apply_def]
theorem swapYZ_comp : gradedSwapYZ.comp gradedSwapYZ = GradedRingHom.id CMGrading := by
  apply GradedRingHom.ext
  intro p
  change swapYZ (swapYZ p) = p
  simp only [swapYZ, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
  have he : ((Equiv.swap (1 : Fin 3) 2) : Fin 3 → Fin 3) ∘
      (Equiv.swap (1 : Fin 3) 2) = id := by
    funext j
    simp
  rw [he, MvPolynomial.rename_id]
  rfl

def yAwayToZ : YChartAway →+* ZChartAway :=
  HomogeneousLocalization.map gradedSwapYZ (by
    rintro p ⟨n, rfl⟩
    exact ⟨n, by simp⟩)
def zAwayToY : ZChartAway →+* YChartAway :=
  HomogeneousLocalization.map gradedSwapYZ (by
    rintro p ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

theorem y_z_inverse : zAwayToY.comp yAwayToZ = RingHom.id YChartAway := by
  rw [yAwayToZ, zAwayToY, ← HomogeneousLocalization.map_comp]
  simpa only [swapYZ_comp] using HomogeneousLocalization.map_id CMGrading (.powers yCoordinate)
theorem z_y_inverse : yAwayToZ.comp zAwayToY = RingHom.id ZChartAway := by
  rw [yAwayToZ, zAwayToY, ← HomogeneousLocalization.map_comp]
  simpa only [swapYZ_comp] using HomogeneousLocalization.map_id CMGrading (.powers zCoordinate)

def yAwayEquivZ : YChartAway ≃+* ZChartAway :=
  RingEquiv.ofRingHom yAwayToZ zAwayToY
    z_y_inverse y_z_inverse
def yAwayEquivPlane : YChartAway ≃+* ZChartPlane := yAwayEquivZ.trans zAwayEquivPlane

def yNormalizedCubic : YChartAway :=
  Away.mk CMGrading (coordinate_degree_one 1) 3 projectiveCubic
    (by simpa using cubic_degree_three)
def yAffineCubic : ZChartPlane :=
  MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3 +
    MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2

theorem yAwayToZ_mk (n : ℕ) (p : HomogeneousRing) (hp : p ∈ CMGrading n) :
    yAwayToZ (Away.mk CMGrading (coordinate_degree_one 1) n p
      (by simpa using hp)) = Away.mk CMGrading (coordinate_degree_one 2) n
        (gradedSwapYZ p) (by simpa using gradedSwapYZ.map_mem hp) := by
  unfold yAwayToZ Away.mk
  rw [HomogeneousLocalization.map_mk]
  congr 1
  simp [map_pow]

theorem yNormalizedCubic_image : yAwayEquivPlane yNormalizedCubic = yAffineCubic := by
  change zAwayEquivPlane (yAwayToZ yNormalizedCubic) = _
  rw [zAwayEquivPlane_apply, yNormalizedCubic, yAwayToZ_mk 3 _ cubic_degree_three]
  erw [zAwayToPlane_mk 3 _ (gradedSwapYZ.map_mem cubic_degree_three)]
  simp [zDehomogenize, projectiveCubic,
    WeierstrassCurve.Projective.polynomial, squareCurve, yAffineCubic]
  ring

#print axioms yAwayEquivPlane
#print axioms yNormalizedCubic_image
end Holonics.Hodge.CMGraphSource
