import Holonics.Geometry.FrameTransport

open scoped Matrix

noncomputable section

namespace Holonics.Geometry.FrameTransport

/-! [proved-derived; source-only] Proposed insertion immediately after
`cross_second_third` in Geometry/FrameTransport. The columns are the actual
u/v derivatives of the polynomial disk section in TUBE_GEOMETRY_DERIVATION.md.
No positivity is needed for this polynomial identity; invertibility, derivative
identification, 3D continuity and native material/port joins are separate. -/

/-- Oriented section area for q₁=a*u*(1+ε*u), q₂=b*v*(1+ε*u). -/
theorem tube_section_area_vector (f : Frame3) (a b ε u v : ℝ) :
    cross3 ((a * (1 + 2 * ε * u)) • f.basis 1 +
        (b * ε * v) • f.basis 2) ((b * (1 + ε * u)) • f.basis 2) =
      (a * b * (1 + ε * u) * (1 + 2 * ε * u)) • f.basis 0 := by
  have hframe : coords (f.basis 1) ⨯₃ coords (f.basis 2) =
      coords (f.basis 0) := by
    have h := congrArg coords (cross_second_third f)
    simpa only [coords, cross3, ofCoords, WithLp.ofLp_toLp] using h
  have harea :
      ((a * (1 + 2 * ε * u)) • coords (f.basis 1) +
        (b * ε * v) • coords (f.basis 2)) ⨯₃
          ((b * (1 + ε * u)) • coords (f.basis 2)) =
      ((a * (1 + 2 * ε * u)) * (b * (1 + ε * u))) •
        coords (f.basis 0) := by
    rw [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂]
    simp only [map_smul, cross_self, smul_zero, add_zero, smul_smul]
    rw [hframe]
  have hcoef : (a * (1 + 2 * ε * u)) * (b * (1 + ε * u)) =
      a * b * (1 + ε * u) * (1 + 2 * ε * u) := by ring
  ext i
  change (((a * (1 + 2 * ε * u)) • coords (f.basis 1) +
      (b * ε * v) • coords (f.basis 2)) ⨯₃
        ((b * (1 + ε * u)) • coords (f.basis 2))) i =
    ((a * b * (1 + ε * u) * (1 + 2 * ε * u)) • coords (f.basis 0)) i
  rw [harea, hcoef]

/-- The section reading of an actual relative current; its continuity law is owed. -/
theorem tube_section_flux (f : Frame3) (a b ε u v : ℝ) (j : Vec3) :
    dot3 j (cross3 ((a * (1 + 2 * ε * u)) • f.basis 1 +
        (b * ε * v) • f.basis 2) ((b * (1 + ε * u)) • f.basis 2)) =
      (a * b * (1 + ε * u) * (1 + 2 * ε * u)) * dot3 j (f.basis 0) := by
  rw [tube_section_area_vector]
  simp only [dot3, real_inner_smul_right]

end Holonics.Geometry.FrameTransport

#print axioms Holonics.Geometry.FrameTransport.tube_section_area_vector
#print axioms Holonics.Geometry.FrameTransport.tube_section_flux
