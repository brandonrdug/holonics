import TubeSectionAreaVectorFinal
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
The actual asymmetric section chart, with spine position and material frame fixed.
This is a receiver chart of the tube, not a new material law. The existing proper
FrameTransport owner and previously checked area/current lemmas are imported.
The calculus is the product/smul calculus used by Geometry/ConnectionCalculus.
No positivity, invertibility or C2 spine/frame hypothesis is needed for this
globally polynomial section derivative. Such hypotheses belong to the full
three-dimensional chart, embedding and continuity consumers.
Refs #62, #73.
-/

noncomputable section

namespace Holonics.Geometry.FrameTransport

/-- The explicit transverse section of the asymmetric tube at a fixed spine point. -/
def tube_section_chart (f : Frame3) (c : Vec3) (a b ε : ℝ) (z : ℝ × ℝ) : Vec3 :=
  c + (a * z.1 * (1 + ε * z.1)) • f.basis 1 +
    (b * z.2 * (1 + ε * z.1)) • f.basis 2

/-- Its derivative, expressed as a continuous linear map on actual coordinate increments. -/
def tube_section_derivative (f : Frame3) (a b ε : ℝ) (z : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] Vec3 :=
  ((a * (1 + 2 * ε * z.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (f.basis 1) +
    ((b * ε * z.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (b * (1 + ε * z.1)) • ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (f.basis 2)

/-- Identification of the displayed section columns with an actual Fréchet derivative. -/
theorem tube_section_hasFDerivAt (f : Frame3) (c : Vec3) (a b ε : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (tube_section_chart f c a b ε)
      (tube_section_derivative f a b ε z) z := by
  have hu : HasFDerivAt (fun y : ℝ × ℝ => y.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) z := hasFDerivAt_fst
  have hv : HasFDerivAt (fun y : ℝ × ℝ => y.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) z := hasFDerivAt_snd
  have hh := (hasFDerivAt_const (1 : ℝ) z).add (hu.const_smul ε)
  have hq1 := (hu.const_smul a).mul hh
  have hq2 := (hv.const_smul b).mul hh
  have hX := ((hasFDerivAt_const c z).add (hq1.smul_const (f.basis 1))).add
    (hq2.smul_const (f.basis 2))
  convert! hX using 1
  apply ContinuousLinearMap.ext
  intro δ
  ext i
  simp [tube_section_derivative, smul_eq_mul]
  ring

theorem tube_section_fderiv_first (f : Frame3) (c : Vec3) (a b ε u v : ℝ) :
    fderiv ℝ (tube_section_chart f c a b ε) (u, v) (1, 0) =
      (a * (1 + 2 * ε * u)) • f.basis 1 + (b * ε * v) • f.basis 2 := by
  rw [(tube_section_hasFDerivAt f c a b ε (u, v)).fderiv]
  simp [tube_section_derivative]

theorem tube_section_fderiv_second (f : Frame3) (c : Vec3) (a b ε u v : ℝ) :
    fderiv ℝ (tube_section_chart f c a b ε) (u, v) (0, 1) =
      (b * (1 + ε * u)) • f.basis 2 := by
  rw [(tube_section_hasFDerivAt f c a b ε (u, v)).fderiv]
  simp [tube_section_derivative]

/-- The oriented area is now a reading of the constructed chart's derivative. -/
theorem tube_section_actual_area (f : Frame3) (c : Vec3) (a b ε u v : ℝ) :
    cross3 (fderiv ℝ (tube_section_chart f c a b ε) (u, v) (1, 0))
      (fderiv ℝ (tube_section_chart f c a b ε) (u, v) (0, 1)) =
      (a * b * (1 + ε * u) * (1 + 2 * ε * u)) • f.basis 0 := by
  rw [tube_section_fderiv_first, tube_section_fderiv_second]
  exact tube_section_area_vector f a b ε u v

/-- The section pairs an actual current with the constructed chart's oriented area.
Supplying a continuity current, moving-relative current or balance is a separate consumer. -/
theorem tube_section_actual_flux (f : Frame3) (c : Vec3) (a b ε u v : ℝ) (j : Vec3) :
    dot3 j (cross3 (fderiv ℝ (tube_section_chart f c a b ε) (u, v) (1, 0))
      (fderiv ℝ (tube_section_chart f c a b ε) (u, v) (0, 1))) =
      (a * b * (1 + ε * u) * (1 + 2 * ε * u)) * dot3 j (f.basis 0) := by
  rw [tube_section_fderiv_first, tube_section_fderiv_second]
  exact tube_section_flux f a b ε u v j

end Holonics.Geometry.FrameTransport

#print axioms Holonics.Geometry.FrameTransport.tube_section_hasFDerivAt
#print axioms Holonics.Geometry.FrameTransport.tube_section_fderiv_first
#print axioms Holonics.Geometry.FrameTransport.tube_section_fderiv_second
#print axioms Holonics.Geometry.FrameTransport.tube_section_actual_area
#print axioms Holonics.Geometry.FrameTransport.tube_section_actual_flux
