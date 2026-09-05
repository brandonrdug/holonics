import ElementaryHolonics.Millennium.NavierStokesHorizontalMean
import ElementaryHolonics.Millennium.NavierStokesAnisotropicFrame

/-!
# Framed horizontal mean

The horizontal average is transported over the actual moving affine cell induced by a
nonzero horizontal frame factor.  The definition retains the endpoint orientation, so the
same change-of-variables proof works for either sign of the factor.
-/

noncomputable section

open ContDiff Function Set MeasureTheory
open scoped Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesFramedHorizontalMean

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesHorizontalMean
open Soma.Holonics.Millennium.NavierStokesAnisotropicFrame

def framedHorizontalMean (r : ℝ) (centre : Space) (F : Space → ℝ) (ζ : ℝ) : ℝ :=
  r ^ 2 * ∫ x in (-centre 0 / r)..((1 - centre 0) / r),
    ∫ y in (-centre 1 / r)..((1 - centre 1) / r), F (assemble x y ζ)

theorem framedHorizontalMean_affine_transport
    (r zScale a : ℝ) (hr : r ≠ 0) (centre : Space) (f : Space → ℝ) (ζ : ℝ) :
    framedHorizontalMean r centre
        (fun p ↦ a * f (centre + diagonalFrame r zScale p)) ζ =
      a * horizontalMean f (centre 2 + zScale * ζ) := by
  have hpoint (x y : ℝ) :
      a * f (centre + diagonalFrame r zScale (assemble x y ζ)) =
        a * f (assemble (centre 0 + r * x) (centre 1 + r * y)
          (centre 2 + zScale * ζ)) := by
    congr 2
    rw [diagonalFrame_apply]
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [assemble]
  unfold framedHorizontalMean
  simp_rw [hpoint]
  simp_rw [intervalIntegral.integral_const_mul]
  have hy (x : ℝ) :
      (∫ y in (-centre 1 / r)..((1 - centre 1) / r),
          f (assemble (centre 0 + r * x) (centre 1 + r * y)
            (centre 2 + zScale * ζ))) =
        r⁻¹ * ∫ v in (0 : ℝ)..1,
          f (assemble (centre 0 + r * x) v (centre 2 + zScale * ζ)) := by
    have h := intervalIntegral.integral_comp_add_mul
      (a := -centre 1 / r) (b := (1 - centre 1) / r) (c := r)
      (fun v : ℝ ↦ f (assemble (centre 0 + r * x) v (centre 2 + zScale * ζ)))
      hr (centre 1)
    have hstart : centre 1 + r * (-centre 1 / r) = 0 := by
      field_simp [hr]
      ring
    have hend : centre 1 + r * ((1 - centre 1) / r) = 1 := by
      field_simp [hr]
      ring
    rw [hstart, hend] at h
    simpa [smul_eq_mul] using h
  simp_rw [hy]
  rw [intervalIntegral.integral_const_mul]
  have hx :
      (∫ x in (-centre 0 / r)..((1 - centre 0) / r),
          ∫ v in (0 : ℝ)..1,
            f (assemble (centre 0 + r * x) v (centre 2 + zScale * ζ))) =
        r⁻¹ * ∫ u in (0 : ℝ)..1,
          ∫ v in (0 : ℝ)..1,
            f (assemble u v (centre 2 + zScale * ζ)) := by
    have h := intervalIntegral.integral_comp_add_mul
      (a := -centre 0 / r) (b := (1 - centre 0) / r) (c := r)
      (fun u : ℝ ↦ ∫ v in (0 : ℝ)..1,
        f (assemble u v (centre 2 + zScale * ζ))) hr (centre 0)
    have hstart : centre 0 + r * (-centre 0 / r) = 0 := by
      field_simp [hr]
      ring
    have hend : centre 0 + r * ((1 - centre 0) / r) = 1 := by
      field_simp [hr]
      ring
    rw [hstart, hend] at h
    simpa [smul_eq_mul] using h
  rw [hx]
  unfold horizontalMean
  field_simp [hr]

theorem framedHorizontalMean_affine_transport_hasDerivAt
    (r zScale a : ℝ) (hr : r ≠ 0) (centre : Space) (f : Space → ℝ)
    (hf : ContDiff ℝ 2 f) (ζ : ℝ) :
    HasDerivAt
      (framedHorizontalMean r centre (fun y ↦ a * f (centre + diagonalFrame r zScale y)))
      (a * zScale * horizontalMean (fun p ↦ fderiv ℝ f p
        (EuclideanSpace.single (2 : Fin 3) 1)) (centre 2 + zScale * ζ)) ζ := by
  have harg : HasDerivAt (fun η : ℝ ↦ centre 2 + zScale * η) zScale ζ := by
    convert (hasDerivAt_const ζ (centre 2)).add ((hasDerivAt_id ζ).const_mul zScale)
      using 1 <;> first | rfl | simp
  have h := ((horizontalMean_hasDerivAt f hf (centre 2 + zScale * ζ)).comp ζ harg).const_mul a
  convert h using 1 <;> try rfl
  · funext η
    exact framedHorizontalMean_affine_transport r zScale a hr centre f η
  · ring

#print axioms framedHorizontalMean_affine_transport
#print axioms framedHorizontalMean_affine_transport_hasDerivAt

end Soma.Holonics.Millennium.NavierStokesFramedHorizontalMean
