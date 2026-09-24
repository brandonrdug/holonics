import Mathlib

/-!
# Analytic navigation by a retained residual

This owner records local holomorphic Newton and residual-release identities.  The hypotheses are
local jet and nonzero-derivative conditions; no convergence, basin, or global zero-selection claim
is made.  Affine covariance transports the source and both jets together.
-/

noncomputable section

namespace Holonics.Mathematics.AnalyticNavigation

open Complex

/-! ## Newton's local map -/

/-- One Newton step with a real or complex step parameter. -/
def newtonMap (lambda : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z - lambda * f z / deriv f z

/-- The local Newton map derivative, with both source jets retained. -/
theorem hasDerivAt_newtonMap {lambda first second z : ℂ}
    (f : ℂ → ℂ)
    (hf : HasDerivAt f first z)
    (hfirst : HasDerivAt (deriv f) second z)
    (hfirst_ne : first ≠ 0) :
    HasDerivAt (newtonMap lambda f)
      (1 - lambda + lambda * f z * second / first ^ 2) z := by
  have hderiv : deriv f z = first := hf.deriv
  have hden : deriv f z ≠ 0 := by rw [hderiv]; exact hfirst_ne
  have hquot : HasDerivAt (fun w : ℂ => f w / deriv f w)
      ((first * first - f z * second) / first ^ 2) z := by
    have h := hf.div hfirst hden
    rw [hderiv] at h
    exact h
  have hmap := (hasDerivAt_id z).sub ((hquot.const_mul lambda))
  have hsq : first ^ 2 ≠ 0 := pow_ne_zero 2 hfirst_ne
  have hraw : HasDerivAt (newtonMap lambda f)
      (1 - lambda * ((first * first - f z * second) / first ^ 2)) z := by
    have hfun : newtonMap lambda f =
        id - fun w : ℂ => lambda * (f w / deriv f w) := by
      funext w
      simp only [newtonMap, Pi.sub_apply, id_eq]
      ring
    exact hmap.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => by
      rw [hfun]))
  convert hraw using 1
  field_simp [hsq]
  ring

/-! ## Residual release -/

/-- A curve following the negative Newton residual has the local residual-release derivative.
The exponential consequence requires an additional initial-value/ODE argument and is not claimed
by this local theorem. -/
theorem hasDerivAt_residual_release {f : ℂ → ℂ} {z z' : ℝ → ℂ} {t : ℝ}
    (hf : HasDerivAt f (deriv f (z t)) (z t))
    (hz : HasDerivAt z (z' t) t)
    (hderiv_ne : deriv f (z t) ≠ 0)
    (hdirection : z' t = -f (z t) / deriv f (z t)) :
    HasDerivAt (fun s => f (z s)) (-f (z t)) t := by
  have hcomp := hf.comp t hz
  rw [hdirection] at hcomp
  rw [show (fun s => f (z s)) = f ∘ z by rfl]
  convert hcomp using 1
  · rfl
  field_simp [hderiv_ne]

/-! ## Affine source and coordinate covariance -/

/-- The affine coordinate change used by the covariance statements. -/
def affineCoordinate (a b z : ℂ) : ℂ := a * z + b

/-- Pull a holomorphic source through the inverse affine coordinate and scale its value. -/
def affinePullback (a b c : ℂ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  c * f ((w - b) / a)

theorem affinePullback_value {a b c z : ℂ} (ha : a ≠ 0) (f : ℂ → ℂ) :
    affinePullback a b c f (affineCoordinate a b z) = c * f z := by
  unfold affinePullback affineCoordinate
  have hz : (a * z + b - b) / a = z := by
    calc
      (a * z + b - b) / a = (a * z) / a := by congr 1 <;> ring
      _ = z * (a * a⁻¹) := by rw [div_eq_mul_inv]; ring
      _ = z := by rw [mul_inv_cancel₀ ha, mul_one]
  rw [hz]

/-- The source derivative transforms by the inverse affine scale. -/
theorem hasDerivAt_affinePullback {a b c first z : ℂ} (ha : a ≠ 0)
    (f : ℂ → ℂ) (hf : HasDerivAt f first z) :
    HasDerivAt (affinePullback a b c f)
      (c * first / a) (affineCoordinate a b z) := by
  let x : ℂ := affineCoordinate a b z
  let inner : ℂ → ℂ := (fun _ => z) + fun w => (id w - x) / a
  have hinner : HasDerivAt inner (1 / a) x := by
    simpa [inner] using
      ((hasDerivAt_const x z).add
        ((hasDerivAt_id x).sub_const x |>.div_const a))
  have hpoint : inner x = z := by simp [inner]
  have hf' : HasDerivAt f first (inner x) := by
    rw [hpoint]
    exact hf
  have hcomp := hf'.comp x hinner
  have hscaled := hcomp.const_mul c
  have hfun : affinePullback a b c f =
      (fun w : ℂ => c * f (inner w)) := by
    funext w
    simp only [affinePullback]
    congr 2
    simp only [inner, Pi.add_apply, Pi.sub_apply, id_eq]
    dsimp [x, affineCoordinate]
    field_simp [ha]
    ring
  rw [hfun]
  simpa [x, affineCoordinate, inner, div_eq_mul_inv, mul_assoc] using hscaled

/-! ## Normalized complex residual direction -/

/-- The normalized negative residual gradient equals the negative Newton residual direction. -/
theorem normalizedResidualDirection_eq_newtonDirection {value first : ℂ}
    (hfirst : first ≠ 0) :
    -star first * value / Complex.normSq first = -value / first := by
  rw [Complex.normSq_eq_conj_mul_self]
  field_simp [hfirst]
  rw [starRingEnd_apply]
  ring

end Holonics.Mathematics.AnalyticNavigation

section Audit
open Holonics.Mathematics.AnalyticNavigation
#print axioms hasDerivAt_newtonMap
#print axioms hasDerivAt_residual_release
#print axioms affinePullback_value
#print axioms hasDerivAt_affinePullback
#print axioms normalizedResidualDirection_eq_newtonDirection
end Audit
