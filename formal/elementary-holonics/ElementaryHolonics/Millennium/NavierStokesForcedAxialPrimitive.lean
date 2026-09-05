import ElementaryHolonics.Millennium.NavierStokesAxialPrimitive
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The changing axis returns its forced axial primitive

The time and viscous source belongs in the axial equation. For positive F, the actual primitive
F*integral(S/F²) supplies its oriented correction. The zero-axis anchor selects a representative
of the homogeneous cF fibre. A first-viscosity response includes the corresponding forced term;
it does not silently preserve the instantaneous Euler axis relation.
-/

noncomputable section

open ContDiff Set MeasureTheory Filter
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesForcedAxialPrimitive

open Soma.Holonics.Millennium.NavierStokesAxialPrimitive

def forcingPrimitive (F S : ℝ → ℝ) (z : ℝ) : ℝ := ∫ r in (0 : ℝ)..z, S r / F r ^ 2

def forcingCarrier (F S : ℝ → ℝ) (z : ℝ) : ℝ := F z * forcingPrimitive F S z

def forcedAxialW (alpha beta : ℝ) (F S : ℝ → ℝ) (z : ℝ) : ℝ :=
  axialW alpha beta F z + forcingCarrier F S z

theorem forcingPrimitive_hasDerivAt (F S : ℝ → ℝ) (hF : Continuous F)
    (hpositive : ∀ z, 0 < F z) (hS : Continuous S) (z : ℝ) :
    HasDerivAt (forcingPrimitive F S) (S z / F z ^ 2) z := by
  have hc : Continuous (fun r ↦ S r / F r ^ 2) :=
    hS.div (hF.pow 2) (fun r ↦ pow_ne_zero 2 (hpositive r).ne')
  exact (hc.integral_hasStrictDerivAt (0 : ℝ) z).hasDerivAt

theorem forcingCarrier_hasDerivAt (F S : ℝ → ℝ) (hF : Differentiable ℝ F)
    (hpositive : ∀ z, 0 < F z) (hS : Continuous S) (z : ℝ) :
    HasDerivAt (forcingCarrier F S)
      (deriv F z * forcingPrimitive F S z + S z / F z) z := by
  have h := (hF z).hasDerivAt.mul
    (forcingPrimitive_hasDerivAt F S hF.continuous hpositive hS z)
  convert h using 1 <;> first | rfl | (field_simp [(hpositive z).ne'] <;> ring)

theorem forcingCarrier_wronskian (F S : ℝ → ℝ) (hF : Differentiable ℝ F)
    (hpositive : ∀ z, 0 < F z) (hS : Continuous S) (z : ℝ) :
    F z * deriv (forcingCarrier F S) z - deriv F z * forcingCarrier F S z = S z := by
  rw [(forcingCarrier_hasDerivAt F S hF hpositive hS z).deriv]
  unfold forcingCarrier
  field_simp [(hpositive z).ne']
  ring

@[simp] theorem forcingCarrier_zero (F S : ℝ → ℝ) : forcingCarrier F S 0 = 0 := by
  simp [forcingCarrier, forcingPrimitive]

@[simp] theorem forcedAxialW_zero (alpha beta : ℝ) (F S : ℝ → ℝ) :
    forcedAxialW alpha beta F S 0 = 0 := by simp [forcedAxialW]

theorem forcedAxialW_differentiable (alpha beta : ℝ) (F S : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z) (hS : Continuous S) :
    Differentiable ℝ (forcedAxialW alpha beta F S) := by
  intro z
  exact ((hasDerivAt_axialW alpha beta F hF hpositive z).add
    (forcingCarrier_hasDerivAt F S (hF.differentiable (by norm_num)) hpositive hS z)).differentiableAt

theorem forcedAxialW_origin_derivative (alpha beta : ℝ) (F S : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z) (hS : Continuous S) :
    deriv (forcedAxialW alpha beta F S) 0 = alpha + beta + S 0 / F 0 := by
  have h := (hasDerivAt_axialW alpha beta F hF hpositive 0).add
    (forcingCarrier_hasDerivAt F S (hF.differentiable (by norm_num)) hpositive hS 0)
  change HasDerivAt (forcedAxialW alpha beta F S) _ 0 at h
  rw [h.deriv]
  simp [primitiveInv, forcingPrimitive]
  field_simp [(hpositive 0).ne']
  ring

/-- The source S is returned by actual differentiation of the constructed primitive. -/
theorem forcedAxialW_axis_identity (alpha beta : ℝ) (F S : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z) (hS : Continuous S) (z : ℝ) :
    S z + (forcedAxialW alpha beta F S z + beta * z) * deriv F z +
      (alpha + beta - deriv (forcedAxialW alpha beta F S) z) * F z = 0 := by
  have hbase := axialW_axis_identity alpha beta F hF hpositive z
  have hcarrier := forcingCarrier_wronskian F S (hF.differentiable (by norm_num)) hpositive hS z
  have hd := (hasDerivAt_axialW alpha beta F hF hpositive z).add
    (forcingCarrier_hasDerivAt F S (hF.differentiable (by norm_num)) hpositive hS z)
  have hsum : deriv (forcedAxialW alpha beta F S) z =
      deriv (axialW alpha beta F) z + deriv (forcingCarrier F S) z := by
    exact deriv_fun_add (hasDerivAt_axialW alpha beta F hF hpositive z).differentiableAt
      (forcingCarrier_hasDerivAt F S (hF.differentiable (by norm_num)) hpositive hS z).differentiableAt
  rw [hsum]
  unfold forcedAxialW
  linear_combination hbase - hcarrier

theorem forcingPrimitive_contDiff (F S : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z, 0 < F z) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (forcingPrimitive F S) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun z ↦ (forcingPrimitive_hasDerivAt F S hF.continuous hpositive hS.continuous z).differentiableAt, ?_⟩
  have hd : deriv (forcingPrimitive F S) = fun z ↦ S z / F z ^ 2 :=
    funext fun z ↦ (forcingPrimitive_hasDerivAt F S hF.continuous hpositive hS.continuous z).deriv
  rw [hd]
  exact hS.div (hF.pow 2) (fun z ↦ pow_ne_zero 2 (hpositive z).ne')

theorem forcedAxialW_contDiff (alpha beta : ℝ) (F S : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hpositive : ∀ z, 0 < F z) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (forcedAxialW alpha beta F S) :=
  (contDiff_infty_axialW alpha beta F hF hpositive).add
    (hF.mul (forcingPrimitive_contDiff F S hF hpositive hS))

def axisTimeSource (F K : ℝ → ℝ → ℝ) (mu : ℝ → ℝ) (t z : ℝ) : ℝ :=
  deriv (fun τ ↦ F τ z) t - mu t * (8 * K t z + deriv (deriv (F t)) z)

/-- The time source uses the actual derivative of the selected shape and the declared first
radial swirl coefficient. The constructed W then pays the complete axis equation. -/
theorem moving_axis_identity (alpha beta : ℝ) (F K : ℝ → ℝ → ℝ) (mu : ℝ → ℝ) (t z : ℝ)
    (hF : ContDiff ℝ 2 (F t)) (hpositive : ∀ r, 0 < F t r)
    (hsource : Continuous (axisTimeSource F K mu t)) :
    let W := forcedAxialW alpha beta (F t) (axisTimeSource F K mu t)
    deriv (fun τ ↦ F τ z) t + (W z + beta * z) * deriv (F t) z +
      (alpha + beta - deriv W z) * F t z = mu t * (8 * K t z + deriv (deriv (F t)) z) := by
  dsimp only
  have h := forcedAxialW_axis_identity alpha beta (F t) (axisTimeSource F K mu t)
    hF hpositive hsource z
  have hs : axisTimeSource F K mu t z =
      deriv (fun τ ↦ F τ z) t - mu t * (8 * K t z + deriv (deriv (F t)) z) := rfl
  rw [hs] at h
  linear_combination h

/-- The homogeneous cF fibre is retained until an axial value fixes it. -/
theorem forcedAxialW_homogeneous_fibre (alpha beta c : ℝ) (F S : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z) (hS : Continuous S) (z : ℝ) :
    let W := fun r ↦ forcedAxialW alpha beta F S r + c * F r
    S z + (W z + beta * z) * deriv F z + (alpha + beta - deriv W z) * F z = 0 := by
  dsimp only
  have h := forcedAxialW_axis_identity alpha beta F S hF hpositive hS z
  rw [deriv_fun_add (forcedAxialW_differentiable alpha beta F S hF hpositive hS z)
    ((hF.differentiable (by norm_num) z).const_mul c),
    deriv_const_mul c (hF.differentiable (by norm_num) z)]
  linear_combination h

/-- The source and value at zero uniquely determine the anchored axial velocity. -/
theorem forcedAxialW_unique (alpha beta : ℝ) (F S W : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z) (hS : Continuous S)
    (hW : Differentiable ℝ W) (hzero : W 0 = 0)
    (haxis : ∀ z, S z + (W z + beta * z) * deriv F z +
      (alpha + beta - deriv W z) * F z = 0) : W = forcedAxialW alpha beta F S := by
  let difference : ℝ → ℝ := fun z ↦ (W z - forcedAxialW alpha beta F S z) / F z
  have hdiff := forcedAxialW_differentiable alpha beta F S hF hpositive hS
  have hd : ∀ z, HasDerivAt difference 0 z := by
    intro z
    have h := ((hW z).hasDerivAt.sub (hdiff z).hasDerivAt).div
      (hF.differentiable (by norm_num) z).hasDerivAt (hpositive z).ne'
    have hnum : (deriv W z - deriv (forcedAxialW alpha beta F S) z) * F z -
        (W z - forcedAxialW alpha beta F S z) * deriv F z = 0 := by
      linear_combination forcedAxialW_axis_identity alpha beta F S hF hpositive hS z - haxis z
    convert h using 1 <;> first | rfl | (simp only [Pi.sub_apply]; rw [hnum]; simp)
  have hconst := is_const_of_deriv_eq_zero (fun z ↦ (hd z).differentiableAt)
    (fun z ↦ (hd z).deriv)
  funext z
  have hz := hconst z 0
  have hquot : (W z - forcedAxialW alpha beta F S z) / F z = 0 := by
    simpa [difference, hzero] using hz
  have hn := congrArg (fun q : ℝ ↦ q * F z) hquot
  field_simp [(hpositive z).ne'] at hn
  exact sub_eq_zero.mp (by simpa using hn)

/-- Constructed linear response in the axial shape, plus its independent source primitive. -/
def linearAxisResponse (alpha beta : ℝ) (F f S : ℝ → ℝ) (z : ℝ) : ℝ :=
  (alpha + 2 * beta) * (f z * primitiveInv F z - forcingCarrier F f z) + forcingCarrier F S z

theorem linearAxisResponse_hasDerivAt (alpha beta : ℝ) (F f S : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z)
    (hf : Differentiable ℝ f) (hS : Continuous S) (z : ℝ) :
    HasDerivAt (linearAxisResponse alpha beta F f S)
      ((alpha + 2 * beta) * (deriv f z * primitiveInv F z - deriv F z * forcingPrimitive F f z) +
        deriv F z * forcingPrimitive F S z + S z / F z) z := by
  have h := ((((hf z).hasDerivAt.mul (hasDerivAt_primitiveInv F hF hpositive z)).sub
    (forcingCarrier_hasDerivAt F f (hF.differentiable (by norm_num)) hpositive hf.continuous z)).const_mul
    (alpha + 2 * beta)).add
    (forcingCarrier_hasDerivAt F S (hF.differentiable (by norm_num)) hpositive hS z)
  convert h using 1 <;> first | rfl | (field_simp [(hpositive z).ne']; ring)

theorem linearAxisResponse_returns_source (alpha beta : ℝ) (F f S : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z)
    (hf : Differentiable ℝ f) (hS : Continuous S) (z : ℝ) :
    axialGamma alpha beta F z * deriv f z +
      (alpha + beta - deriv (axialW alpha beta F) z) * f z +
      linearAxisResponse alpha beta F f S z * deriv F z -
      deriv (linearAxisResponse alpha beta F f S) z * F z = -S z := by
  rw [(linearAxisResponse_hasDerivAt alpha beta F f S hF hpositive hf hS z).deriv,
    (hasDerivAt_axialW alpha beta F hF hpositive z).deriv]
  unfold linearAxisResponse forcingCarrier axialGamma
  field_simp [(hpositive z).ne']
  ring

/-- The decaying viscosity mu'=-delta*mu shifts the axis equation by -delta*f. -/
theorem firstViscousAxisResponse (alpha beta delta : ℝ) (F f Phi : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z)
    (hf : Differentiable ℝ f) (hPhi : Continuous Phi) (z : ℝ) :
    let w := linearAxisResponse alpha beta F f (fun r ↦ -delta * f r - Phi r)
    axialGamma alpha beta F z * deriv f z +
      (alpha + beta - deriv (axialW alpha beta F) z - delta) * f z +
      w z * deriv F z - deriv w z * F z = Phi z := by
  dsimp only
  have h := linearAxisResponse_returns_source alpha beta F f (fun r ↦ -delta * f r - Phi r)
    hF hpositive hf ((continuous_const.mul hf.continuous).sub hPhi) z
  linear_combination h

#print axioms forcingCarrier_wronskian
#print axioms forcedAxialW_origin_derivative
#print axioms forcedAxialW_axis_identity
#print axioms forcedAxialW_contDiff
#print axioms moving_axis_identity
#print axioms forcedAxialW_homogeneous_fibre
#print axioms forcedAxialW_unique
#print axioms linearAxisResponse_returns_source
#print axioms firstViscousAxisResponse

end Soma.Holonics.Millennium.NavierStokesForcedAxialPrimitive
