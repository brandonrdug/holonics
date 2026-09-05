import ElementaryHolonics.Millennium.NavierStokesAxialPrimitive
import ElementaryHolonics.Millennium.NavierStokesAxialLift
import ElementaryHolonics.Millennium.NavierStokesAxisRegularization
import ElementaryHolonics.Millennium.NavierStokesAxisFirstJet
import ElementaryHolonics.Millennium.NavierStokesFirstRadialLift
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The positive algebraic axial profile and its constructed strain

The source is the actual function `(1+z²)^(-p/2)`. Its positivity, smoothness and axial jets
are derived, then composed with the reciprocal primitive construction for the axial velocity.
-/

noncomputable section

open ContDiff Set Filter InnerProductSpace
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesAlgebraicAxis

open Soma.Holonics.Millennium.NavierStokesAxialPrimitive
open Soma.Holonics.Millennium.NavierStokesAxialLift
open Soma.Holonics.Millennium.NavierStokesAxisRegularization
open Soma.Holonics.Millennium.NavierStokesAxisFirstJet
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFirstRadialLift

def algebraicProfile (p z : ℝ) : ℝ := (1 + z ^ 2) ^ (-p / 2)

theorem algebraicProfile_positive (p z : ℝ) : 0 < algebraicProfile p z := by
  unfold algebraicProfile
  exact Real.rpow_pos_of_pos (by positivity) _

theorem algebraicProfile_contDiff (p : ℝ) : ContDiff ℝ ∞ (algebraicProfile p) := by
  have hb : ContDiff ℝ ∞ (fun z : ℝ ↦ 1 + z ^ 2) := by fun_prop
  exact hb.rpow_const_of_ne (fun z ↦ by positivity)

@[simp] theorem algebraicProfile_zero (p : ℝ) : algebraicProfile p 0 = 1 := by
  simp [algebraicProfile]

theorem algebraicProfile_hasDerivAt (p z : ℝ) :
    HasDerivAt (algebraicProfile p) (-p * z * algebraicProfile (p + 2) z) z := by
  have hb := ((hasDerivAt_id z).pow 2).const_add 1
  have hbase : (1 + z ^ 2 : ℝ) ≠ 0 := by positivity
  have hpow := hb.rpow_const (p := -p / 2) (Or.inl hbase)
  have he : -p / 2 - 1 = -(p + 2) / 2 := by ring
  convert hpow using 1 <;> first | rfl | (simp [algebraicProfile, he] <;> ring)

theorem algebraicProfile_deriv (p : ℝ) :
    deriv (algebraicProfile p) = fun z ↦ -p * z * algebraicProfile (p + 2) z :=
  funext fun z ↦ (algebraicProfile_hasDerivAt p z).deriv

@[simp] theorem algebraicProfile_deriv_zero (p : ℝ) : deriv (algebraicProfile p) 0 = 0 := by
  rw [algebraicProfile_deriv]
  simp

theorem algebraicProfile_second_jet_zero (p : ℝ) :
    HasDerivAt (deriv (algebraicProfile p)) (-p) 0 := by
  rw [algebraicProfile_deriv]
  have h := (hasDerivAt_const_mul (-p) (x := 0)).mul (algebraicProfile_hasDerivAt (p + 2) 0)
  convert h using 1 <;> first | rfl | simp

def algebraicStrain (alpha beta p : ℝ) : ℝ → ℝ := axialW alpha beta (algebraicProfile p)

theorem algebraicStrain_contDiff (alpha beta p : ℝ) :
    ContDiff ℝ ∞ (algebraicStrain alpha beta p) :=
  contDiff_infty_axialW alpha beta (algebraicProfile p) (algebraicProfile_contDiff p)
    (algebraicProfile_positive p)

theorem algebraicStrain_axis_identity (alpha beta p z : ℝ) :
    (algebraicStrain alpha beta p z + beta * z) * deriv (algebraicProfile p) z +
      (alpha + beta - deriv (algebraicStrain alpha beta p) z) * algebraicProfile p z = 0 :=
  axialW_axis_identity alpha beta (algebraicProfile p)
    ((algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top))
    (algebraicProfile_positive p) z

@[simp] theorem algebraicStrain_zero (alpha beta p : ℝ) : algebraicStrain alpha beta p 0 = 0 := by
  simp [algebraicStrain]

theorem algebraicStrain_deriv (alpha beta p : ℝ) :
    deriv (algebraicStrain alpha beta p) = fun z ↦
      (alpha + 2 * beta) * deriv (algebraicProfile p) z * primitiveInv (algebraicProfile p) z
        + (alpha + beta) := by
  funext z
  unfold algebraicStrain
  rw [(hasDerivAt_axialW alpha beta (algebraicProfile p)
    ((algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top))
    (algebraicProfile_positive p) z).deriv]
  have hF : algebraicProfile p z ≠ 0 := (algebraicProfile_positive p z).ne'
  field_simp
  ring

@[simp] theorem algebraicStrain_deriv_zero (alpha beta p : ℝ) :
    deriv (algebraicStrain alpha beta p) 0 = alpha + beta := by
  rw [algebraicStrain_deriv]
  simp

theorem algebraicStrain_second_jet_zero (alpha beta p : ℝ) :
    HasDerivAt (deriv (algebraicStrain alpha beta p)) 0 0 := by
  rw [algebraicStrain_deriv]
  have h := (((algebraicProfile_second_jet_zero p).const_mul (alpha + 2 * beta)).mul
    (hasDerivAt_primitiveInv (algebraicProfile p)
      ((algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top))
      (algebraicProfile_positive p) 0)).add_const (alpha + beta)
  convert h using 1 <;> first | rfl | simp

@[simp] theorem algebraicStrain_second_deriv_zero (alpha beta p : ℝ) :
    deriv (deriv (algebraicStrain alpha beta p)) 0 = 0 :=
  (algebraicStrain_second_jet_zero alpha beta p).deriv

theorem algebraicStrain_second_deriv (alpha beta p : ℝ) :
    deriv (deriv (algebraicStrain alpha beta p)) = fun z ↦
      (alpha + 2 * beta) * deriv (deriv (algebraicProfile p)) z * primitiveInv (algebraicProfile p) z
        + (alpha + 2 * beta) * deriv (algebraicProfile p) z * (algebraicProfile p z)⁻¹ := by
  have hF1 : ContDiff ℝ ∞ (deriv (algebraicProfile p)) := by
    have := algebraicProfile_contDiff p
    fun_prop
  rw [algebraicStrain_deriv]
  funext z
  have h := ((((hF1.differentiable (by simp) z).hasDerivAt).const_mul (alpha + 2 * beta)).mul
    (hasDerivAt_primitiveInv (algebraicProfile p)
      ((algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top))
      (algebraicProfile_positive p) z)).add_const (alpha + beta)
  convert h.deriv using 1 <;> first | rfl | ring

theorem algebraicStrain_third_jet_zero (alpha beta p : ℝ) :
    HasDerivAt (deriv (deriv (algebraicStrain alpha beta p)))
      (-2 * (alpha + 2 * beta) * p) 0 := by
  have hF2 : ContDiff ℝ ∞ (deriv (deriv (algebraicProfile p))) := by
    have := algebraicProfile_contDiff p
    fun_prop
  have hI := hasDerivAt_primitiveInv (algebraicProfile p)
    ((algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top))
    (algebraicProfile_positive p) 0
  have hiF := (algebraicProfile_hasDerivAt p 0).inv (by simp)
  have h := ((((hF2.differentiable (by simp) 0).hasDerivAt).const_mul (alpha + 2 * beta)).mul hI).add
    (((algebraicProfile_second_jet_zero p).const_mul (alpha + 2 * beta)).mul hiF)
  rw [algebraicStrain_second_deriv]
  convert h using 1 <;>
    first | rfl | (simp [(algebraicProfile_second_jet_zero p).deriv] <;> ring)

@[simp] theorem algebraicStrain_third_deriv_zero (alpha beta p : ℝ) :
    deriv (deriv (deriv (algebraicStrain alpha beta p))) 0 = -2 * (alpha + 2 * beta) * p :=
  (algebraicStrain_third_jet_zero alpha beta p).deriv

def algebraicPressureCoefficient (alpha beta p : ℝ) : ℝ → ℝ :=
  axialA (algebraicProfile p) (algebraicStrain alpha beta p) alpha beta

theorem algebraicPressureCoefficient_contDiff (alpha beta p : ℝ) :
    ContDiff ℝ ∞ (algebraicPressureCoefficient alpha beta p) := by
  have hF := algebraicProfile_contDiff p
  have hW := algebraicStrain_contDiff alpha beta p
  unfold algebraicPressureCoefficient axialA
  fun_prop

@[simp] theorem algebraicPressureCoefficient_deriv_zero (alpha beta p : ℝ) :
    deriv (algebraicPressureCoefficient alpha beta p) 0 = 0 := by
  unfold algebraicPressureCoefficient
  rw [axialA_deriv _ _ (algebraicProfile_contDiff p) (algebraicStrain_contDiff alpha beta p)]
  simp

theorem algebraicPressureCoefficient_second_jet_zero (alpha beta p : ℝ) :
    HasDerivAt (deriv (algebraicPressureCoefficient alpha beta p))
      (2 * p * (1 + (alpha + 2 * beta) ^ 2)) 0 := by
  have hW3 : ContDiff ℝ ∞ (deriv (deriv (deriv (algebraicStrain alpha beta p)))) := by
    have := algebraicStrain_contDiff alpha beta p
    fun_prop
  have hW := (algebraicStrain_contDiff alpha beta p).differentiable (by simp) 0 |>.hasDerivAt
  have hgamma := hW.add ((hasDerivAt_id 0).const_mul beta)
  have hfirst := ((algebraicProfile_hasDerivAt p 0).mul (algebraicProfile_second_jet_zero p)).const_mul (-2)
  have hsecond := ((hgamma.mul ((hW3.differentiable (by simp) 0).hasDerivAt)).add
    ((algebraicStrain_third_jet_zero alpha beta p).const_mul (alpha + 2 * beta))).div_const 2
  have h := hfirst.sub hsecond
  unfold algebraicPressureCoefficient
  rw [axialA_deriv _ _ (algebraicProfile_contDiff p) (algebraicStrain_contDiff alpha beta p)]
  convert h using 1
  all_goals
    first
    | rfl
    | (funext z; simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq]; ring)
    | (simp <;> ring)

/-- The axial equation alone does not complete the affine-radial velocity into an Euler profile:
the actual radial pressure coefficient has a strictly nonzero second jet at the origin. -/
theorem algebraicAxialLift_has_no_pressure_completion (alpha beta p : ℝ) (hp : 0 < p) :
    ¬ ∃ pressure : Space → ℝ, ContDiff ℝ 2 pressure ∧
      ∀ x, axialResidual (algebraicProfile p) (algebraicStrain alpha beta p) alpha beta x +
        gradient pressure x = 0 := by
  rintro ⟨pressure, hpressure, hbalance⟩
  have hcompat := pressure_balance_implies_compatibility (algebraicProfile p)
    (algebraicStrain alpha beta p) (algebraicProfile_contDiff p)
    (algebraicStrain_contDiff alpha beta p) alpha beta pressure hpressure hbalance
  have heq : deriv (algebraicPressureCoefficient alpha beta p) = fun _ ↦ 0 :=
    funext fun z ↦ (hcompat z).2
  have hjet := (algebraicPressureCoefficient_second_jet_zero alpha beta p).deriv
  rw [heq, deriv_const] at hjet
  have hpositive : 0 < 2 * p * (1 + (alpha + 2 * beta) ^ 2) := by positivity
  linarith

def algebraicRadialCorrection (alpha beta p : ℝ) : ℝ → ℝ :=
  axialH alpha beta (algebraicPressureCoefficient alpha beta p) (algebraicProfile p)

@[simp] theorem algebraicRadialCorrection_zero (alpha beta p : ℝ) :
    algebraicRadialCorrection alpha beta p 0 = 0 := by
  simp [algebraicRadialCorrection, axialH]

theorem algebraicRadialCorrection_first_jet_zero (alpha beta p : ℝ)
    (hk : alpha + 2 * beta ≠ 0) :
    HasDerivAt (algebraicRadialCorrection alpha beta p)
      (p * (1 + (alpha + 2 * beta) ^ 2) / (2 * (alpha + 2 * beta))) 0 := by
  have h := hasDerivAt_axialH_zero alpha beta (algebraicPressureCoefficient alpha beta p)
    (algebraicProfile p)
    ((algebraicPressureCoefficient_contDiff alpha beta p).of_le (WithTop.coe_le_coe.mpr le_top))
    ((algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top))
    (algebraicProfile_positive p) hk (algebraicPressureCoefficient_deriv_zero alpha beta p)
  rw [(algebraicPressureCoefficient_second_jet_zero alpha beta p).deriv] at h
  convert h using 1 <;> first | rfl | (field_simp; ring)

theorem algebraicRadialCorrection_differentiable (alpha beta p : ℝ)
    (hk : alpha + 2 * beta ≠ 0) : Differentiable ℝ (algebraicRadialCorrection alpha beta p) := by
  intro z
  by_cases hz : z = 0
  · subst z
    exact (algebraicRadialCorrection_first_jet_zero alpha beta p hk).differentiableAt
  · have hF2 : ContDiff ℝ 2 (algebraicProfile p) :=
      (algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top)
    exact (axialH_pressure_compatibility alpha beta (algebraicPressureCoefficient alpha beta p)
      (algebraicProfile p)
      ((algebraicPressureCoefficient_contDiff alpha beta p).of_le (WithTop.coe_le_coe.mpr le_top))
      hF2 (algebraicProfile_positive p) z hz
      (axialGamma_ne_zero_of_nonzero alpha beta (algebraicProfile p) hF2
        (algebraicProfile_positive p) hk hz)).differentiableAt

theorem algebraicRadialCorrection_pressure_identity (alpha beta p : ℝ)
    (hk : alpha + 2 * beta ≠ 0) (z : ℝ) :
    axialGamma alpha beta (algebraicProfile p) z * deriv (algebraicRadialCorrection alpha beta p) z +
      (alpha + 2 * beta) * algebraicRadialCorrection alpha beta p z =
        deriv (algebraicPressureCoefficient alpha beta p) z / 2 := by
  by_cases hz : z = 0
  · subst z
    simp [axialGamma]
  · exact axialH_pressure_compatibility_identity_of_nonzero alpha beta
      (algebraicPressureCoefficient alpha beta p) (algebraicProfile p)
      ((algebraicPressureCoefficient_contDiff alpha beta p).of_le (WithTop.coe_le_coe.mpr le_top))
      ((algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top))
      (algebraicProfile_positive p) hk z hz

/-- Paying the first swirl coefficient fixes the value of the next radial swirl carrier.
Its remaining quadratic coefficient is strictly positive in the proposed concentration window. -/
theorem algebraic_firstSwirl_payment_leaves_quadratic_defect
    (alpha beta p : ℝ) (hbeta : 0 < beta) (halpha : beta < alpha) (hp : 0 < p)
    (K : ℝ → ℝ) (_hK : DifferentiableAt ℝ K 0)
    (hpayment : firstSwirlCoefficient alpha beta (algebraicProfile p)
      (algebraicStrain alpha beta p) (algebraicRadialCorrection alpha beta p) K 0 = 0) :
    0 < secondSwirlCoefficient (algebraicRadialCorrection alpha beta p) K 0 := by
  have hk : 0 < alpha + 2 * beta := by linarith
  have hj := (algebraicRadialCorrection_first_jet_zero alpha beta p hk.ne').deriv
  have hjetpos : 0 < deriv (algebraicRadialCorrection alpha beta p) 0 := by
    rw [hj]
    positivity
  have hpay : (beta - alpha) * K 0 = deriv (algebraicRadialCorrection alpha beta p) 0 / 2 := by
    unfold firstSwirlCoefficient at hpayment
    simp only [algebraicStrain_zero, mul_zero, zero_add, algebraicStrain_deriv_zero,
      algebraicRadialCorrection_zero, algebraicProfile_deriv_zero, zero_mul,
      algebraicProfile_zero, mul_one, add_zero] at hpayment
    nlinarith
  have hKnegative : K 0 < 0 := by
    by_contra hn
    have hnonneg := le_of_not_gt hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg (by linarith : beta - alpha ≤ 0) hnonneg
    linarith
  simp only [secondSwirlCoefficient, algebraicRadialCorrection_zero, zero_mul, zero_sub]
  exact neg_pos.mpr (mul_neg_of_pos_of_neg hjetpos hKnegative)

#print axioms algebraicProfile_contDiff
#print axioms algebraicProfile_hasDerivAt
#print axioms algebraicProfile_second_jet_zero
#print axioms algebraicStrain_axis_identity
#print axioms algebraicStrain_second_jet_zero
#print axioms algebraicStrain_third_jet_zero
#print axioms algebraicPressureCoefficient_second_jet_zero
#print axioms algebraicAxialLift_has_no_pressure_completion
#print axioms algebraicRadialCorrection_first_jet_zero
#print axioms algebraicRadialCorrection_differentiable
#print axioms algebraicRadialCorrection_pressure_identity
#print axioms algebraic_firstSwirl_payment_leaves_quadratic_defect

end Soma.Holonics.Millennium.NavierStokesAlgebraicAxis
