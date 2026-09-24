import ElementaryHolonics.Millennium.NavierStokesParabolicRebase
import ElementaryHolonics.Millennium.NavierStokesPeriodicEnstrophy
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The parabolic vorticity current retains its transported cell

**[proved-derived]** The Navier--Stokes parabolic rebase is already known to carry every
term of the momentum equation with the same cubic weight.  This file transports the
vorticity receivers through the same source passage.  The spatial receiver is not silently
held fixed: at positive scale `lambda`, the source unit cube is observed through the
preimage cell `lambda⁻¹ • unitCube`.

The returned laws are exact:

* vorticity has pointwise weight `lambda²`;
* its complete spatial derivative has pointwise weight `lambda³`;
* enstrophy on the transported cell has weight `lambda`;
* derivative dissipation on the transported cell has weight `lambda³`; and
* fourth-power vorticity mass on the transported cell has weight `lambda⁵`.

The last three exponents contain both contributions: the field weight and the inverse-cubic
Jacobian of the transported three-dimensional cell.  Thus the quartic receiver is compared
along an actual PDE-preserving scale family, rather than along an amplitude change which leaves
the other Navier--Stokes data fixed.
-/

noncomputable section

open InnerProductSpace MeasureTheory Set
open scoped BigOperators Pointwise

namespace Soma.Holonics.Millennium.NavierStokesParabolicVorticityCurrent

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesParabolicRebase
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## Pointwise constitutive transport -/

/-- Curl adds one spatial chart factor to the transported velocity amplitude. -/
theorem vorticityField_parabolicVelocity
    (scale : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ) :
    vorticityField (parabolicVelocity scale velocity) x t =
      scale ^ 2 • vorticityField velocity (scale • x) (scale ^ 2 * t) := by
  unfold vorticityField vorticityAt velocityJacobianAt
  rw [fderiv_parabolicVelocity]
  exact map_smul derivativeCurlLinearMap (scale ^ 2) _

/-- The complete spatial derivative of vorticity carries one further chart factor. -/
theorem fderiv_vorticityField_parabolicVelocity
    (scale : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ) :
    fderiv ℝ (fun y ↦ vorticityField (parabolicVelocity scale velocity) y t) x =
      scale ^ 3 •
        fderiv ℝ (fun y ↦ vorticityField velocity y (scale ^ 2 * t)) (scale • x) := by
  have hfunction :
      (fun y ↦ vorticityField (parabolicVelocity scale velocity) y t) =
        scale ^ 2 •
          (fun y ↦ vorticityField velocity (scale • y) (scale ^ 2 * t)) := by
    funext y
    exact vorticityField_parabolicVelocity scale velocity y t
  rw [hfunction, congrFun (fderiv_const_smul_of_field (scale ^ 2)) x]
  simp only [Pi.smul_apply]
  have hcomp :
      fderiv ℝ (fun y ↦ vorticityField velocity (scale • y) (scale ^ 2 * t)) x =
        scale •
          fderiv ℝ (fun y ↦ vorticityField velocity y (scale ^ 2 * t)) (scale • x) := by
    simpa only using
      (fderiv_comp_smul
        (f := fun y ↦ vorticityField velocity y (scale ^ 2 * t))
        (x := x) scale)
  rw [hcomp, smul_smul]
  congr 1

/-- Each scalar vorticity-component gradient carries the same cubic weight.  This is the
component-gradient receiver used by the existing periodic enstrophy balance, rather than a new
coordinate-derivative surrogate. -/
theorem gradient_vorticityComponent_parabolicVelocity
    (scale : ℝ) (velocity : VelocityField) (component : Fin 3) (x : Space) (t : ℝ) :
    gradient
        (fun y ↦ vorticityField (parabolicVelocity scale velocity) y t component) x =
      scale ^ 3 •
        gradient (fun y ↦ vorticityField velocity y (scale ^ 2 * t) component)
          (scale • x) := by
  unfold gradient
  have hfunction :
      (fun y ↦ vorticityField (parabolicVelocity scale velocity) y t component) =
        scale ^ 2 •
          (fun y ↦ vorticityField velocity (scale • y) (scale ^ 2 * t) component) := by
    funext y
    simpa using
      congrArg (fun value : Space ↦ value component)
        (vorticityField_parabolicVelocity scale velocity y t)
  rw [hfunction, congrFun (fderiv_const_smul_of_field (scale ^ 2)) x]
  simp only [Pi.smul_apply]
  have hcomp :
      fderiv ℝ
          (fun y ↦ vorticityField velocity (scale • y) (scale ^ 2 * t) component) x =
        scale •
          fderiv ℝ (fun y ↦ vorticityField velocity y (scale ^ 2 * t) component)
            (scale • x) := by
    simpa only using
      (fderiv_comp_smul
        (f := fun y ↦ vorticityField velocity y (scale ^ 2 * t) component)
        (x := x) scale)
  rw [hcomp]
  simp only [map_smul, smul_smul]
  congr 1

/-! ## Receiver populations before the cell return -/

/-- Half the squared vorticity population on a declared spatial receiver cell. -/
def enstrophyOn (cell : Set Space) (velocity : VelocityField) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in cell, ‖vorticityField velocity x t‖ ^ 2

/-- The component-gradient-square vorticity population on a declared cell.  At `unitCube` this
is definitionally the established periodic viscous-dissipation receiver. -/
def vorticityDerivativeDissipationOn
    (cell : Set Space) (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in cell, ∑ component : Fin 3,
    ‖gradient (fun y ↦ vorticityField velocity y t component) x‖ ^ 2

theorem vorticityDerivativeDissipationOn_unitCube
    (velocity : VelocityField) (t : ℝ) :
    vorticityDerivativeDissipationOn unitCube velocity t =
      periodicVorticityDissipation velocity t := rfl

/-- The fourth-power vorticity population on a declared spatial receiver cell. -/
def vorticityFourthPowerOn
    (cell : Set Space) (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in cell, ‖vorticityField velocity x t‖ ^ 4

/-- The spatial cell whose positive-scale image is the source unit cube. -/
def parabolicCell (scale : ℝ) : Set Space := scale⁻¹ • unitCube

theorem scale_smul_parabolicCell
    {scale : ℝ} (hscale : scale ≠ 0) :
    scale • parabolicCell scale = unitCube := by
  simp [parabolicCell, ← mul_smul, hscale]

/-! ## Exact transported-cell laws -/

/-- The square-norm vorticity density carries pointwise weight four. -/
theorem norm_vorticityField_parabolicVelocity_sq
    (scale : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ) :
    ‖vorticityField (parabolicVelocity scale velocity) x t‖ ^ 2 =
      scale ^ 4 * ‖vorticityField velocity (scale • x) (scale ^ 2 * t)‖ ^ 2 := by
  rw [vorticityField_parabolicVelocity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg scale), mul_pow]
  ring

/-- The fourth-power density carries pointwise weight eight. -/
theorem norm_vorticityField_parabolicVelocity_fourth
    (scale : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ) :
    ‖vorticityField (parabolicVelocity scale velocity) x t‖ ^ 4 =
      scale ^ 8 * ‖vorticityField velocity (scale • x) (scale ^ 2 * t)‖ ^ 4 := by
  rw [vorticityField_parabolicVelocity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg scale), mul_pow]
  ring

/-- Every component-gradient-square density carries pointwise weight six. -/
theorem vorticityDerivativeDensity_parabolicVelocity
    {scale : ℝ} (velocity : VelocityField) (x : Space) (t : ℝ) :
    (∑ component : Fin 3,
        ‖gradient
            (fun y ↦ vorticityField (parabolicVelocity scale velocity) y t component) x‖ ^ 2) =
      scale ^ 6 *
        ∑ component : Fin 3,
          ‖gradient (fun y ↦ vorticityField velocity y (scale ^ 2 * t) component)
            (scale • x)‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  rw [gradient_vorticityComponent_parabolicVelocity]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Enstrophy gains field weight four and loses three weights to the transported cell, leaving
the exact critical weight one. -/
theorem enstrophyOn_parabolicCell
    {scale : ℝ} (hscale : 0 < scale) (velocity : VelocityField) (t : ℝ) :
    enstrophyOn (parabolicCell scale) (parabolicVelocity scale velocity) t =
      scale * enstrophyOn unitCube velocity (scale ^ 2 * t) := by
  unfold enstrophyOn
  have hchange := Measure.setIntegral_comp_smul
    (volume : Measure Space)
    (fun x : Space ↦ ‖vorticityField velocity x (scale ^ 2 * t)‖ ^ 2)
    (parabolicCell scale) hscale.ne'
  rw [scale_smul_parabolicCell hscale.ne'] at hchange
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchange
  rw [show (fun x : Space ↦
      ‖vorticityField (parabolicVelocity scale velocity) x t‖ ^ 2) =
      fun x ↦ scale ^ 4 *
        ‖vorticityField velocity (scale • x) (scale ^ 2 * t)‖ ^ 2 by
          funext x
          exact norm_vorticityField_parabolicVelocity_sq scale velocity x t]
  rw [integral_const_mul, hchange, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hscale.le 3))]
  field_simp [hscale.ne']

/-- The derivative dissipation gains pointwise weight six and loses the three-dimensional cell
Jacobian, leaving weight three. -/
theorem vorticityDerivativeDissipationOn_parabolicCell
    {scale : ℝ} (hscale : 0 < scale) (velocity : VelocityField) (t : ℝ) :
    vorticityDerivativeDissipationOn (parabolicCell scale)
        (parabolicVelocity scale velocity) t =
      scale ^ 3 *
        vorticityDerivativeDissipationOn unitCube velocity (scale ^ 2 * t) := by
  unfold vorticityDerivativeDissipationOn
  let density : Space → ℝ := fun x ↦ ∑ direction : Fin 3,
    ‖gradient (fun y ↦ vorticityField velocity y (scale ^ 2 * t) direction) x‖ ^ 2
  have hchange := Measure.setIntegral_comp_smul
    (volume : Measure Space) density (parabolicCell scale) hscale.ne'
  rw [scale_smul_parabolicCell hscale.ne'] at hchange
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchange
  rw [show (fun x : Space ↦
      ∑ direction : Fin 3,
        ‖gradient
            (fun y ↦ vorticityField (parabolicVelocity scale velocity) y t direction) x‖ ^ 2) =
      fun x ↦ scale ^ 6 * density (scale • x) by
        funext x
        exact vorticityDerivativeDensity_parabolicVelocity velocity x t]
  rw [integral_const_mul, hchange, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hscale.le 3))]
  field_simp [hscale.ne']
  simp only [density]

/-- The fourth-power population gains pointwise weight eight and loses the transported-cell
Jacobian, leaving weight five. -/
theorem vorticityFourthPowerOn_parabolicCell
    {scale : ℝ} (hscale : 0 < scale) (velocity : VelocityField) (t : ℝ) :
    vorticityFourthPowerOn (parabolicCell scale)
        (parabolicVelocity scale velocity) t =
      scale ^ 5 * vorticityFourthPowerOn unitCube velocity (scale ^ 2 * t) := by
  unfold vorticityFourthPowerOn
  have hchange := Measure.setIntegral_comp_smul
    (volume : Measure Space)
    (fun x : Space ↦ ‖vorticityField velocity x (scale ^ 2 * t)‖ ^ 4)
    (parabolicCell scale) hscale.ne'
  rw [scale_smul_parabolicCell hscale.ne'] at hchange
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchange
  rw [show (fun x : Space ↦
      ‖vorticityField (parabolicVelocity scale velocity) x t‖ ^ 4) =
      fun x ↦ scale ^ 8 *
        ‖vorticityField velocity (scale • x) (scale ^ 2 * t)‖ ^ 4 by
          funext x
          exact norm_vorticityField_parabolicVelocity_fourth scale velocity x t]
  rw [integral_const_mul, hchange, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hscale.le 3))]
  field_simp [hscale.ne']

/-! ## The retained scale separator -/

/-- Along the genuine PDE-preserving scale family the quartic and dissipation receivers differ
by exactly two powers of scale.  The scale address is therefore a load-bearing predecessor of any
proposed absorption law. -/
theorem parabolic_quartic_dissipation_weight_difference : (5 : ℤ) - 3 = 2 := by
  norm_num

/-! ## The coefficient forced by two independent receiver actions -/

/-- Candidate powers for a monomial quartic estimate
`Q ≤ constant · Enstrophy^a · Dissipation^b`.  Amplitude transport and genuine parabolic
transport are independent equations, so both are retained. -/
structure QuarticAbsorptionExponents where
  enstrophyPower : ℚ
  dissipationPower : ℚ
  amplitudeBalance : 2 * enstrophyPower + 2 * dissipationPower = 4
  parabolicBalance : enstrophyPower + 3 * dissipationPower = 5

/-- The two exact receiver actions uniquely force the three-dimensional Gagliardo--Nirenberg
exponents: one half of enstrophy and three halves of dissipation. -/
theorem QuarticAbsorptionExponents.unique (weights : QuarticAbsorptionExponents) :
    weights.enstrophyPower = 1 / 2 ∧ weights.dissipationPower = 3 / 2 := by
  constructor <;> linarith [weights.amplitudeBalance, weights.parabolicBalance]

/-- After one dissipation factor is exposed for viscous absorption, the only monomial coefficient
compatible with both receiver actions has one half-power of enstrophy and one half-power of
dissipation. -/
theorem QuarticAbsorptionExponents.coefficientPowers (weights : QuarticAbsorptionExponents) :
    weights.enstrophyPower = 1 / 2 ∧ weights.dissipationPower - 1 = 1 / 2 := by
  obtain ⟨henstrophy, hdissipation⟩ := weights.unique
  constructor
  · exact henstrophy
  · rw [hdissipation]
    norm_num

theorem enstrophyOn_nonneg (cell : Set Space) (velocity : VelocityField) (t : ℝ) :
    0 ≤ enstrophyOn cell velocity t := by
  unfold enstrophyOn
  exact mul_nonneg (by norm_num)
    (integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _)))

theorem vorticityDerivativeDissipationOn_nonneg
    (cell : Set Space) (velocity : VelocityField) (t : ℝ) :
    0 ≤ vorticityDerivativeDissipationOn cell velocity t := by
  unfold vorticityDerivativeDissipationOn
  apply integral_nonneg_of_ae
  exact Filter.Eventually.of_forall fun x ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The exact weight-two coefficient selected by the exponent theorem, retained before any
Young inequality or scalar absorption aperture. -/
def scaleTwoVorticityCoefficientOn
    (cell : Set Space) (velocity : VelocityField) (t : ℝ) : ℝ :=
  Real.sqrt
    (enstrophyOn cell velocity t *
      vorticityDerivativeDissipationOn cell velocity t)

/-- The selected coefficient really carries the two missing parabolic weights on the transported
cell.  No numerical approximation or unit-erasing scalar cast occurs. -/
theorem scaleTwoVorticityCoefficientOn_parabolicCell
    {scale : ℝ} (hscale : 0 < scale) (velocity : VelocityField) (t : ℝ) :
    scaleTwoVorticityCoefficientOn (parabolicCell scale)
        (parabolicVelocity scale velocity) t =
      scale ^ 2 *
        scaleTwoVorticityCoefficientOn unitCube velocity (scale ^ 2 * t) := by
  unfold scaleTwoVorticityCoefficientOn
  rw [enstrophyOn_parabolicCell hscale,
    vorticityDerivativeDissipationOn_parabolicCell hscale]
  rw [show
      scale * enstrophyOn unitCube velocity (scale ^ 2 * t) *
          (scale ^ 3 *
            vorticityDerivativeDissipationOn unitCube velocity (scale ^ 2 * t)) =
        (scale ^ 2) ^ 2 *
          (enstrophyOn unitCube velocity (scale ^ 2 * t) *
            vorticityDerivativeDissipationOn unitCube velocity (scale ^ 2 * t)) by
      ring]
  rw [Real.sqrt_mul (sq_nonneg (scale ^ 2)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (sq_nonneg scale)]

/-- A quartic-to-dissipation absorption law is exactly covariant under the genuine parabolic
Navier--Stokes passage when its coefficient retains the missing two scale weights.  This is an
`iff`, not an estimate produced by rounding: the source inequality and its transported-cell
reading contain precisely the same information once the positive scale occurrence is retained. -/
theorem vorticityFourthPower_le_dissipation_parabolic_iff
    {scale coefficient : ℝ} (hscale : 0 < scale)
    (velocity : VelocityField) (t : ℝ) :
    vorticityFourthPowerOn (parabolicCell scale)
          (parabolicVelocity scale velocity) t ≤
        (scale ^ 2 * coefficient) *
          vorticityDerivativeDissipationOn (parabolicCell scale)
            (parabolicVelocity scale velocity) t ↔
      vorticityFourthPowerOn unitCube velocity (scale ^ 2 * t) ≤
        coefficient *
          vorticityDerivativeDissipationOn unitCube velocity (scale ^ 2 * t) := by
  rw [vorticityFourthPowerOn_parabolicCell hscale,
    vorticityDerivativeDissipationOn_parabolicCell hscale]
  rw [show
      (scale ^ 2 * coefficient) *
          (scale ^ 3 *
            vorticityDerivativeDissipationOn unitCube velocity (scale ^ 2 * t)) =
        scale ^ 5 *
          (coefficient *
            vorticityDerivativeDissipationOn unitCube velocity (scale ^ 2 * t)) by
      ring]
  exact mul_le_mul_iff_of_pos_left (pow_pos hscale 5)

section Audit

#print axioms vorticityField_parabolicVelocity
#print axioms fderiv_vorticityField_parabolicVelocity
#print axioms enstrophyOn_parabolicCell
#print axioms vorticityDerivativeDissipationOn_parabolicCell
#print axioms vorticityFourthPowerOn_parabolicCell
#print axioms vorticityFourthPower_le_dissipation_parabolic_iff
#print axioms QuarticAbsorptionExponents.unique
#print axioms scaleTwoVorticityCoefficientOn_parabolicCell

end Audit

end Soma.Holonics.Millennium.NavierStokesParabolicVorticityCurrent
