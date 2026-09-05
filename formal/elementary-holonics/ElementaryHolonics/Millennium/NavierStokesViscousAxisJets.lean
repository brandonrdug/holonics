import Mathlib.Tactic

/-!
# The first viscous axis receivers require a shape current

The full finite Euler recurrence returns these exact coefficients of its first radial swirl
correction. They fix the constant and quadratic axis diffusion receivers. Varying only the
swirl amplitude cannot pay both when amplitude and viscosity are positive. A separate shape
current can pay the two displayed receivers. Source attachment is the finite recurrence;
no complete time-dependent fluid solution or pressure continuation is asserted here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesViscousAxisJets

def firstSwirlConstant (X : ℝ) : ℝ := -5 / 14 * X - 35 / 8

def firstSwirlQuadratic (X : ℝ) : ℝ := 15 / 16 * X + 3885 / 416

def axisDiffusionConstant (a : ℝ) : ℝ := a * (8 * firstSwirlConstant (a ^ 2) - 5 / 2)

def axisDiffusionQuadratic (a : ℝ) : ℝ := a * (8 * firstSwirlQuadratic (a ^ 2) + 135 / 8)

def shapeMismatch (X : ℝ) : ℝ := 55 / 14 * X + 2325 / 52

theorem axis_diffusion_constant (a : ℝ) :
    axisDiffusionConstant a = -a * (20 / 7 * a ^ 2 + 75 / 2) := by
  unfold axisDiffusionConstant firstSwirlConstant
  ring

theorem axis_diffusion_mismatch (a : ℝ) :
    axisDiffusionQuadratic a + 5 / 4 * axisDiffusionConstant a = a * shapeMismatch (a ^ 2) := by
  unfold axisDiffusionQuadratic axisDiffusionConstant firstSwirlConstant firstSwirlQuadratic shapeMismatch
  ring

theorem shapeMismatch_positive (a : ℝ) : 0 < shapeMismatch (a ^ 2) := by
  unfold shapeMismatch
  positivity

/-- The two equations are the constant and z^2 receivers of an amplitude-only axis current. -/
theorem amplitude_only_axis_rows_incompatible {a mu : ℝ} (ha : 0 < a) (hmu : 0 < mu)
    (aRate : ℝ) :
    ¬ (aRate = mu * axisDiffusionConstant a ∧
      -(5 / 4) * aRate = mu * axisDiffusionQuadratic a) := by
  rintro ⟨h0, h2⟩
  have hpositive : 0 < mu * (a * shapeMismatch (a ^ 2)) :=
    mul_pos hmu (mul_pos ha (shapeMismatch_positive a))
  rw [← axis_diffusion_mismatch a] at hpositive
  nlinarith

def amplitudeCurrent (a mu : ℝ) : ℝ := mu * axisDiffusionConstant a

def shapeCurrent (a mu : ℝ) : ℝ := mu * shapeMismatch (a ^ 2)

/-- A second coefficient current pays the first two axis receivers while keeping the complete
higher-axis and pressure residuals outside this finite statement. -/
theorem two_axis_currents_repair (a mu : ℝ) :
    amplitudeCurrent a mu = mu * axisDiffusionConstant a ∧
      -(5 / 4) * amplitudeCurrent a mu + a * shapeCurrent a mu =
        mu * axisDiffusionQuadratic a := by
  refine ⟨rfl, ?_⟩
  have h := axis_diffusion_mismatch a
  unfold amplitudeCurrent shapeCurrent
  linear_combination -mu * h

theorem two_axis_current_signs {a mu : ℝ} (ha : 0 < a) (hmu : 0 < mu) :
    amplitudeCurrent a mu < 0 ∧ 0 < shapeCurrent a mu := by
  constructor
  · rw [amplitudeCurrent, axis_diffusion_constant]
    have hp : 0 < (20 / 7 : ℝ) * a ^ 2 + 75 / 2 := by positivity
    exact mul_neg_of_pos_of_neg hmu (mul_neg_of_neg_of_pos (neg_neg_of_pos ha) hp)
  · exact mul_pos hmu (shapeMismatch_positive a)

#print axioms axis_diffusion_mismatch
#print axioms amplitude_only_axis_rows_incompatible
#print axioms two_axis_currents_repair
#print axioms two_axis_current_signs

end Soma.Holonics.Millennium.NavierStokesViscousAxisJets
