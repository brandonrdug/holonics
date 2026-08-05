import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Soma.Holonics.R27

def chartStatement : Prop := (∀ t u v : ℤ, v^2 - (u + (1))^5 + t*(u + (1)) - (1) = (v^2 + (-1 + 0*t)*u^5 + (-5 + 0*t)*u^4 + (-10 + 0*t)*u^3 + (-10 + 0*t)*u^2 + (-5 + 1*t)*u^1 + (-2 + 1*t)*u^0))
theorem generated_chart : chartStatement := by
  unfold chartStatement
  intro t u v; ring

def gaussianChartStatement : Prop := (∀ t u v : ℂ, (Complex.I*v)^2 - (-u)^5 + t*(-u) - 1 = -(v^2-u^5+t*u+1))
theorem generated_gaussian_chart : gaussianChartStatement := by
  unfold gaussianChartStatement
  intro t u v; rw [mul_pow, Complex.I_sq]; ring

def jacobianStatement : Prop := (∀ t x : ℤ, x*(t-5*x^4)+(x^5-t*x+1) = 1-4*x^5)
theorem generated_jacobian : jacobianStatement := by
  unfold jacobianStatement
  intro t x; ring

def bezoutStatement : Prop := (∀ t x : ℤ, ((3125*t^0)*x^0 + (2500*t^1)*x^1 + (2000*t^2)*x^2 + (1600*t^3)*x^3)*(x^5-t*x+1) + ((256*t^4)*x^0 + (-625*t^0)*x^1 + (-500*t^1)*x^2 + (-400*t^2)*x^3 + (-320*t^3)*x^4)*(5*x^4-t) = (3125*t^0 + -256*t^5))
theorem generated_bezout : bezoutStatement := by
  unfold bezoutStatement
  intro t x; ring

def reductionStatement_0 : Prop := (∀ t x : ℤ, ((320*t^4)*x^0 + (3125*t^0)*x^1 + (2500*t^1)*x^2 + (2000*t^2)*x^3)*(x^5-t*x+1) + ((320*t^3)*x^0 + (-64*t^4)*x^1 + (-625*t^0)*x^2 + (-500*t^1)*x^3 + (-400*t^2)*x^4)*(5*x^4-t) = (3125*t^0 + -256*t^5)*x^1)
theorem generated_reduction_0 : reductionStatement_0 := by
  unfold reductionStatement_0
  intro t x; ring

def reductionStatement_1 : Prop := (∀ t x : ℤ, ((400*t^3)*x^0 + (320*t^4)*x^1 + (3125*t^0)*x^2 + (2500*t^1)*x^3)*(x^5-t*x+1) + ((400*t^2)*x^0 + (-80*t^3)*x^1 + (-64*t^4)*x^2 + (-625*t^0)*x^3 + (-500*t^1)*x^4)*(5*x^4-t) = (3125*t^0 + -256*t^5)*x^2)
theorem generated_reduction_1 : reductionStatement_1 := by
  unfold reductionStatement_1
  intro t x; ring

def reductionStatement_2 : Prop := (∀ t x : ℤ, ((500*t^2)*x^0 + (400*t^3)*x^1 + (320*t^4)*x^2 + (3125*t^0)*x^3)*(x^5-t*x+1) + ((500*t^1)*x^0 + (-100*t^2)*x^1 + (-80*t^3)*x^2 + (-64*t^4)*x^3 + (-625*t^0)*x^4)*(5*x^4-t) = (3125*t^0 + -256*t^5)*x^3)
theorem generated_reduction_2 : reductionStatement_2 := by
  unfold reductionStatement_2
  intro t x; ring

def reductionStatement_3 : Prop := (∀ t x : ℤ, ((625*t^1)*x^0 + (500*t^2)*x^1 + (400*t^3)*x^2 + (320*t^4)*x^3)*(x^5-t*x+1) + ((625*t^0)*x^0 + (-125*t^1)*x^1 + (-100*t^2)*x^2 + (-80*t^3)*x^3 + (-64*t^4)*x^4)*(5*x^4-t) = (3125*t^0 + -256*t^5)*x^4)
theorem generated_reduction_3 : reductionStatement_3 := by
  unfold reductionStatement_3
  intro t x; ring

def scalarStatement : Prop := (∀ t z0 z1 z2 z3 z4 : ℤ, ((50000 + -4096*t^5)*z4 + -61440*t^4*z3 + -247680*t^3*z2 + -264000*t^2*z1 + -29601*t*z0) = 16*(3125*t^0 + -256*t^5)*z4 - 61440*t^4*z3 - 247680*t^3*z2 - 264000*t^2*z1 - 29601*t*z0)
theorem generated_scalar : scalarStatement := by
  unfold scalarStatement
  intro t z0 z1 z2 z3 z4; ring

def recurrenceStatement_0 : Prop := ((50000 : ℚ)*120*((9867 : ℚ) / 2000000) + (-61440 : ℚ)*0 + (-247680 : ℚ)*0 + (-264000 : ℚ)*0 + (-29601 : ℚ) = 0)
theorem generated_recurrence_0 : recurrenceStatement_0 := by
  unfold recurrenceStatement_0
  norm_num

def recurrenceStatement_1 : Prop := ((50000 : ℚ)*360*((97867 : ℚ) / 6000000) + (-61440 : ℚ)*0 + (-247680 : ℚ)*0 + (-264000 : ℚ)*1 + (-29601 : ℚ) = 0)
theorem generated_recurrence_1 : recurrenceStatement_1 := by
  unfold recurrenceStatement_1
  norm_num

def recurrenceStatement_2 : Prop := ((50000 : ℚ)*840*((50141 : ℚ) / 2000000) + (-61440 : ℚ)*0 + (-247680 : ℚ)*2 + (-264000 : ℚ)*2 + (-29601 : ℚ) = 0)
theorem generated_recurrence_2 : recurrenceStatement_2 := by
  unfold recurrenceStatement_2
  norm_num

def recurrenceStatement_3 : Prop := ((50000 : ℚ)*1680*((892107 : ℚ) / 28000000) + (-61440 : ℚ)*6 + (-247680 : ℚ)*6 + (-264000 : ℚ)*3 + (-29601 : ℚ) = 0)
theorem generated_recurrence_3 : recurrenceStatement_3 := by
  unfold recurrenceStatement_3
  norm_num

def finiteIndicialStatement : Prop := (∀ r : ℤ, ((0*r^0 + 0*r^1 + 2*r^2 + -3*r^3 + 1*r^4) = r^2*(r-1)*(r-2)))
theorem generated_finite_indicial : finiteIndicialStatement := by
  unfold finiteIndicialStatement
  intro r; ring

def infinityIndicialStatement : Prop := (∀ r : ℤ, ((29601*r^0 + 114624*r^1 + 108416*r^2 + 36864*r^3 + 4096*r^4) = (8*r+3)*(8*r+13)*(8*r+23)*(8*r+33)))
theorem generated_infinity_indicial : infinityIndicialStatement := by
  unfold infinityIndicialStatement
  intro r; ring

def residueStatement : Prop := (∀ a : ℚ, 4*a^5=1 → (((-3 : ℚ) / 40)*a^0) ≠ 0 ∧ ((((-3 : ℚ) / 40)*a^0)*a^0 + (((-1 : ℚ) / 10)*a^4)*a^1 + (((1 : ℚ) / 10)*a^3)*a^2 + (((3 : ℚ) / 10)*a^2)*a^3) = 0)
theorem generated_residue_witness : residueStatement := by
  unfold residueStatement
  intro a h; constructor
  · norm_num
  · nlinarith [h]

def separationStatement : Prop := ((195400 : ℕ) ≠ 195401 ∧ (3125 : ℤ) ≠ 50000 ∧ ((9867 : ℚ) / 2000000) ≠ ((9867 : ℚ) / 32000000))
theorem generated_separation : separationStatement := by
  unfold separationStatement
  norm_num

theorem generated_expression_geometry : chartStatement ∧ gaussianChartStatement ∧ jacobianStatement ∧ bezoutStatement ∧ reductionStatement_0 ∧ reductionStatement_1 ∧ reductionStatement_2 ∧ reductionStatement_3 ∧ scalarStatement ∧ recurrenceStatement_0 ∧ recurrenceStatement_1 ∧ recurrenceStatement_2 ∧ recurrenceStatement_3 ∧ finiteIndicialStatement ∧ infinityIndicialStatement ∧ residueStatement ∧ separationStatement := by
  exact ⟨generated_chart, generated_gaussian_chart, generated_jacobian, generated_bezout, generated_reduction_0, generated_reduction_1, generated_reduction_2, generated_reduction_3, generated_scalar, generated_recurrence_0, generated_recurrence_1, generated_recurrence_2, generated_recurrence_3, generated_finite_indicial, generated_infinity_indicial, generated_residue_witness, generated_separation⟩

end Soma.Holonics.R27

#check Soma.Holonics.R27.generated_expression_geometry
