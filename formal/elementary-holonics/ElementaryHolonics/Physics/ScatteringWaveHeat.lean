import Mathlib
import Mathlib.Tactic

/-!
# Power-normalized two-port scattering and attenuation

This file records a finite transmission-channel law.  The matrix
`R(a,b) = [[a,-b],[b,a]]` acts on two complex ports; when `a²+b²=1` it is a
real orthogonal rotation and preserves the summed complex `normSq` power.  An
attenuation factor `d` leaves `(1-d²)` of the incoming power in an explicit
heat receiver.  No continuum, relativistic, or quantum interpretation is
claimed here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicComplexParametron

abbrev ComplexPorts := ℂ × ℂ

/-- The real two-port scattering rotation, acting on complex channel values. -/
def scattering (a b : ℝ) (ports : ComplexPorts) : ComplexPorts :=
  ((a : ℂ) * ports.1 - (b : ℂ) * ports.2,
    (b : ℂ) * ports.1 + (a : ℂ) * ports.2)

/-- Summed incoming complex-port power in the finite channel chart. -/
def portPower (ports : ComplexPorts) : ℝ :=
  Complex.normSq ports.1 + Complex.normSq ports.2

theorem scattering_power
    (a b : ℝ) (ports : ComplexPorts) (hunit : a ^ 2 + b ^ 2 = 1) :
    portPower (scattering a b ports) = portPower ports := by
  unfold portPower scattering
  simp [Complex.normSq_apply]
  ring_nf at hunit ⊢
  nlinarith

/-- Attenuation leaves the complementary fraction of incoming power as heat. -/
def attenuationHeat (d : ℝ) (ports : ComplexPorts) : ℝ :=
  (1 - d ^ 2) * portPower ports

/-- The transmitted power plus explicit attenuation heat equals input power. -/
theorem attenuation_power_heat
    (d : ℝ) (ports : ComplexPorts) :
    d ^ 2 * portPower ports + attenuationHeat d ports = portPower ports := by
  unfold attenuationHeat
  ring

/-- With `0 ≤ d ≤ 1`, the attenuation heat receiver is nonnegative. -/
theorem attenuationHeat_nonneg
    (d : ℝ) (ports : ComplexPorts) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    0 ≤ attenuationHeat d ports := by
  unfold attenuationHeat portPower
  have hfactor : 0 ≤ 1 - d ^ 2 := by nlinarith
  have hpower : 0 ≤ Complex.normSq ports.1 + Complex.normSq ports.2 :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact mul_nonneg hfactor hpower

end Soma.Holonics.Millennium.HolonicComplexParametron
