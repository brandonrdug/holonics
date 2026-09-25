import Holonics.Geometry.HolonicTorusKnots
import Mathlib.Tactic

/-!
# Compactified momentum/winding and its physical spectral receiver

[definition] This source chart interprets the existing integral two-torus lift as a pair of
momentum and winding charges of a closed-string circle sector. Radius has length units;
alphaPrime has length-squared units. With hbar = c = 1, massSquared and oscillatorOffset have
inverse-length-squared units. The oscillator/level-matching sector is retained separately.
Source: David Tong, String Theory, section 8.2--8.3, equations (8.5)--(8.10).

[proved-derived] Radius inversion with charge exchange preserves this spectrum and the charge
product, fixes the left mover and reflects the right mover. A finite modulo-four phase quotient
does not determine the physical mass receiver. These are circle-sector consequences with an
explicit source map, not an identification of every torus slope with a physical string state.
-/

noncomputable section
namespace Holonics.Physics.CompactifiedModeTransport

open Holonics.Geometry.HolonicTorusKnots

/-- Integral charges in the same carrier as the existing addressed torus lift. -/
abbrev Charges := Fin 2 → ℤ

def exchange (charge : Charges) : Charges := ![charge 1, charge 0]

theorem exchange_involutive (charge : Charges) : exchange (exchange charge) = charge := by
  funext i
  fin_cases i <;> rfl

/-- The topological lift and the charge reader share the actual integer coordinates. -/
theorem charge_from_lift (charge : Charges) (i : Fin 2) :
    torusSlopeLift charge 1 i - torusSlopeLift charge 0 i = (charge i : ℝ) :=
  torusSlopeLift_endpoint_displacement charge i

def dualRadius (alphaPrime radius : ℝ) : ℝ := alphaPrime / radius

def leftMover (alphaPrime radius : ℝ) (charge : Charges) : ℝ :=
  (charge 0 : ℝ) / radius + (charge 1 : ℝ) * radius / alphaPrime

def rightMover (alphaPrime radius : ℝ) (charge : Charges) : ℝ :=
  (charge 0 : ℝ) / radius - (charge 1 : ℝ) * radius / alphaPrime

def massSquared (alphaPrime radius oscillatorOffset : ℝ) (charge : Charges) : ℝ :=
  ((charge 0 : ℝ) / radius)^2 + ((charge 1 : ℝ) * radius / alphaPrime)^2 + oscillatorOffset

theorem dualRadius_involutive {alphaPrime radius : ℝ}
    (ha : alphaPrime ≠ 0) : dualRadius alphaPrime (dualRadius alphaPrime radius) = radius := by
  unfold dualRadius
  field_simp

theorem leftMover_dual {alphaPrime radius : ℝ} (ha : alphaPrime ≠ 0)
    (hr : radius ≠ 0) (charge : Charges) :
    leftMover alphaPrime (dualRadius alphaPrime radius) (exchange charge) =
      leftMover alphaPrime radius charge := by
  simp [leftMover, dualRadius, exchange]
  field_simp
  ring

theorem rightMover_dual {alphaPrime radius : ℝ} (ha : alphaPrime ≠ 0)
    (hr : radius ≠ 0) (charge : Charges) :
    rightMover alphaPrime (dualRadius alphaPrime radius) (exchange charge) =
      -rightMover alphaPrime radius charge := by
  simp [rightMover, dualRadius, exchange]
  field_simp

theorem massSquared_eq_mover_pair (alphaPrime radius oscillatorOffset : ℝ) (charge : Charges) :
    massSquared alphaPrime radius oscillatorOffset charge =
      (leftMover alphaPrime radius charge ^ 2 + rightMover alphaPrime radius charge ^ 2) / 2 +
        oscillatorOffset := by
  unfold massSquared leftMover rightMover
  ring

theorem massSquared_dual {alphaPrime radius : ℝ} (ha : alphaPrime ≠ 0)
    (hr : radius ≠ 0) (oscillatorOffset : ℝ) (charge : Charges) :
    massSquared alphaPrime (dualRadius alphaPrime radius) oscillatorOffset (exchange charge) =
      massSquared alphaPrime radius oscillatorOffset charge := by
  rw [massSquared_eq_mover_pair, leftMover_dual ha hr, rightMover_dual ha hr,
    massSquared_eq_mover_pair]
  ring

/-- The momentum/winding product in the retained level-matching constraint is preserved. -/
theorem levelMatching_dual (charge : Charges) :
    exchange charge 0 * exchange charge 1 = charge 0 * charge 1 := by
  simp [exchange, mul_comm]

theorem massSquared_ge_offset (alphaPrime radius oscillatorOffset : ℝ) (charge : Charges) :
    oscillatorOffset ≤ massSquared alphaPrime radius oscillatorOffset charge := by
  unfold massSquared
  nlinarith [sq_nonneg ((charge 0 : ℝ) / radius),
    sq_nonneg ((charge 1 : ℝ) * radius / alphaPrime)]

/-- A concrete spectral obstruction to replacing integer winding by a finite phase code.
At unit radius/alphaPrime and zero oscillator offset, charges (0,0) and (0,4) share the
modulo-four face, but their mass squares are 0 and 16. -/
theorem finite_phase_loses_mass :
    slopeModuloFour (![0, 0] : Charges) = slopeModuloFour (![0, 4] : Charges) ∧
      massSquared 1 1 0 (![0, 0] : Charges) = 0 ∧
      massSquared 1 1 0 (![0, 4] : Charges) = 16 := by
  constructor
  · funext i
    fin_cases i <;> decide
  · norm_num [massSquared]

/-! ## A cyclic compact direction returns a gauge-coupled reduced action

The supplied local metric block has vertical kinetic term B(v + C)^2/2, where C is
the connection evaluated on the retained horizontal velocity. Routh reduction fixes the
conjugate momentum q and eliminates v. It leaves q C in the horizontal action, together
with the compact kinetic potential q^2/(2B); a changing B cannot be silently discarded.
-/

def cyclicLagrangian (baseL scale vertical connection : ℝ) : ℝ :=
  baseL + scale / 2 * (vertical + connection)^2

def cyclicMomentum (scale vertical connection : ℝ) : ℝ :=
  scale * (vertical + connection)

/-- The linear coefficient in an exact velocity change is the conjugate momentum. -/
theorem cyclicLagrangian_velocity_increment (baseL scale vertical connection delta : ℝ) :
    cyclicLagrangian baseL scale (vertical + delta) connection -
      cyclicLagrangian baseL scale vertical connection =
      cyclicMomentum scale vertical connection * delta + scale / 2 * delta^2 := by
  unfold cyclicLagrangian cyclicMomentum
  ring

theorem fixedMomentum_velocity {scale : ℝ} (hs : scale ≠ 0) (charge connection : ℝ) :
    cyclicMomentum scale (charge / scale - connection) connection = charge := by
  unfold cyclicMomentum
  field_simp
  ring

/-- Eliminating the compact velocity retains both gauge coupling and compact energy. -/
theorem cyclic_routh_reduction {scale : ℝ} (hs : scale ≠ 0)
    (baseL charge connection : ℝ) :
    cyclicLagrangian baseL scale (charge / scale - connection) connection -
      charge * (charge / scale - connection) =
      baseL + charge * connection - charge^2 / (2 * scale) := by
  unfold cyclicLagrangian
  field_simp
  ring

end Holonics.Physics.CompactifiedModeTransport
