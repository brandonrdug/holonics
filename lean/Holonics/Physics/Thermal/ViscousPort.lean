import Holonics.Physics.Thermal.Exchange
import Holonics.Physics.Fluid.ControlVolume

/-!
# The viscous-work port: the fluid cell joined to the thermal cell

[definition] Rebuild step 6, K3 (#74), battle tests 3 and 5; plan §3.6 ("viscous/contact work can
enter internal heat without creating or destroying total stress-energy"). The fluid instance
returns, per cell, the work its viscous stress does against the deformation,
`W = V (τ : G) = V (2μ |Def u|² + λ (tr G)²)` (`Physics/Fluid/ControlVolume.viscousHeat`), which is
nonnegative for `μ ≥ 0`, `nλ + 2μ ≥ 0` (`dissipation_nonneg`). The port is the admitted power
`W ≥ 0` entering a cell's internal energy (`ViscousWork`), and **the fluid produces it**:
`ViscousWork.ofFluid` builds the port's work from `viscousHeat` with its admission from
`dissipation_nonneg`. Rust: `holonics::physics::fluid::control_volume::ViscousHeat`, produced by
`ControlVolume::cell_return` and consumed by `holonics::physics::thermal::exchange`.

[proved-derived; formal-checked] What is proved.

1. **The port is joined to the fluid cell** (`cell_port_join`, composing
   `ControlVolume.cell_heat_port`): on the unit cell under a uniform Newtonian stress and an affine
   field, the traction power read face by face less the pressure work is the power of
   `ViscousWork.ofFluid`.
2. **Energy across the joined port, by construction of the updates** (`port_first_law`, exact over
   `ℚ`): when the fluid's mechanical energy is debited over a tick by the traction power less the
   pressure work, and the thermal cell receives `ofFluid` through `Exchange.next₁` while exchanging
   heat with a second cell, mechanical plus internal energy is unchanged. The updates are defined
   to balance; the content is item 1, that the debited and the credited power are the same
   quantity. The kinetic-energy change of an actual tick of the momentum balance is not computed
   here (#62, `ControlVolume`'s open time advance).
3. **The port's production rate** is `W/T`, nonnegative and zero exactly without work
   (`port_production_nonneg`, `port_production_eq_zero_iff`).
4. **The tick's entropy is enclosed by exact Clausius readings**: `hW · C/U' ≤ C log(U'/U) ≤
   hW · C/U`, `U' = U + hW` (`port_entropy_enclosure`, from `Exchange.cell_entropy_enclosure`), so
   it is nonnegative (`port_entropy_nonneg`) and positive when work enters
   (`port_entropy_pos`).

[counterexample; formal-checked] **The admission `W ≥ 0` is load-bearing**: a port that withdrew
work (`W = −1` from `U = 2`, `C = 1`, `h = 1`) would lower the entropy by `log 2`
(`withdrawn_work_lowers_entropy`); that is not viscous heating but a reversible or active
exchange, which this port does not admit.

No `axiom`, no `sorry`.
-/

namespace Holonics.Physics.Thermal.ViscousPort

open Holonics.Physics.Thermal.Exchange
open Holonics.Physics.Fluid.Cells Holonics.Physics.Fluid.ControlVolume

/-- [definition] **The admitted viscous work** entering a cell: a power `W ≥ 0`. -/
structure ViscousWork where
  power : ℚ
  admitted : 0 ≤ power

/-- [definition] **The viscous work a fluid cell hands to the port**: its viscous heat
`V (τ : G)`, admitted by `dissipation_nonneg` (`μ ≥ 0`, `nλ + 2μ ≥ 0`) and `V ≥ 0`. -/
def ViscousWork.ofFluid {n : ℕ} (μ lam V : ℚ) (G : Matrix (Fin n) (Fin n) ℚ) (hμ : 0 ≤ μ)
    (hb : 0 ≤ n * lam + 2 * μ) (hV : 0 ≤ V) : ViscousWork :=
  ⟨viscousHeat μ lam V G, mul_nonneg hV (dissipation_nonneg hμ hb G)⟩

/-- [proved-derived; formal-checked] **The port is joined to the fluid cell**: the unit cell's
traction power under a uniform Newtonian stress, read face by face, less the pressure work, is the
power of the viscous work the fluid hands to the port (`ControlVolume.cell_heat_port`). -/
theorem cell_port_join {n : ℕ} (p μ lam : ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ)
    (v : Point n) (hμ : 0 ≤ μ) (hb : 0 ≤ n * lam + 2 * μ) :
    faceRead (tractionPowerFlux (stress p μ lam G) u₀ G) (faces (v, Finset.univ)) -
        (-p * Matrix.trace G) =
      (ViscousWork.ofFluid μ lam 1 G hμ hb zero_le_one).power :=
  cell_heat_port p μ lam u₀ G v

/-- [proved-derived; formal-checked] **Energy across the joined port, by construction of the
updates.** Over a tick `h`, the fluid's mechanical energy `K` is debited by the traction power less
the pressure work, read face by face on the unit cell; cell 1 receives the fluid's viscous work
through `Exchange.next₁` and exchanges heat with cell 2. Mechanical plus internal energy is
unchanged. The updates are defined to balance; the join `cell_port_join` is what makes the debit
and the credit one quantity. -/
theorem port_first_law {n : ℕ} (p μ lam : ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ)
    (v : Point n) (hμ : 0 ≤ μ) (hb : 0 ≤ n * lam + 2 * μ) (κ h C₁ U₁ C₂ U₂ K : ℚ) :
    (K - h * (faceRead (tractionPowerFlux (stress p μ lam G) u₀ G) (faces (v, Finset.univ)) -
        (-p * Matrix.trace G))) +
      next₁ κ h C₁ U₁ C₂ U₂ (ViscousWork.ofFluid μ lam 1 G hμ hb zero_le_one).power +
      next₂ κ h C₁ U₁ C₂ U₂ 0 = K + U₁ + U₂ := by
  rw [cell_port_join p μ lam u₀ G v hμ hb]
  unfold next₁ next₂
  ring

/-- [definition] **The production rate of the port** at temperature `T`: `W/T`. -/
def portProduction (w : ViscousWork) (T : ℚ) : ℚ := w.power / T

theorem port_production_nonneg (w : ViscousWork) {T : ℚ} (hT : 0 < T) :
    0 ≤ portProduction w T :=
  div_nonneg w.admitted hT.le

/-- [proved-derived; formal-checked] The port produces entropy exactly when work enters. -/
theorem port_production_eq_zero_iff (w : ViscousWork) {T : ℚ} (hT : 0 < T) :
    portProduction w T = 0 ↔ w.power = 0 := by
  unfold portProduction
  rw [div_eq_zero_iff, or_iff_left hT.ne']

/-- [proved-derived; formal-checked] **The tick's entropy at the port is enclosed** by the
Clausius readings at the end and at the start of the tick. -/
theorem port_entropy_enclosure (w : ViscousWork) {C U h : ℝ} (hC : 0 ≤ C) (hU : 0 < U)
    (hh : 0 ≤ h) :
    h * w.power * (C / (U + h * w.power)) ≤ C * Real.log ((U + h * w.power) / U) ∧
      C * Real.log ((U + h * w.power) / U) ≤ h * w.power * (C / U) := by
  have hW : (0 : ℝ) ≤ w.power := by exact_mod_cast w.admitted
  have hU' : 0 < U + h * w.power := by positivity
  have := cell_entropy_enclosure hC hU hU'
  simp only [add_sub_cancel_left] at this
  exact this

/-- [proved-derived; formal-checked] **Admitted viscous work never lowers the entropy.** -/
theorem port_entropy_nonneg (w : ViscousWork) {C U h : ℝ} (hC : 0 ≤ C) (hU : 0 < U)
    (hh : 0 ≤ h) : 0 ≤ C * Real.log ((U + h * w.power) / U) := by
  have hW : (0 : ℝ) ≤ w.power := by exact_mod_cast w.admitted
  have hU' : 0 < U + h * w.power := by positivity
  have := (port_entropy_enclosure w hC hU hh).1
  have : 0 ≤ h * w.power * (C / (U + h * w.power)) := by positivity
  linarith

/-- [proved-derived; formal-checked] **Work entering a cell of positive capacity raises its
entropy strictly.** -/
theorem port_entropy_pos (w : ViscousWork) {C U h : ℝ} (hC : 0 < C) (hU : 0 < U) (hh : 0 < h)
    (hW : 0 < w.power) : 0 < C * Real.log ((U + h * w.power) / U) := by
  have hW' : (0 : ℝ) < w.power := by exact_mod_cast hW
  have hU' : 0 < U + h * w.power := by positivity
  have := (port_entropy_enclosure w hC.le hU hh.le).1
  have : 0 < h * w.power * (C / (U + h * w.power)) := by positivity
  linarith

/-- [counterexample; formal-checked] **Withdrawn work would lower the entropy**: `U = 2`, `C = 1`,
`h = 1`, `W = −1` gives `C log(U'/U) = log(1/2) = −log 2 < 0`. -/
theorem withdrawn_work_lowers_entropy :
    (1 : ℝ) * Real.log ((2 + 1 * (-1)) / 2) = -Real.log 2 ∧ -Real.log 2 < 0 := by
  refine ⟨?_, neg_neg_of_pos (Real.log_pos (by norm_num))⟩
  rw [show ((2 : ℝ) + 1 * (-1)) / 2 = 2⁻¹ by norm_num, Real.log_inv, one_mul]

section Audit

#print axioms cell_port_join
#print axioms port_first_law
#print axioms port_production_eq_zero_iff
#print axioms port_entropy_enclosure
#print axioms port_entropy_pos
#print axioms withdrawn_work_lowers_entropy

end Audit

end Holonics.Physics.Thermal.ViscousPort
