import Holonics.Physics.PhaseCarrier
import Holonics.Geometry.PhaseCarry
import Holonics.Geometry.HolonicClockedPantographicSwing
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Holon.Navigator: lifted phases, lossless clock jumps and carries

[definition] The navigator facet `G`: a lifted phase `θ̃` with its counted winding `n`; the
**clock jump** at a section crossing advances `θ̃` by a full turn and `n` by one, leaving the chart
phase `θ̃ − 2πn` unchanged.

[proved-derived; formal-checked] The jump is lossless for every storage read through the phase
carrier and for the parametron pump storage (`jump_lossless`, composing
`PhaseCarrier.phaseCarrier_fullTurn_fibre`); it carries winding (`jump_carries_winding`). Jump
counts are carries and compose as a cocycle (`jumps_are_carries`: `PhaseCarry.winding_add`,
`carry_cocycle`, `carry_le_one`), and a `RationalClockPassage` jumps losslessly: the target
carrier at the accumulated phase equals its carrier at the retained residue
(`clockPassage_jumps_lossless`, via `denominator_mul_targetTicks_add_phaseResidue`).

[proved-derived; formal-checked] **A closing navigator's transport is a finite-order port map**
(`Transport::Map`, rebuild step 4 addition 1): a permutation `σ` of a finite port chart has a
positive order (`map_order_pos`), its powers read only the tick's class modulo that order
(`map_pow_mod_order`), so a full turn is lossless and the winding is the lift's alone
(`map_turn_lossless`, the map's face of `jump_lossless`); two maps compose to a map of positive
order (`map_compose_order_pos`), which for commuting maps divides the least common multiple of
their orders (`map_compose_order_dvd`). The rotor `(· + 1)` on `ℤ/d` has order exactly `d`
(`mapRotor_order`, with `mapRotor_pow`): a Cayley image has no eigenvalue `−1`, so an even period is
not a flow's Cayley step, and the map is carried as itself.
-/

noncomputable section

namespace Holonics.HolonCore

open Holonics.Physics.HolonicParametron
open Holonics.Geometry.PhaseCarry
open Holonics.Geometry.HolonicClockedPantographicSwing

/-! ## 1. A lifted phase and its lossless jump -/

/-- [definition] A navigator's lifted phase `θ̃` with the winding `n` it has counted. -/
structure LiftedPhase where
  θ : ℝ
  n : ℤ

/-- [definition] The chart phase `θ̃ − 2πn` read on the circle. -/
def LiftedPhase.chart (p : LiftedPhase) : ℝ := p.θ - 2 * Real.pi * p.n

/-- [definition] **The clock jump** at a section crossing: the phase advances a full turn and the
winding counts it. -/
def LiftedPhase.jump (p : LiftedPhase) : LiftedPhase := ⟨p.θ + 2 * Real.pi, p.n + 1⟩

theorem phaseCarrier_add_int_turns (θ : ℝ) (k : ℤ) :
    phaseCarrier (θ + 2 * Real.pi * k) = phaseCarrier θ := by
  unfold phaseCarrier
  rw [show (((θ + 2 * Real.pi * k : ℝ) : ℂ) * Complex.I) =
      (θ : ℂ) * Complex.I + k * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- [proved-derived; formal-checked] **The jump is lossless for every carrier storage.** Any storage
read through the phase carrier `e^{iθ}` is unchanged by the jump (`phaseCarrier_fullTurn_fibre`),
and so is the parametron's pump storage. -/
theorem jump_lossless (storage : ℂ → ℝ) (p : LiftedPhase) (strength pumpPhase : ℝ) :
    storage (phaseCarrier p.jump.θ) = storage (phaseCarrier p.θ) ∧
      pumpStorage strength pumpPhase p.jump.θ = pumpStorage strength pumpPhase p.θ := by
  refine ⟨by rw [LiftedPhase.jump, phaseCarrier_fullTurn_fibre], ?_⟩
  unfold pumpStorage LiftedPhase.jump
  rw [show 2 * (p.θ + 2 * Real.pi) - pumpPhase =
      ((2 * p.θ - pumpPhase) + 2 * Real.pi) + 2 * Real.pi by ring,
    Real.cos_add_two_pi, Real.cos_add_two_pi]

/-- [proved-derived; formal-checked] **The jump carries winding.** The winding increases by one,
the chart phase is unchanged, and the lifted state is new: the storage forgets what the lift
retains. -/
theorem jump_carries_winding (p : LiftedPhase) :
    p.jump.n = p.n + 1 ∧ p.jump.chart = p.chart ∧ p.jump ≠ p := by
  refine ⟨rfl, by simp [LiftedPhase.jump, LiftedPhase.chart]; ring, fun h => ?_⟩
  have := congrArg LiftedPhase.n h
  simp [LiftedPhase.jump] at this

/-! ## 2. Jumps are carries, and carries are a cocycle -/

/-- [proved-derived; formal-checked] **Jump counts compose as a cocycle.** On a ring of period `n`,
advancing `a` then `b` makes `carry n a b` section crossings beyond the separate windings
(`PhaseCarry.winding_add`), and the crossings of three consecutive advances are associative
(`PhaseCarry.carry_cocycle`). Each crossing is one lossless jump. -/
theorem jumps_are_carries (n a b c : ℕ) (hn : 0 < n) :
    winding n (a + b) = winding n a + winding n b + carry n a b ∧
      carry n a b + carry n (a + b) c = carry n b c + carry n a (b + c) ∧
      carry n a b ≤ 1 :=
  ⟨winding_add n a b hn, carry_cocycle n a b c hn, carry_le_one n a b hn⟩

/-- [proved-derived; formal-checked] **A rational clock passage jumps losslessly.** The target
ring's carrier at the accumulated phase equals its carrier at the retained residue: the
`targetTicks` completed crossings are jumps the storage cannot see, retained as winding by
`RationalClockPassage.denominator_mul_targetTicks_add_phaseResidue`. -/
theorem clockPassage_jumps_lossless {ClockAddress : Type*}
    (passage : RationalClockPassage ClockAddress) (r s : ℕ) :
    phaseCarrier (2 * Real.pi * ((r + passage.numerator * s : ℕ) : ℝ) / passage.denominator) =
      phaseCarrier (2 * Real.pi * (passage.phaseResidue r s : ℝ) / passage.denominator) := by
  have h := passage.denominator_mul_targetTicks_add_phaseResidue r s
  have hd : (passage.denominator : ℝ) ≠ 0 := by exact_mod_cast passage.denominator_pos.ne'
  rw [← h]
  push_cast
  rw [show 2 * Real.pi * ((passage.denominator : ℝ) * passage.targetTicks r s +
      passage.phaseResidue r s) / passage.denominator =
      2 * Real.pi * (passage.phaseResidue r s : ℝ) / passage.denominator +
        2 * Real.pi * ((passage.targetTicks r s : ℤ) : ℝ) by push_cast; field_simp; ring]
  exact phaseCarrier_add_int_turns _ _

/-! ## 3. A closing navigator: a finite-order port map -/

section Map

variable {α : Type*}

/-- [proved-derived; formal-checked] **A finite-order map reads only the tick's class**: its `n`-th
power is its power at `n` modulo its order. -/
theorem map_pow_mod_order (σ : Equiv.Perm α) (n : ℕ) : σ ^ n = σ ^ (n % orderOf σ) :=
  (pow_mod_orderOf σ n).symm

/-- [proved-derived; formal-checked] **A full turn of a finite-order map is lossless**: advancing
`w` whole turns of the order moves nothing, so the winding is carried by the lift alone. -/
theorem map_turn_lossless (σ : Equiv.Perm α) (r w : ℕ) : σ ^ (r + orderOf σ * w) = σ ^ r := by
  rw [pow_add, pow_mul, pow_orderOf_eq_one, one_pow, mul_one]

/-- [proved-derived; formal-checked] **A map of commuting finite-order maps**: the composite's order
divides the least common multiple of the two orders. -/
theorem map_compose_order_dvd (σ τ : Equiv.Perm α) (h : Commute σ τ) :
    orderOf (σ * τ) ∣ Nat.lcm (orderOf σ) (orderOf τ) :=
  h.orderOf_mul_dvd_lcm

variable [Finite α]

/-- [proved-derived; formal-checked] A permutation of a finite port chart has a positive order. -/
theorem map_order_pos (σ : Equiv.Perm α) : 0 < orderOf σ := orderOf_pos σ

/-- [proved-derived; formal-checked] **Two maps compose to a map**: the composite of two
permutations of a finite port chart is again of positive order. -/
theorem map_compose_order_pos (σ τ : Equiv.Perm α) : 0 < orderOf (σ * τ) := orderOf_pos _

end Map

/-- [proved-derived; formal-checked] The rotor's powers are the additions on `ℤ/d`. -/
theorem mapRotor_pow (d k : ℕ) :
    (Equiv.addRight (1 : ZMod d)) ^ k = Equiv.addRight (k : ZMod d) := by
  induction k with
  | zero => ext x; simp
  | succ k ih =>
      ext x
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      simp only [Equiv.coe_addRight, Nat.cast_succ]
      ring

/-- [proved-derived; formal-checked] **The rotor of period `d` has order exactly `d`**: the closing
ring's navigator returns after `d` ticks and not before. -/
theorem mapRotor_order (d : ℕ) [NeZero d] : orderOf (Equiv.addRight (1 : ZMod d)) = d := by
  rw [orderOf_eq_iff (NeZero.pos d)]
  refine ⟨?_, ?_⟩
  · rw [mapRotor_pow]; ext x; simp
  · intro m hm hm0 h
    have := congrArg (fun f : Equiv.Perm (ZMod d) => f 0) h
    simp at this
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd hm0 this) (not_le.mpr hm)

end Holonics.HolonCore
