import Holonics.Physics.CompositeMassEnergy
import Holonics.Compression.Landmark.FixedPoint
import Holonics.Aeon.Clock.Reading

/-!
# The boost as an aeon clock transport: the Doppler ratio, dilation as a rate, the twin

[definition] Rebuild step 6, K4 (#75, the Lorentz scope of its comment); null-cone record
(2026-09-24) §1. A receiver's clock is the observer covector `ω_R = −U_μ dx^μ`, and elapsed time on
an aeon is the pairing `t_R(Δ) = ⟨ω_R | Δ⟩ = −⟨U, Δ⟩` (`clockReading`). In the light-cone chart
`u = t − x`, `v = t + x` (`LightCone`, `ofTX`), the Minkowski pairing is `⟨a, b⟩ = −(a_u b_v + a_v b_u)/2`
(`pairing`) and the boost is the undivided Doppler pair `(u, v) ↦ (ku, k⁻¹v)` (`boost`).

[proved-derived; formal-checked] Over any field of characteristic zero, exactly:

* **The boost is a ratio.** It preserves the pairing (`boost_pairing`) and the interval `uv`
  (`boost_interval`); collinear composition multiplies the Doppler ratios, `k₁₂ = k₁k₂`
  (`boost_mul`). In the `(t, x)` chart it is `t′ = γt − γβx`, `x′ = γx − γβt` with
  `γ = (k + k⁻¹)/2`, `γβ = (k − k⁻¹)/2` (`boost_tx`), on the hyperbola `γ² − (γβ)² = 1` of the
  owner `CompositeMassEnergy.multiplicativeScale_lorentz_identity`, and it is the owner's
  `CompositeMassEnergy.unitBoost` read in the light-cone chart (`unitBoost_lightCone`). No logarithm
  is taken: rapidity `log k` is the ratio's additive chart.
* **Velocity addition is the landmark owner's.** The velocity `β(k) = (k² − 1)/(k² + 1)` lies in the
  open cone (`abs_betaOf_lt_one`) and its Doppler chart `D(β) = (1 + β)/(1 − β)` is `k²`
  (`doppler_betaOf`), so the product of ratios is the velocity addition of
  `Compression/Landmark/FixedPoint.vadd`, derived from `doppler_vadd` (`velocity_addition`).
* **Time dilation is a clock ratio.** The receiver of Doppler ratio `k` has the unit velocity
  `U(k) = (k⁻¹, k)` (`receiverVelocity_unit`); its clock reads its own aeon as proper time
  (`clockReading_self`), and reads the aeon `τU(k₂)` of another receiver as `τ γ(k₁/k₂)`
  (`time_dilation`): the Lorentz law of cosines `t_R/t_R′ = −⟨U, U′⟩ = γ`, a function of the relative
  Doppler ratio only. A boost carries `U(k′)` to `U(k′/k)` (`boost_receiverVelocity`), and it is a
  clock transport: the boosted receiver reads the boosted aeon as the receiver read the aeon,
  `t_{ΛU}(ΛΔ) = t_U(Δ)` (`clockReading_boost`).
* **The rate of the aeon clocks.** On the event complex (`events`: occurrences are events, and
  each ordered pair of events is a passage), each receiver has one inertial clock, the owner's exact
  clock of its potential `φ_R(x) = −⟨U, x⟩` (`Aeon/Clock/Reading.exactClock`, `inertialClock`), which
  reads every aeon; the owner's rate of two receivers on the aeon `0 → τU(k₂)` is the undivided pair
  `(τγ(k₁/k₂) : τ)` (`dilation_is_rate`). The one-passage complex `segment` carries the clocks of
  `NonClosedClock.redshift_rate`.
* **The twin.** The traveller who leaves along `U(k)` and returns along `U(k⁻¹)`, each for proper
  time `τ`, arrives with the stay-at-home interval `(2γτ)²` (`twin_interval`), and `γ > 1` for
  `k ≠ 1` (`one_lt_gammaOf`). In general the proper time `√(uv)` of future-directed displacements is
  superadditive, the reverse triangle inequality (`properTime_reverse_triangle`).

[proved-standard] The Lorentz boost, the Doppler factor and the twin asymmetry are standard; the
reading of the boost as a rate of aeon clocks is the record's `[interpretation]`, made exact here.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.Boost

/-! ## 1. The light-cone chart and the boost -/

/-- [definition] **A displacement in the light-cone chart**: `u = t − x`, `v = t + x`. -/
@[ext] structure LightCone (K : Type*) where
  u : K
  v : K

section Chart

variable {K : Type*} [Field K]

/-- [definition] The displacement of `(t, x)`. -/
def ofTX (t x : K) : LightCone K := ⟨t - x, t + x⟩

/-- [definition] The time face `t = (u + v)/2`. -/
def time (e : LightCone K) : K := (e.u + e.v) / 2

/-- [definition] The space face `x = (v − u)/2`. -/
def space (e : LightCone K) : K := (e.v - e.u) / 2

/-- [definition] The interval `uv = t² − x²`. -/
def interval (e : LightCone K) : K := e.u * e.v

/-- [definition] **The Minkowski pairing** `⟨a, b⟩ = −a_t b_t + a_x b_x = −(a_u b_v + a_v b_u)/2`. -/
def pairing (a b : LightCone K) : K := -(a.u * b.v + a.v * b.u) / 2

/-- [definition] Displacements add. -/
instance : Add (LightCone K) := ⟨fun a b => ⟨a.u + b.u, a.v + b.v⟩⟩

/-- [definition] The displacement scaled by `τ`. -/
def scale (τ : K) (e : LightCone K) : LightCone K := ⟨τ * e.u, τ * e.v⟩

/-- [definition] **The boost** of Doppler ratio `k`: `(u, v) ↦ (ku, k⁻¹v)`. -/
def boost (k : K) (e : LightCone K) : LightCone K := ⟨k * e.u, k⁻¹ * e.v⟩

/-- [definition] `γ = (k + k⁻¹)/2`. -/
def gammaOf (k : K) : K := (k + k⁻¹) / 2

/-- [definition] `γβ = (k − k⁻¹)/2`. -/
def gammaBetaOf (k : K) : K := (k - k⁻¹) / 2

/-- [definition] The velocity `β = γβ/γ = (k² − 1)/(k² + 1)`. -/
def betaOf (k : K) : K := (k ^ 2 - 1) / (k ^ 2 + 1)

variable [CharZero K]

theorem ofTX_time (t x : K) : time (ofTX t x) = t := by
  simp [ofTX, time]

theorem ofTX_space (t x : K) : space (ofTX t x) = x := by
  simp [ofTX, space]

/-- [proved-derived; formal-checked] The self-pairing is minus the interval. -/
theorem pairing_self (e : LightCone K) : pairing e e = -interval e := by
  simp [pairing, interval]; ring

/-- [proved-derived; formal-checked] In the `(t, x)` chart the pairing is `−t_a t_b + x_a x_b`. -/
theorem pairing_ofTX (t x t' x' : K) :
    pairing (ofTX t x) (ofTX t' x') = -(t * t') + x * x' := by
  simp [pairing, ofTX]; ring

/-- [proved-derived; formal-checked] **The boost preserves the pairing.** -/
theorem boost_pairing {k : K} (hk : k ≠ 0) (a b : LightCone K) :
    pairing (boost k a) (boost k b) = pairing a b := by
  simp only [pairing, boost]
  field_simp

omit [CharZero K] in
/-- [proved-derived; formal-checked] The boost preserves the interval. -/
theorem boost_interval {k : K} (hk : k ≠ 0) (e : LightCone K) :
    interval (boost k e) = interval e := by
  simp only [interval, boost]
  field_simp

omit [CharZero K] in
/-- [proved-derived; formal-checked] **Collinear composition multiplies the Doppler ratios.** -/
theorem boost_mul (k₁ k₂ : K) (e : LightCone K) :
    boost k₁ (boost k₂ e) = boost (k₁ * k₂) e := by
  ext <;> simp [boost, mul_inv_rev] <;> ring

omit [CharZero K] in
theorem boost_one (e : LightCone K) : boost 1 e = e := by
  ext <;> simp [boost]

/-- [proved-derived; formal-checked] **The boost in the `(t, x)` chart**: `t′ = γt − γβx`,
`x′ = γx − γβt`. -/
theorem boost_tx {k : K} (hk : k ≠ 0) (t x : K) :
    time (boost k (ofTX t x)) = gammaOf k * t - gammaBetaOf k * x ∧
      space (boost k (ofTX t x)) = gammaOf k * x - gammaBetaOf k * t := by
  constructor <;> simp only [time, space, boost, ofTX, gammaOf, gammaBetaOf] <;> field_simp <;> ring

omit [CharZero K] in
/-- [proved-derived; formal-checked] `γ(k⁻¹) = γ(k)`: dilation does not see the direction. -/
theorem gammaOf_inv (k : K) : gammaOf k⁻¹ = gammaOf k := by
  simp [gammaOf, add_comm]

/-! ## 2. The receiver's clock and time dilation -/

/-- [definition] **The unit velocity** of the receiver of Doppler ratio `k`: `U(k) = (k⁻¹, k)`,
i.e. `(γ, γβ)` in the `(t, x)` chart. -/
def receiverVelocity (k : K) : LightCone K := ⟨k⁻¹, k⟩

/-- [definition] **The receiver's clock reading** `t_R(Δ) = ⟨ω_R | Δ⟩ = −⟨U, Δ⟩`. -/
def clockReading (U Δ : LightCone K) : K := -pairing U Δ

/-- [proved-derived; formal-checked] `U(k)` is a unit timelike velocity, `⟨U, U⟩ = −1`. -/
theorem receiverVelocity_unit {k : K} (hk : k ≠ 0) :
    pairing (receiverVelocity k) (receiverVelocity k) = -1 := by
  simp only [pairing, receiverVelocity]
  field_simp
  ring

/-- [proved-derived; formal-checked] `U(k) = (γ, γβ)` in the `(t, x)` chart. -/
theorem receiverVelocity_tx (k : K) :
    time (receiverVelocity k) = gammaOf k ∧ space (receiverVelocity k) = gammaBetaOf k := by
  constructor
  · unfold time receiverVelocity gammaOf; ring
  · unfold space receiverVelocity gammaBetaOf; ring

/-- [proved-derived; formal-checked] **A receiver's clock reads its own aeon as proper time.** -/
theorem clockReading_self {k : K} (hk : k ≠ 0) (τ : K) :
    clockReading (receiverVelocity k) (scale τ (receiverVelocity k)) = τ := by
  simp only [clockReading, pairing, receiverVelocity, scale]
  field_simp
  ring

/-- [proved-derived; formal-checked] **Time dilation is the Lorentz law of cosines**: the clock of
`U(k₁)` reads the aeon `τU(k₂)` as `τ γ(k₁/k₂)`, which depends on the relative Doppler ratio only. -/
theorem time_dilation {k₁ k₂ : K} (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0) (τ : K) :
    clockReading (receiverVelocity k₁) (scale τ (receiverVelocity k₂)) =
      τ * gammaOf (k₁ / k₂) := by
  simp only [clockReading, pairing, receiverVelocity, scale, gammaOf]
  field_simp
  ring

omit [CharZero K] in
/-- [proved-derived; formal-checked] A boost carries the receiver `U(k′)` to `U(k′/k)`. -/
theorem boost_receiverVelocity (k k' : K) :
    boost k (receiverVelocity k') = receiverVelocity (k' / k) := by
  ext <;> simp [boost, receiverVelocity, div_eq_mul_inv, mul_comm]

/-- [proved-derived; formal-checked] **The boost is a clock transport**: the boosted receiver reads
the boosted displacement as the receiver read the displacement, `t_{ΛU}(ΛΔ) = t_U(Δ)`
(`boost_pairing`). -/
theorem clockReading_boost {k : K} (hk : k ≠ 0) (U Δ : LightCone K) :
    clockReading (boost k U) (boost k Δ) = clockReading U Δ := by
  rw [clockReading, clockReading, boost_pairing hk]

/-! ## 3. The twin -/

/-- [proved-derived; formal-checked] **The twin's aeons.** Out along `U(k)` and back along `U(k⁻¹)`,
each for proper time `τ`, the traveller's displacement is the stay-at-home aeon of interval
`(2γτ)²`. -/
theorem twin_interval {k : K} (hk : k ≠ 0) (τ : K) :
    interval (scale τ (receiverVelocity k) + scale τ (receiverVelocity k⁻¹)) =
      (2 * gammaOf k * τ) ^ 2 := by
  change (τ * k⁻¹ + τ * k⁻¹⁻¹) * (τ * k + τ * k⁻¹) = _
  simp only [inv_inv, gammaOf]
  field_simp
  ring

end Chart

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-derived; formal-checked] **The stay-at-home twin ages more**: `γ > 1` for a positive
Doppler ratio `k ≠ 1`. -/
theorem one_lt_gammaOf {k : K} (hk : 0 < k) (hk1 : k ≠ 1) : 1 < gammaOf k := by
  unfold gammaOf
  have hsq : 0 < (k - 1) ^ 2 := by
    have : k - 1 ≠ 0 := sub_ne_zero.mpr hk1
    positivity
  rw [lt_div_iff₀ (by norm_num : (0 : K) < 2)]
  have : k + k⁻¹ - 2 = (k - 1) ^ 2 / k := by field_simp; ring
  have hpos : 0 < (k - 1) ^ 2 / k := div_pos hsq hk
  linarith

end Ordered

/-! ## Velocity addition through the landmark owner's Doppler chart -/

section Velocity

open Holonics.Compression.Landmark.FixedPoint

/-- [proved-derived; formal-checked] A positive Doppler ratio's velocity lies in the open cone. -/
theorem abs_betaOf_lt_one {k : ℚ} (hk : 0 < k) : |betaOf k| < 1 := by
  unfold betaOf
  have hA : 0 < k ^ 2 + 1 := by positivity
  rw [abs_lt, lt_div_iff₀ hA, div_lt_iff₀ hA]
  constructor <;> nlinarith [sq_nonneg k, pow_pos hk 2]

/-- [proved-derived; formal-checked] **The Doppler chart of the velocity is the squared ratio**:
`D(β(k)) = (1 + β)/(1 − β) = k²`. -/
theorem doppler_betaOf {k : ℚ} (hk : k ≠ 0) : doppler (betaOf k) = k ^ 2 := by
  unfold doppler betaOf
  have hA : k ^ 2 + 1 ≠ 0 := by positivity
  have hB : 1 - (k ^ 2 - 1) / (k ^ 2 + 1) ≠ 0 := by
    rw [one_sub_div hA]; exact div_ne_zero (by ring_nf; norm_num) hA
  rw [div_eq_iff hB]
  field_simp
  ring

/-- [proved-derived; formal-checked] **Velocity addition is the product of Doppler ratios**, read
through the landmark owner: `D(β(k₁k₂)) = k₁²k₂² = D(β₁)D(β₂) = D(vadd β₂ β₁)` (`doppler_vadd`), and
the Doppler chart determines the velocity in the cone (`one_sub_eq_doppler`), so
`β(k₁k₂) = (β₁ + β₂)/(1 + β₁β₂)`. -/
theorem velocity_addition {k₁ k₂ : ℚ} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    betaOf (k₁ * k₂) = vadd (betaOf k₂) (betaOf k₁) := by
  have hb₁ := abs_betaOf_lt_one h₁
  have hb₂ := abs_betaOf_lt_one h₂
  have hb₁₂ := abs_betaOf_lt_one (mul_pos h₁ h₂)
  have hD : doppler (betaOf (k₁ * k₂)) = doppler (vadd (betaOf k₂) (betaOf k₁)) := by
    rw [doppler_vadd hb₁ hb₂, doppler_betaOf (mul_pos h₁ h₂).ne', doppler_betaOf h₁.ne',
      doppler_betaOf h₂.ne']
    ring
  have h := one_sub_eq_doppler hb₁₂
  rw [hD, ← one_sub_eq_doppler (vadd_mem hb₁ hb₂)] at h
  linarith

end Velocity

/-- [proved-derived; formal-checked] **The boost is the owner's `unitBoost` in the light-cone
chart**: with `β = (k − k⁻¹)/(k + k⁻¹)` and `γ = (k + k⁻¹)/2`, `E′ − p′ = k(E − p)` and
`E′ + p′ = k⁻¹(E + p)`. -/
theorem unitBoost_lightCone {k : ℝ} (hk : 0 < k)
    (P : Holonics.Physics.HolonicMassShellFace.FourMomentum) :
    (Holonics.Physics.CompositeMassEnergy.unitBoost ((k - k⁻¹) / (k + k⁻¹)) ((k + k⁻¹) / 2) P).energy -
        (Holonics.Physics.CompositeMassEnergy.unitBoost ((k - k⁻¹) / (k + k⁻¹)) ((k + k⁻¹) / 2)
          P).momentum 0 = k * (P.energy - P.momentum 0) ∧
      (Holonics.Physics.CompositeMassEnergy.unitBoost ((k - k⁻¹) / (k + k⁻¹)) ((k + k⁻¹) / 2)
          P).energy +
        (Holonics.Physics.CompositeMassEnergy.unitBoost ((k - k⁻¹) / (k + k⁻¹)) ((k + k⁻¹) / 2)
          P).momentum 0 = k⁻¹ * (P.energy + P.momentum 0) := by
  have hsum : k + k⁻¹ ≠ 0 := by positivity
  constructor <;>
    simp only [Holonics.Physics.CompositeMassEnergy.unitBoost, Matrix.cons_val_zero] <;>
    field_simp <;> ring

/-- [proved-derived; formal-checked] **The reverse triangle inequality**: the proper time `√(uv)` of
future-directed displacements is superadditive, `√(u₁v₁) + √(u₂v₂) ≤ √((u₁ + u₂)(v₁ + v₂))`. -/
theorem properTime_reverse_triangle {u₁ v₁ u₂ v₂ : ℝ} (hu₁ : 0 ≤ u₁) (hv₁ : 0 ≤ v₁) (hu₂ : 0 ≤ u₂)
    (hv₂ : 0 ≤ v₂) :
    Real.sqrt (u₁ * v₁) + Real.sqrt (u₂ * v₂) ≤ Real.sqrt ((u₁ + u₂) * (v₁ + v₂)) := by
  apply Real.le_sqrt_of_sq_le
  have ha := Real.sq_sqrt (mul_nonneg hu₁ hv₁)
  have hb := Real.sq_sqrt (mul_nonneg hu₂ hv₂)
  have hab : Real.sqrt (u₁ * v₁) * Real.sqrt (u₂ * v₂) =
      Real.sqrt (u₁ * v₂) * Real.sqrt (u₂ * v₁) := by
    rw [← Real.sqrt_mul (mul_nonneg hu₁ hv₁), ← Real.sqrt_mul (mul_nonneg hu₁ hv₂)]
    congr 1
    ring
  have hc := Real.sq_sqrt (mul_nonneg hu₁ hv₂)
  have hd := Real.sq_sqrt (mul_nonneg hu₂ hv₁)
  nlinarith [sq_nonneg (Real.sqrt (u₁ * v₂) - Real.sqrt (u₂ * v₁))]

/-! ## 4. The rate of two inertial aeon clocks -/

section Rate

open Holonics.Aeon.Clock.Groupoid
open Holonics.Aeon.Clock.Reading

/-- [definition] **One passage between two occurrences**, `0 → 1`, no two-cell: the carrier of two
static clocks read on one coordinate interval (`NonClosedClock.redshift_rate`). -/
def segment : ParametricComplex (Fin 2) Unit Empty where
  src _ := 0
  tgt _ := 1
  base := Empty.elim
  boundary := Empty.elim

theorem segment_wellFormed : segment.WellFormed := fun f => f.elim

/-- [definition] The aeon along the passage. -/
def along : Aeon segment 0 1 := ⟨[((), true)], by simp [ParametricComplex.Chained,
  ParametricComplex.start, ParametricComplex.finish, segment]⟩

/-- [definition] **The event complex**: its occurrences are the events of the light-cone chart and
each ordered pair of events `(x, y)` is a passage `x → y`; no two-cell. -/
def events : ParametricComplex (LightCone ℚ) (LightCone ℚ × LightCone ℚ) Empty where
  src e := e.1
  tgt e := e.2
  base := Empty.elim
  boundary := Empty.elim

theorem events_wellFormed : events.WellFormed := fun f => f.elim

/-- [definition] The aeon along the passage from the event `x` to the event `y`. -/
def passage (x y : LightCone ℚ) : Aeon events x y := ⟨[((x, y), true)], by simp [
  ParametricComplex.Chained, ParametricComplex.start, ParametricComplex.finish, events]⟩

/-- [definition] **The inertial clock** of the receiver `U(k)`: the owner's exact clock of its
potential `φ_R(x) = −⟨U, x⟩` on the event complex (`Aeon/Clock/Reading.exactClock`). One clock per
receiver; it reads every aeon. -/
def inertialClock (k : ℚ) : Clock events ℚ :=
  exactClock events_wellFormed fun x => clockReading (receiverVelocity k) x

/-- [proved-derived; formal-checked] The inertial clock reads an aeon by its endpoints:
`t_R(γ) = t_R(y) − t_R(x)`, the pairing with the displacement (`reading_exactClock`). -/
theorem inertialClock_reading (k : ℚ) {x y : LightCone ℚ} (γ : Aeon events x y) :
    reading (inertialClock k) γ = clockReading (receiverVelocity k) y -
      clockReading (receiverVelocity k) x :=
  reading_exactClock events_wellFormed _ γ

/-- [proved-derived; formal-checked] **Dilation is the rate of two aeon clocks.** The owner's rate
of the receivers `U(k₁)` and `U(k₂)` on the aeon `0 → τU(k₂)` is the undivided pair
`(τγ(k₁/k₂) : τ)`. -/
theorem dilation_is_rate {k₁ k₂ : ℚ} (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0) (τ : ℚ) :
    rate (inertialClock k₁) (inertialClock k₂) (passage ⟨0, 0⟩ (scale τ (receiverVelocity k₂))) =
      ⟨τ * gammaOf (k₁ / k₂), τ⟩ := by
  have hzero : ∀ k : ℚ, clockReading (receiverVelocity k) ⟨0, 0⟩ = 0 := fun k => by
    simp [clockReading, pairing]
  simp only [rate, inertialClock_reading, hzero, sub_zero, time_dilation h₁ h₂,
    clockReading_self h₂]

end Rate

section Audit

#print axioms boost_pairing
#print axioms boost_interval
#print axioms boost_mul
#print axioms boost_tx
#print axioms receiverVelocity_unit
#print axioms clockReading_self
#print axioms time_dilation
#print axioms boost_receiverVelocity
#print axioms clockReading_boost
#print axioms twin_interval
#print axioms one_lt_gammaOf
#print axioms abs_betaOf_lt_one
#print axioms doppler_betaOf
#print axioms velocity_addition
#print axioms unitBoost_lightCone
#print axioms properTime_reverse_triangle
#print axioms inertialClock_reading
#print axioms dilation_is_rate

end Audit

end Holonics.Physics.Spacetime.Boost
