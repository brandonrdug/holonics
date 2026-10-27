import Holonics.Physics.Spacetime.Boost
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# The moving mirror: a reflection is a passage, two mirrors make a boost, and a receding wall
keeps `ωL`

The record `research/records/2026-10-25_A_REFLECTION_IS_A_PASSAGE_THE_INVOLUTION_IS_ITS_ENDPOINT_A_MOVING_MIRROR_STRETCHES_THE_RETURN_AND_TWO_MIRRORS_MAKE_A_BOOST.md`
(§§2–5) reads a reflection as a passage whose endpoint is the involution. This file proves the
box that record leaves in #410, beside `Physics/Spacetime/Boost` and in its light-cone chart
`u = t − x`, `v = t + x`, where `boost k (u, v) = (ku, k⁻¹v)` and the receiver of Doppler ratio
`k` has velocity `U(k) = (k⁻¹, k)`.

[proved-derived; formal-checked] What is proved.

1. **The mirror at rest in the frame of `U(k)`** is `R_k (u, v) = (v / k², k² u)` (`mirror`):
   boost to the mirror's frame, swap the two light directions, boost back (`mirror_eq_conj`); at
   rest it is the swap (`mirror_one`). It is an involution (`mirror_mirror`), keeps the interval
   and the pairing (`mirror_interval`, `mirror_pairing`), fixes the mirror's worldline `τ U(k)`
   (`mirror_worldline`, `mirror_receiverVelocity`), keeps the future cone (`mirror_future`) and
   swaps its two null axes (`mirror_null_axes`). Back in space, forward in time.
2. **The pivot sits at the mirror's rapidity** (`mirror_ratio`): the null ratios of an event and
   its image multiply to `k⁴`, `(v′/u′)(v/u) = k⁴`, the half-turn `S_a x = 2a − x` of the log-null
   chart with its grip at `log k²`, read without a logarithm.
3. **Two mirrors make a boost** (`mirror_mul`): `R_k₂ R_k₁ = boost ((k₁ / k₂)²)`.
4. **The return lands stretched** (`stretch_on_worldline`, `doppler_of_betaOf`): the phase `ω u`
   of a right-moving wave read on the mirror's worldline is `(ω / k²) v`, and
   `1 / k² = (1 − β) / (1 + β)` with `β = (k² − 1) / (k² + 1)`.
5. **The radar echo returns at `k² t₁`** (`radar_echo`, `radar_echo_tx`): the ray sent from
   `x = 0` at `t₁` meets the mirror's worldline at proper time `k t₁`, where `v = k² t₁`, so the
   return reaches `x = 0` at `t₂ = k² t₁` (Bondi).
6. **A box with one receding wall keeps `ωL`** (`departure`, `bounce_on_wall`, `boxLength_succ`,
   `boxLength_pow`, `wall_reading`, `freq_mul_length`): with a wall fixed at `x = 0` and one at
   `x = L₀ + βt`, each bounce is an event on the wall, `L_(n+1) = L_n (1 + β) / (1 − β)`, the
   frequency read on the wall falls by `(1 − β) / (1 + β)` at each bounce, so `ω_n L_n = ω_0 L_0`,
   bounce by bounce, for any `β` with `1 ± β ≠ 0` (over ℚ, any `|β| < 1`).
7. **The reactive wall returns everything, late** (`reactive_norm`, `reactive_logDeriv`,
   `reactiveWall_normSq`, `reactiveWall_hasDerivAt`, `reactiveWall_logDeriv`): over any field
   with `i² = −1` (so over `ℚ(i)`), `Γ = (ix − 1)/(ix + 1)` times its conjugate is `1` and its
   pole terms sum to `−2i/(1 + x²)`; over `ℂ`, `|Γ|² = 1` and `Γ⁻¹ dΓ/dx = −2i/(1 + x²)` as a
   derivative in the real `x`, and with `x = ωL/Z₀` the delay `|Im Γ⁻¹ dΓ/dω| = (2L/Z₀)/(1 + x²)`
   (`reactiveWall_delay`).

The computational object is the helical pair interaction: a mirror is a contact whose return is a
half-turn about a moving grip, and the boost is the stretch that grip's motion adds. Of the winding
guide's six general objects this touches the pair (the contact's return) and faces and placement
(the light-cone chart and its pivot); the helix, the cell holonomy, the tube and the tower thread
stay attached.

Consumers: the atlas rows `lorentz.moving-mirror` and `wave.reactive-wall-delay`, and the
record's Owed list.
-/

namespace Holonics.Physics.Spacetime.MovingMirror

open Holonics.Physics.Spacetime.Boost

/-! ## 1. The mirror -/

section Mirror

variable {K : Type*} [Field K]

/-- [definition] **The mirror at rest in the frame of `U(k)`**: `R_k (u, v) = (v / k², k² u)`. -/
def mirror (k : K) (e : LightCone K) : LightCone K := ⟨e.v / k ^ 2, k ^ 2 * e.u⟩

/-- [proved-derived; formal-checked] The mirror at rest swaps the two light directions. -/
theorem mirror_one (e : LightCone K) : mirror 1 e = ⟨e.v, e.u⟩ := by
  ext <;> simp [mirror]

/-- [proved-derived; formal-checked] **Boost, swap, boost back**:
`R_k = boost k⁻¹ ∘ R_1 ∘ boost k`. -/
theorem mirror_eq_conj {k : K} (hk : k ≠ 0) (e : LightCone K) :
    mirror k e = boost k⁻¹ (mirror 1 (boost k e)) := by
  ext <;> simp only [mirror, boost, one_pow, div_one, one_mul, inv_inv] <;>
    first | (field_simp <;> ring) | ring

/-- [proved-derived; formal-checked] **The mirror is an involution.** -/
theorem mirror_mirror {k : K} (hk : k ≠ 0) (e : LightCone K) : mirror k (mirror k e) = e := by
  ext <;> simp only [mirror] <;> field_simp <;> ring

/-- [proved-derived; formal-checked] The mirror keeps the interval `uv`. -/
theorem mirror_interval {k : K} (hk : k ≠ 0) (e : LightCone K) :
    interval (mirror k e) = interval e := by
  simp only [interval, mirror]
  field_simp <;> ring

/-- [proved-derived; formal-checked] **The mirror keeps the pairing**: it is an isometry of the
interval. -/
theorem mirror_pairing {k : K} (hk : k ≠ 0) (a b : LightCone K) :
    pairing (mirror k a) (mirror k b) = pairing a b := by
  simp only [pairing, mirror]
  field_simp <;> ring

/-- [proved-derived; formal-checked] **The mirror fixes its own worldline** `τ U(k)`. -/
theorem mirror_worldline {k : K} (hk : k ≠ 0) (τ : K) :
    mirror k (scale τ (receiverVelocity k)) = scale τ (receiverVelocity k) := by
  ext <;> simp only [mirror, scale, receiverVelocity] <;> field_simp <;> ring

/-- [proved-derived; formal-checked] The mirror fixes `U(k)`. -/
theorem mirror_receiverVelocity {k : K} (hk : k ≠ 0) :
    mirror k (receiverVelocity k) = receiverVelocity k := by
  ext <;> simp only [mirror, receiverVelocity] <;> field_simp <;> ring

/-- [proved-derived; formal-checked] **The mirror swaps the two null axes**:
`R_k (1, 0) = (0, k²)` and `R_k (0, 1) = (k⁻², 0)`. -/
theorem mirror_null_axes (k : K) :
    mirror k ⟨1, 0⟩ = ⟨0, k ^ 2⟩ ∧ mirror k ⟨0, 1⟩ = ⟨1 / k ^ 2, 0⟩ := by
  constructor <;> ext <;> simp [mirror]

/-- [proved-derived; formal-checked] **The pivot sits at the mirror's rapidity**: the null ratios
of an event and its image multiply to `k⁴`, `v′ v = k⁴ u′ u`. In the log-null chart this is the
reflection of `log (v/u)` about `2 log k`. -/
theorem mirror_ratio {k : K} (hk : k ≠ 0) (e : LightCone K) :
    (mirror k e).v * e.v = k ^ 4 * ((mirror k e).u * e.u) := by
  simp only [mirror]
  field_simp <;> ring

/-- [proved-derived; formal-checked] **Two mirrors make a boost**:
`R_k₂ R_k₁ = boost ((k₁/k₂)²)`. -/
theorem mirror_mul {k₁ k₂ : K} (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0) (e : LightCone K) :
    mirror k₂ (mirror k₁ e) = boost ((k₁ / k₂) ^ 2) e := by
  ext <;> simp only [mirror, boost] <;> field_simp <;> ring

/-- [proved-derived; formal-checked] **The return lands stretched**: the phase `ω u` of a
right-moving wave, read on the mirror's worldline, is `(ω / k²) v`, a left-moving wave of
frequency `ω / k²`. -/
theorem stretch_on_worldline {k : K} (hk : k ≠ 0) (ω τ : K) :
    ω * (scale τ (receiverVelocity k)).u = ω / k ^ 2 * (scale τ (receiverVelocity k)).v := by
  simp only [scale, receiverVelocity]
  field_simp <;> ring

/-- [proved-derived; formal-checked] **The radar echo returns at `k² t₁`** (Bondi). The ray sent
from `x = 0` at `t₁` keeps `u = t₁`; it meets the mirror's worldline at proper time `k t₁`; there
`v = k² t₁`, which the returning ray keeps, so it reaches `x = 0` at `t₂ = k² t₁`. -/
theorem radar_echo {k : K} (hk : k ≠ 0) (t₁ : K) :
    (scale (k * t₁) (receiverVelocity k)).u = (ofTX t₁ 0).u ∧
      (scale (k * t₁) (receiverVelocity k)).v = (ofTX (k ^ 2 * t₁) 0).v := by
  constructor
  · simp only [scale, receiverVelocity, ofTX, sub_zero]
    rw [mul_right_comm, mul_inv_cancel₀ hk, one_mul]
  · simp only [scale, receiverVelocity, ofTX, add_zero]
    ring

variable [CharZero K]

/-- [proved-derived; formal-checked] **The stretch in the velocity chart**: with
`β = (k² − 1)/(k² + 1)`, `(1 + β)/(1 − β) = k²`. -/
theorem doppler_of_betaOf {k : K} (hk : k ≠ 0) (h1 : k ^ 2 + 1 ≠ 0) :
    (1 + betaOf k) / (1 - betaOf k) = k ^ 2 := by
  have hm : (1 : K) - betaOf k = 2 / (k ^ 2 + 1) := by
    unfold betaOf
    field_simp <;> ring
  have hp : (1 : K) + betaOf k = 2 * k ^ 2 / (k ^ 2 + 1) := by
    unfold betaOf
    field_simp <;> ring
  rw [hm, hp, div_div_div_cancel_right₀ h1]
  ring

/-- [proved-derived; formal-checked] **The radar echo in the `(t, x)` chart**: the mirror
`x = βt` meets the ray `x = t − t₁` at `t_m = t₁ (k² + 1)/2`, `x_m = t₁ (k² − 1)/2`, and the return
reaches `x = 0` at `t_m + x_m = k² t₁`. -/
theorem radar_echo_tx {k : K} (h1 : k ^ 2 + 1 ≠ 0) (t₁ : K) :
    t₁ * (k ^ 2 - 1) / 2 = betaOf k * (t₁ * (k ^ 2 + 1) / 2) ∧
      t₁ * (k ^ 2 - 1) / 2 = t₁ * (k ^ 2 + 1) / 2 - t₁ ∧
      t₁ * (k ^ 2 + 1) / 2 + t₁ * (k ^ 2 - 1) / 2 = k ^ 2 * t₁ := by
  refine ⟨?_, by ring, by ring⟩
  unfold betaOf
  field_simp <;> ring

end Mirror

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-derived; formal-checked] **The mirror keeps the future cone**: an event with `u, v > 0`
returns with `u, v > 0`. A mirror never sends anything into the past. -/
theorem mirror_future {k : K} (hk : k ≠ 0) {e : LightCone K} (hu : 0 < e.u) (hv : 0 < e.v) :
    0 < (mirror k e).u ∧ 0 < (mirror k e).v := by
  have hk2 : 0 < k ^ 2 := by positivity
  exact ⟨div_pos hv hk2, mul_pos hk2 hu⟩

end Ordered

/-! ## 2. The box with one receding wall -/

section Box

variable {K : Type*} [Field K]

/-- [definition] **The departures from the fixed wall**: a right-moving ray leaving `x = 0` at
time `s` (so `u = s`) meets the wall `x = L₀ + βt` and returns to `x = 0` at time
`((1 + β) s + 2 L₀) / (1 − β)`, where it leaves again at once. -/
def departure (β L₀ s₀ : K) : ℕ → K
  | 0 => s₀
  | n + 1 => ((1 + β) * departure β L₀ s₀ n + 2 * L₀) / (1 - β)

/-- [definition] **The `n`-th bounce** on the receding wall in the light-cone chart: it lies on
the outgoing ray `u = departure n` and on the returning ray `v = departure (n + 1)`. -/
def bounce (β L₀ s₀ : K) (n : ℕ) : LightCone K :=
  ⟨departure β L₀ s₀ n, departure β L₀ s₀ (n + 1)⟩

/-- [definition] **The box's length at the `n`-th bounce**: the bounce's position. -/
def boxLength (β L₀ s₀ : K) (n : ℕ) : K := space (bounce β L₀ s₀ n)

/-- [definition] **The frequency after `n` bounces**: each bounce on the receding wall multiplies
it by `(1 − β)/(1 + β)` (`wall_reading`), the fixed wall keeps it (`mirror_one`). -/
def boxFreq (β ω₀ : K) (n : ℕ) : K := ω₀ * ((1 - β) / (1 + β)) ^ n

variable [CharZero K]

/-- [proved-derived; formal-checked] **Each bounce is an event on the receding wall**:
`x = L₀ + βt`. -/
theorem bounce_on_wall {β : K} (h : 1 - β ≠ 0) (L₀ s₀ : K) (n : ℕ) :
    space (bounce β L₀ s₀ n) = L₀ + β * time (bounce β L₀ s₀ n) := by
  simp only [space, time, bounce, departure]
  field_simp <;> ring

/-- [proved-derived; formal-checked] **The wall stretches the box**:
`L_(n+1) = L_n (1 + β)/(1 − β)`. -/
theorem boxLength_succ {β : K} (h : 1 - β ≠ 0) (L₀ s₀ : K) (n : ℕ) :
    boxLength β L₀ s₀ (n + 1) = (1 + β) / (1 - β) * boxLength β L₀ s₀ n := by
  simp only [boxLength, space, bounce, departure]
  field_simp <;> ring

/-- [proved-derived; formal-checked] `L_n = ((1 + β)/(1 − β))ⁿ L_0`. -/
theorem boxLength_pow {β : K} (h : 1 - β ≠ 0) (L₀ s₀ : K) (n : ℕ) :
    boxLength β L₀ s₀ n = ((1 + β) / (1 - β)) ^ n * boxLength β L₀ s₀ 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [boxLength_succ h, ih, pow_succ]; ring

/-- [proved-derived; formal-checked] **The frequency read on the receding wall**: the phase
`ω u` of a right-moving wave, read between two events of the wall `x = L₀ + βt`, is the phase of a
left-moving wave of frequency `ω (1 − β)/(1 + β)`. -/
theorem wall_reading {β : K} (h : 1 + β ≠ 0) (L₀ ω t t' : K) :
    ω * ((ofTX t' (L₀ + β * t')).u - (ofTX t (L₀ + β * t)).u) =
      ω * ((1 - β) / (1 + β)) * ((ofTX t' (L₀ + β * t')).v - (ofTX t (L₀ + β * t)).v) := by
  simp only [ofTX]
  field_simp <;> ring

/-- [proved-derived; formal-checked] **A receding wall keeps `ωL`**, bounce by bounce:
`ω_n L_n = ω_0 L_0`. -/
theorem freq_mul_length {β : K} (h₁ : 1 - β ≠ 0) (h₂ : 1 + β ≠ 0) (ω₀ L₀ s₀ : K) (n : ℕ) :
    boxFreq β ω₀ n * boxLength β L₀ s₀ n = ω₀ * boxLength β L₀ s₀ 0 := by
  rw [boxLength_pow h₁ L₀ s₀ n, boxFreq]
  have hD : ((1 - β) / (1 + β)) ^ n * ((1 + β) / (1 - β)) ^ n = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm (1 - β) (1 + β), div_self (mul_ne_zero h₂ h₁),
      one_pow]
  calc ω₀ * ((1 - β) / (1 + β)) ^ n * (((1 + β) / (1 - β)) ^ n * boxLength β L₀ s₀ 0)
      = ω₀ * boxLength β L₀ s₀ 0 * (((1 - β) / (1 + β)) ^ n * ((1 + β) / (1 - β)) ^ n) := by
        ring
    _ = ω₀ * boxLength β L₀ s₀ 0 := by rw [hD, mul_one]

end Box

/-! ## 3. The reactive wall -/

section ReactiveAlgebraic

variable {K : Type*} [Field K]

/-- [proved-derived; formal-checked] Over a field with `i² = −1`, `(ix − 1)(ix + 1) = −(1 + x²)`. -/
theorem reactive_product {i x : K} (hi : i ^ 2 = -1) :
    (i * x - 1) * (i * x + 1) = -(1 + x ^ 2) := by
  linear_combination x ^ 2 * hi

/-- [proved-derived; formal-checked] **The reactive wall returns everything**: over a field with
`i² = −1` (over `ℚ(i)`), `Γ = (ix − 1)/(ix + 1)` times its conjugate `(−ix − 1)/(−ix + 1)`
is `1`. -/
theorem reactive_norm {i x : K} (hi : i ^ 2 = -1) (hx : 1 + x ^ 2 ≠ 0) :
    (i * x - 1) / (i * x + 1) * ((-i * x - 1) / (-i * x + 1)) = 1 := by
  have hp := reactive_product (x := x) hi
  have hm : i * x - 1 ≠ 0 := fun h => hx (by rw [h, zero_mul] at hp; linear_combination hp)
  have hq : i * x + 1 ≠ 0 := fun h => hx (by rw [h, mul_zero] at hp; linear_combination hp)
  rw [show -i * x - 1 = -(i * x + 1) by ring, show -i * x + 1 = -(i * x - 1) by ring,
    neg_div_neg_eq, div_mul_div_comm, mul_comm (i * x - 1), div_self (mul_ne_zero hq hm)]

/-- [proved-derived; formal-checked] **The reactive wall's turn rate**: over a field with
`i² = −1`, the pole terms of `Γ⁻¹ dΓ/dx = i/(ix − 1) − i/(ix + 1)` sum to `−2i/(1 + x²)`. -/
theorem reactive_logDeriv {i x : K} (hi : i ^ 2 = -1) (hx : 1 + x ^ 2 ≠ 0) :
    i / (i * x - 1) - i / (i * x + 1) = -2 * i / (1 + x ^ 2) := by
  have hp := reactive_product (x := x) hi
  have hm : i * x - 1 ≠ 0 := fun h => hx (by rw [h, zero_mul] at hp; linear_combination hp)
  have hq : i * x + 1 ≠ 0 := fun h => hx (by rw [h, mul_zero] at hp; linear_combination hp)
  rw [div_sub_div _ _ hm hq, div_eq_div_iff (mul_ne_zero hm hq) hx]
  linear_combination (2 * i) * hp

end ReactiveAlgebraic

section ReactiveComplex

open Complex

/-- [definition] **The reactive wall** at `x = ωL/Z₀`: `Γ(x) = (ix − 1)/(ix + 1)`. -/
noncomputable def reactiveWall (x : ℝ) : ℂ := (I * x - 1) / (I * x + 1)

theorem reactiveWall_num_ne (x : ℝ) : (I * x - 1 : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem reactiveWall_den_ne (x : ℝ) : (I * x + 1 : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- [proved-derived; formal-checked] **`|Γ|² = 1`**: the reactive wall returns everything. -/
theorem reactiveWall_normSq (x : ℝ) : normSq (reactiveWall x) = 1 := by
  rw [reactiveWall, map_div₀]
  have h1 : normSq (I * x - 1) = 1 + x ^ 2 := by
    rw [normSq_apply]
    simp only [sub_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, one_re, sub_im, mul_im, one_im]
    ring
  have h2 : normSq (I * x + 1) = 1 + x ^ 2 := by
    rw [normSq_apply]
    simp only [add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, one_re, add_im, mul_im, one_im]
    ring
  rw [h1, h2]
  exact div_self (by positivity)

/-- [proved-derived; formal-checked] `dΓ/dx = 2i/(ix + 1)²` in the real `x`. -/
theorem reactiveWall_hasDerivAt (x : ℝ) :
    HasDerivAt reactiveWall (2 * I / (I * x + 1) ^ 2) x := by
  have hu : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hc : HasDerivAt (fun y : ℝ => I * (y : ℂ) - 1) (I * 1) x :=
    (hu.const_mul I).sub_const 1
  have hd : HasDerivAt (fun y : ℝ => I * (y : ℂ) + 1) (I * 1) x :=
    (hu.const_mul I).add_const 1
  have h := hc.fun_div hd (reactiveWall_den_ne x)
  show HasDerivAt (fun y : ℝ => (I * (y : ℂ) - 1) / (I * y + 1)) _ x
  convert h using 1
  ring

/-- [proved-derived; formal-checked] **The reactive wall's turn rate**: `Γ⁻¹ dΓ/dx = −2i/(1 + x²)`,
a pure turn rate whose size `2/(1 + x²)` is the delay of the return in units of `L/Z₀`. -/
theorem reactiveWall_logDeriv (x : ℝ) :
    (reactiveWall x)⁻¹ * (2 * I / (I * x + 1) ^ 2) = -2 * I / (1 + (x : ℂ) ^ 2) := by
  have hm := reactiveWall_num_ne x
  have hd := reactiveWall_den_ne x
  have hp : (I * x - 1) * (I * x + 1) = -(1 + (x : ℂ) ^ 2) :=
    reactive_product (x := (x : ℂ)) I_sq
  have h1 : (reactiveWall x)⁻¹ * (2 * I / (I * x + 1) ^ 2) =
      2 * I / ((I * x - 1) * (I * x + 1)) := by
    rw [reactiveWall, inv_div]
    field_simp <;> ring
  rw [h1, hp, div_neg]
  ring

/-- [proved-derived; formal-checked] **The delay of the return**: with `x = ωL/Z₀` the chain rule
gives `dΓ/dω = (L/Z₀) dΓ/dx`, so `Γ⁻¹ dΓ/dω` is a pure turn rate whose size is
`|Im Γ⁻¹ dΓ/dω| = (2L/Z₀)/(1 + x²)`, `2L/Z₀` at `x = 0`. -/
theorem reactiveWall_delay {L Z₀ : ℝ} (hL : 0 < L) (hZ : 0 < Z₀) (ω : ℝ) :
    HasDerivAt (fun ω : ℝ => reactiveWall (ω * L / Z₀))
        ((L / Z₀ : ℝ) • (2 * I / (I * ((ω * L / Z₀ : ℝ) : ℂ) + 1) ^ 2)) ω ∧
      |((reactiveWall (ω * L / Z₀))⁻¹ *
          ((L / Z₀ : ℝ) • (2 * I / (I * ((ω * L / Z₀ : ℝ) : ℂ) + 1) ^ 2))).im| =
        2 * L / Z₀ / (1 + (ω * L / Z₀) ^ 2) := by
  constructor
  · have h := (reactiveWall_hasDerivAt (ω * L / Z₀)).scomp ω
      (((hasDerivAt_id' ω).mul_const L).div_const Z₀)
    rw [one_mul] at h
    exact h
  · rw [Complex.real_smul, mul_left_comm, reactiveWall_logDeriv]
    have h : ((L / Z₀ : ℝ) : ℂ) * (-2 * I / (1 + ((ω * L / Z₀ : ℝ) : ℂ) ^ 2)) =
        ((-(2 * (L / Z₀) / (1 + (ω * L / Z₀) ^ 2)) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h, Complex.mul_I_im, Complex.ofReal_re, abs_neg, abs_of_pos (by positivity)]
    ring

end ReactiveComplex

end Holonics.Physics.Spacetime.MovingMirror
