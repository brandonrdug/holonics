import HolonicsResearch.HNN.NewsClock
import HolonicsResearch.HNN.PassiveMode
import Mathlib

/-!
# The held step: a clocked level's ticks on one held arrival, and the covectors of its mode, gain and arrival

[proved-derived] The source is #410's box "The held step's covectors" (#404, #406), left by the record of the news
clock (`research/records/2026-10-27_THE_LEVELS_TICK_ON_THEIR_OWN_NEWS_SO_THE_TOWER_LEARNS_ITS_ENCODING_ON_ITS_OWN_AXIS.md`,
§2 and §6.4) beside `HNN/NewsClock`, which proves the homogeneous case (`move_covector`: the arrival enters once,
after the move). Here the arrival is held through the ticks: a level that ticks `n = Δτ` times at an arrival takes
`h ← λ h + γ u` at each tick with the same `u = P x`.

What is proved, over any commutative ring with a star (`ℂ` with conjugation is the consumer's).

1. **The held state** (`held`, `held_eq`, `held_add`, `held_poly`): `h_n = λⁿ h + (Σ_(j<n) λʲ) γ u`; ticks compose,
   `h_(m+n)` is `n` ticks from `h_m`; and `h_n` is the value at `λ` of the polynomial
   `h Xⁿ + (Σ_(j<n) Xʲ) γ u`.
2. **Its four partials** (`heldDz`, `heldDz_eq`, `heldDz_eq_derivative`, `held_gain`, `held_arrival`,
   `held_state`): in the mode, `∂h_n/∂λ = n λⁿ⁻¹ h + (Σ_(j<n) j λʲ⁻¹) γ u`, the polynomial's derivative read at `λ`;
   `h_n` is affine in the gain with slope `(Σ_(j<n) λʲ) u`, in the arrival with slope `(Σ_(j<n) λʲ) γ`, and in the
   state before with slope `λⁿ`.
3. **The reverse over the ticks sends each partial's conjugate** (`mode_covector`, `gain_covector`,
   `arrival_covector`, `arrival_covector_of_real_gain`, `state_covector`). With the covector carried back one tick at
   a time, `G⁽ʲ⁻¹⁾ = conj(λ) G⁽ʲ⁾` from `G⁽ⁿ⁾ = G` (`NewsClock.subCovector`, `NewsClock.subCovector_step`):
   `Σ_(j=1..n) conj(h⁽ʲ⁻¹⁾) G⁽ʲ⁾ = conj(∂h_n/∂λ) G`; `Σ_j conj(G⁽ʲ⁾) u = conj(G) ∂h_n/∂γ`;
   `conj(γ) Σ_j G⁽ʲ⁾ = conj(∂h_n/∂u) G`, which is the box's `γ Σ_j G⁽ʲ⁾` for a real gain; and the covector that
   reaches the state before the arrival is `conj(λⁿ) G`. The sums are the chain rule of one tick taken `n` times, and
   no tick's state is kept but the `n` states the forward pass itself visits.
4. **The real readings** (`gain_covector_re`): over `ℂ`, `Σ_j Re(conj(G⁽ʲ⁾) u) = Re(conj(G) ∂h_n/∂γ)`, the form the
   real gain's deposit reads.
5. **An arrival that does not tick** (`no_tick`): `n = 0` leaves the state, sends nothing to the mode, the gain or the
   arrival, and passes `G` through.
6. **Each tick is the passive step** (`held_passive`): with `|λ| = ρ ≤ ρ_max < 1`, the gain `√(1 − ρ²)` and an
   arrival of size at most `M`, a state within `K(ρ_max)·M` stays within it at every tick
   (`PassiveMode.passive_step`), however long the arrival is held.
7. **A held arrival comes to rest** (`held_geometric`, `held_tendsto`): for `λ ≠ 1`,
   `h_n = λⁿ (h − h_∞) + h_∞` with `h_∞ = γ u/(1 − λ)`, and for `|λ| < 1` the state tends to `h_∞` as the ticks
   go on: holding an arrival through many ticks is a relaxation to the fixed point of one tick, at the rate `|λ|` a
   tick.

Limits. One mode and one held arrival; the mode, the gain and the arrival are the same at every tick of the arrival,
which is the built step (`Tower::step` under the news clock). A gate that moves the mode between ticks is
`NewsClock.state_of_moves`' case and is not restated. The partials are stated as slopes of an affine map and as a
polynomial derivative, with no analytic derivative: the state is a polynomial in each of its arguments. Statement 7's
rest is a statement about the limit of ticks at one arrival, and no arrival of the built tower is held past its own
`Δτ`.

The computational object is the helical pair interaction: the mode's turn `λ` is a navigator's advance read at the
level's clock, the tick is the helix's carry, and the covector carried back is the adjoint's transport along the same
ticks. Of the winding guide's six general objects this touches the helix (the tick and its count), the tube (the
clocked span of one arrival and its moments) and the tower thread (the level's own clock); the pair, faces and
placement and the cell holonomy stay attached.

Consumers: the atlas rows `hnn.tower-news-clock-carry` and `tower.packet-input` (a level's input held through the
ticks of the level below), `Tower::step` and `Tower::reverse_joined` under the news clock.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.HeldStep

open Finset
open Holonics.HNN.NewsClock (subCovector)

section Algebra

variable {R : Type*} [CommRing R]

/-! ## 1. The held state -/

/-- [definition] The state after `n` ticks of the mode `z` with the arrival `u` held at the gain `g`:
`h ← z h + g u` at each tick. -/
def held (z g u h : R) : ℕ → R
  | 0 => h
  | n + 1 => z * held z g u h n + g * u

@[simp] theorem held_zero (z g u h : R) : held z g u h 0 = h := rfl

@[simp] theorem held_succ (z g u h : R) (n : ℕ) :
    held z g u h (n + 1) = z * held z g u h n + g * u := rfl

/-- [proved-standard] The geometric sum's step: `Σ_(j<n+1) zʲ = z Σ_(j<n) zʲ + 1`. -/
theorem geom_succ (z : R) (n : ℕ) : ∑ j ∈ range (n + 1), z ^ j = z * ∑ j ∈ range n, z ^ j + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ']

/-- [proved-derived] **The held state:** `h_n = zⁿ h + (Σ_(j<n) zʲ) g u`. -/
theorem held_eq (z g u h : R) (n : ℕ) :
    held z g u h n = z ^ n * h + (∑ j ∈ range n, z ^ j) * (g * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [held_succ, ih, geom_succ]
    ring

/-- [proved-derived] **Ticks compose:** `m + n` ticks are `n` ticks from the state after `m`. -/
theorem held_add (z g u h : R) (m n : ℕ) :
    held z g u h (m + n) = held z g u (held z g u h m) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [← Nat.add_assoc, held_succ, held_succ, ih]

/-- [proved-derived] The held state is the value at the mode of the polynomial `h Xⁿ + (Σ_(j<n) Xʲ) g u`. -/
theorem held_poly (z g u h : R) (n : ℕ) :
    held z g u h n = Polynomial.eval z
      (Polynomial.C h * Polynomial.X ^ n + (∑ j ∈ range n, Polynomial.X ^ j) * Polynomial.C (g * u)) := by
  rw [held_eq]
  simp [Polynomial.eval_finsetSum]
  ring

/-! ## 2. The partials -/

/-- [definition] The derivative of the held state in its mode, by the product rule of one tick:
`∂h_(n+1) = h_n + z ∂h_n`. -/
def heldDz (z g u h : R) : ℕ → R
  | 0 => 0
  | n + 1 => held z g u h n + z * heldDz z g u h n

@[simp] theorem heldDz_zero (z g u h : R) : heldDz z g u h 0 = 0 := rfl

@[simp] theorem heldDz_succ (z g u h : R) (n : ℕ) :
    heldDz z g u h (n + 1) = held z g u h n + z * heldDz z g u h n := rfl

/-- [proved-standard] `z · (j z^(j−1)) = j zʲ`, the natural subtraction read at `j = 0` as zero. -/
theorem mul_deriv_term (z : R) (j : ℕ) : z * ((j : R) * z ^ (j - 1)) = (j : R) * z ^ j := by
  cases j with
  | zero => simp
  | succ j => rw [Nat.add_sub_cancel, pow_succ]; ring

/-- [proved-standard] `Σ_(j<n+1) j z^(j−1) = z Σ_(j<n) j z^(j−1) + Σ_(j<n) zʲ`. -/
theorem deriv_sum_succ (z : R) (n : ℕ) :
    ∑ j ∈ range (n + 1), (j : R) * z ^ (j - 1) =
      z * ∑ j ∈ range n, (j : R) * z ^ (j - 1) + ∑ j ∈ range n, z ^ j := by
  rw [Finset.sum_range_succ', Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_deriv_term]
  push_cast
  ring

/-- [proved-derived] **The mode's partial:** `∂h_n/∂z = n zⁿ⁻¹ h + (Σ_(j<n) j zʲ⁻¹) g u`. -/
theorem heldDz_eq (z g u h : R) (n : ℕ) :
    heldDz z g u h n =
      (n : R) * z ^ (n - 1) * h + (∑ j ∈ range n, (j : R) * z ^ (j - 1)) * (g * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [heldDz_succ, ih, held_eq, deriv_sum_succ, Nat.add_sub_cancel]
    have h1 : z * ((n : R) * z ^ (n - 1) * h) = (n : R) * z ^ n * h := by
      rw [← mul_assoc, mul_deriv_term]
    push_cast
    linear_combination h1

/-- [proved-derived] **The mode's partial is the polynomial's derivative read at the mode.** -/
theorem heldDz_eq_derivative (z g u h : R) (n : ℕ) :
    heldDz z g u h n = Polynomial.eval z (Polynomial.derivative
      (Polynomial.C h * Polynomial.X ^ n + (∑ j ∈ range n, Polynomial.X ^ j) * Polynomial.C (g * u))) := by
  rw [heldDz_eq]
  simp [Polynomial.derivative_mul, Polynomial.eval_finsetSum, Polynomial.derivative_X_pow]
  ring

/-- [proved-derived] **The gain's partial:** the held state is affine in the gain with slope `(Σ_(j<n) zʲ) u`. -/
theorem held_gain (z g d u h : R) (n : ℕ) :
    held z (g + d) u h n - held z g u h n = d * ((∑ j ∈ range n, z ^ j) * u) := by
  rw [held_eq, held_eq]
  ring

/-- [proved-derived] **The arrival's partial:** the held state is affine in the arrival with slope
`(Σ_(j<n) zʲ) g`. -/
theorem held_arrival (z g u v h : R) (n : ℕ) :
    held z g (u + v) h n - held z g u h n = (∑ j ∈ range n, z ^ j) * g * v := by
  rw [held_eq, held_eq]
  ring

/-- [proved-derived] **The state's partial:** the held state is affine in the state before with slope `zⁿ`. -/
theorem held_state (z g u h k : R) (n : ℕ) :
    held z g u (h + k) n - held z g u h n = z ^ n * k := by
  rw [held_eq, held_eq]
  ring

/-! ## 3. The covectors over the ticks -/

/-- [proved-derived] The states the forward pass visits, each carried on by the ticks after it, sum to the mode's
partial: `Σ_(j<n) z^(n−(j+1)) h_j = ∂h_n/∂z`. -/
theorem sum_carried (z g u h : R) (n : ℕ) :
    ∑ j ∈ range n, z ^ (n - (j + 1)) * held z g u h j = heldDz z g u h n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, heldDz_succ, ← ih, Finset.mul_sum, Nat.sub_self, pow_zero, one_mul, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.mp hj
    rw [show n + 1 - (j + 1) = n - (j + 1) + 1 by omega, pow_succ']
    ring

/-- [proved-standard] The carried powers are the geometric sum read backwards. -/
theorem sum_pow_reflect (z : R) (n : ℕ) : ∑ j ∈ range n, z ^ (n - (j + 1)) = ∑ j ∈ range n, z ^ j := by
  have h := Finset.sum_range_reflect (fun j => z ^ j) n
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  show z ^ (n - (j + 1)) = z ^ (n - 1 - j)
  congr 1
  omega

variable [StarRing R]

/-- [proved-derived] **The mode's covector:** each tick pairs the state before it with the covector after it, and
the `n` pairings sum to `conj(∂h_n/∂z) G`. -/
theorem mode_covector (z g u h G : R) (n : ℕ) :
    ∑ j ∈ range n, star (held z g u h j) * subCovector z G n (j + 1) = star (heldDz z g u h n) * G := by
  rw [← sum_carried, star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [subCovector, star_mul', star_pow]
  ring

/-- [proved-derived] **The gain's covector:** `Σ_j conj(G⁽ʲ⁾) u = conj(G) · (Σ_(j<n) zʲ) u`, the conjugate
covector against the gain's partial. -/
theorem gain_covector (z u G : R) (n : ℕ) :
    ∑ j ∈ range n, star (subCovector z G n (j + 1)) * u = star G * ((∑ j ∈ range n, z ^ j) * u) := by
  rw [← sum_pow_reflect, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [subCovector, star_mul', star_pow, star_star]
  ring

/-- [proved-derived] **The arrival's covector:** `conj(g) Σ_j G⁽ʲ⁾ = conj((Σ_(j<n) zʲ) g) G`, the conjugate of
the arrival's partial against the covector. -/
theorem arrival_covector (z g G : R) (n : ℕ) :
    star g * ∑ j ∈ range n, subCovector z G n (j + 1) = star ((∑ j ∈ range n, z ^ j) * g) * G := by
  rw [← sum_pow_reflect, star_mul', star_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [subCovector, star_pow]
  ring

/-- [proved-derived] For a gain that is its own conjugate (a real gain) the arrival's covector is the box's
`g Σ_j G⁽ʲ⁾`. -/
theorem arrival_covector_of_real_gain (z g G : R) (n : ℕ) (hg : star g = g) :
    g * ∑ j ∈ range n, subCovector z G n (j + 1) = star ((∑ j ∈ range n, z ^ j) * g) * G := by
  rw [← arrival_covector, hg]

/-- [proved-derived] **The state's covector:** the covector reaching the state before the arrival is
`conj(zⁿ) G`, the conjugate of the state's partial. -/
theorem state_covector (z G : R) (n : ℕ) : subCovector z G n 0 = star (z ^ n) * G := by
  simp [subCovector, star_pow]

/-- [proved-derived] **An arrival that does not tick** leaves the state, sends nothing to the mode, the gain or
the arrival, and passes the covector through. -/
theorem no_tick (z g u h G : R) :
    held z g u h 0 = h ∧
      ∑ j ∈ range 0, star (held z g u h j) * subCovector z G 0 (j + 1) = 0 ∧
      ∑ j ∈ range 0, star (subCovector z G 0 (j + 1)) * u = 0 ∧
      star g * ∑ j ∈ range 0, subCovector z G 0 (j + 1) = 0 ∧
      subCovector z G 0 0 = G := by
  simp [subCovector]

end Algebra

/-! ## 4. Over the complex numbers: the real reading, the passive bound and the rest -/

section Complex

open Complex

/-- [proved-derived] **The gain's real reading:** `Σ_j Re(conj(G⁽ʲ⁾) u) = Re(conj(G) ∂h_n/∂γ)`. -/
theorem gain_covector_re (z u G : ℂ) (n : ℕ) :
    ∑ j ∈ range n, (star (subCovector z G n (j + 1)) * u).re =
      (star G * ((∑ j ∈ range n, z ^ j) * u)).re := by
  rw [← gain_covector, Complex.re_sum]

/-- [proved-derived] **Each tick is the passive step:** with a turn of modulus `ρ ≤ ρ_max < 1`, the gain
`√(1 − ρ²)` and an arrival of size at most `M`, a state within `K(ρ_max)·M` stays within it at every tick of a
held arrival. -/
theorem held_passive {ρ ρmax M : ℝ} (h0 : 0 ≤ ρ) (hρ : ρ ≤ ρmax) (hmax : ρmax < 1) (hM : 0 ≤ M)
    {z h u : ℂ} (hz : ‖z‖ = ρ) (hh : ‖h‖ ≤ PassiveMode.passiveBound ρmax * M) (hu : ‖u‖ ≤ M) (n : ℕ) :
    ‖held z (Real.sqrt (1 - ρ ^ 2) : ℂ) u h n‖ ≤ PassiveMode.passiveBound ρmax * M := by
  induction n with
  | zero => simpa using hh
  | succ n ih =>
    rw [held_succ]
    exact PassiveMode.passive_step h0 hρ hmax hM hz ih hu

/-- [proved-derived] **The held state about its rest:** for `z ≠ 1`, `h_n = zⁿ (h − h_∞) + h_∞` with
`h_∞ = g u/(1 − z)`, the fixed point of one tick. -/
theorem held_geometric (z g u h : ℂ) (hz : z ≠ 1) (n : ℕ) :
    held z g u h n = z ^ n * (h - g * u / (1 - z)) + g * u / (1 - z) := by
  have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [held_succ, ih]
    field_simp
    ring

/-- [proved-derived] **A held arrival comes to rest:** for `|z| < 1` the held state tends to `g u/(1 − z)` as
the ticks go on, from every state. -/
theorem held_tendsto (z g u h : ℂ) (hz : ‖z‖ < 1) :
    Filter.Tendsto (fun n => held z g u h n) Filter.atTop (nhds (g * u / (1 - z))) := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hpow : Filter.Tendsto (fun n : ℕ => z ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
  have h2 := (hpow.mul_const (h - g * u / (1 - z))).add_const (g * u / (1 - z))
  simp only [zero_mul, zero_add] at h2
  refine h2.congr fun n => ?_
  rw [held_geometric z g u h hz1 n]

end Complex

end Holonics.HNN.HeldStep
