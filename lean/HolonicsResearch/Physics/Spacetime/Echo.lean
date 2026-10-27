import Holonics.Physics.Spacetime.Boost
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# The echo: the round trip reads relative rapidity, a resonator's modes are the branches of the
log of its round trip, and a plasma gives light a rest frequency

The record `research/records/2026-10-25_A_COMPARISON_IS_AN_ECHO_THE_ROUND_TRIP_READS_RELATIVE_RAPIDITY_THE_DELAY_READS_THE_MEDIUM_AND_A_RESONATORS_MODES_ARE_THE_BRANCHES_OF_THE_LOG_OF_ITS_ROUND_TRIP.md`
(§§1, 3–6) reads a comparison as an echo. This file proves the box that record leaves in #410,
beside `Physics/Spacetime/Boost` and its Doppler chart `D(β) = (1 + β)/(1 − β)` (the landmark
owner's `doppler`).

[proved-derived; formal-checked] What is proved.

1. **The round trip reads only relative rapidity** (`echo_identity`, `doppler_sub`,
   `heard_mul_return`, `echo_self`, `echo_instances`): for sound of speed `c`, an emitter of
   velocity `a` and a wall of velocity `b`, the wall's hearing times the return's is
   `(c − b)(c + a)/((c − a)(c + b)) = D(a/c)/D(b/c)`, and `D(x)/D(y) = D((x − y)/(1 − xy))`,
   Einstein's subtraction at the speed `c`, over ℚ; at `c = 5` the pairs `(−3, −2)` and
   `(0, 25/19)` both echo `7/12` while the wall hears `7/8` against `14/19`. **The delay reads the
   medium** (`round_trip_wind`): along a wind `u` the round trip takes `2Lc/(c² − u²)`, across it
   `2L/w` with `w² = c² − u²`, a ratio `c/w` (`5/4` at `c = 5`, `u = 3`).
2. **A resonator's mode class is its round trip's** (`transform_vanishes`, `mode_class`): over a
   field holding a primitive `4N`-th root of unity `ω`, a sequence with `x[t + N] = ρ x[t]` and
   `ρ⁴ = 1` has `ρ = (ω^N)^r` for one `r < 4`, and its `4N`-point transform
   `Σ_(t<4N) x[t] ω^(mt)` vanishes at every `m` with `r + m ≢ 0 (mod 4)`: its spectrum lies on one
   residue class mod 4. More generally the transform vanishes wherever `ρ ω^(mN) ≠ 1`. Over `ℂ`,
   a lossless round trip has its modes at `θ ∈ −arg ρ + 2πℤ` (`mode_condition`), and
   `log ρ = log |ρ| + i arg ρ` (`round_trip_log`).
3. **Young's rule** (`pluck_second_difference`, `sineMode_recurrence`, `green`,
   `sineCoefficient_eq`, `young`): the string of `N` cells plucked at cell `a` (`0 < a < N`) has a
   single corner, its second difference is `−N` at `a` and zero elsewhere, so its `n`-th sine
   coefficient `S_n = Σ_(0<j<N) y_j sin(πnj/N)` satisfies `(2 − 2cos(πn/N)) S_n = N sin(πna/N)`;
   for `0 < n < N` it vanishes iff `N ∣ na`; on 16 cells `a = 8` silences the even harmonics,
   `a = 4` the multiples of 4, `a = 3` and `5` nothing (`young_sixteen`).
4. **The sum of round trips** (`round_trip_sum`, `round_trip_remainder`, `round_trip_gain`,
   `poisson_kernel`, `normSq_one_sub`, `poisson_doppler`, `poisson_doppler_instances`,
   `half_power`, `airy_eq_poisson_div`): `Σ_(j≥0) ρʲ = 1/(1 − ρ)` for `|ρ| < 1`,
   `Σ_(j<m) ρʲ − 1/(1 − ρ) = −ρᵐ/(1 − ρ)` for `ρ ≠ 1`, `|ρᵐ|² = (|ρ|²)ᵐ`, and
   `Re((1 + ρ)/(1 − ρ)) = (1 − |ρ|²)/|1 − ρ|²` over `ℂ` (so over `ℚ(i)`); for `ρ = g e^(iφ)`,
   `|1 − ρ|² = (1 − g)² + 4g sin²(φ/2)`, the Poisson reading is `k = (1 + g)/(1 − g)` at
   resonance and `1/k` between, half power falls at `sin²(φ/2) = (1 − g)²/(4g)`, and the Airy
   reading `(1 − g)²/|1 − ρ|²` is the Poisson reading over `k`.
5. **The plasma shell and its rest frame** (`plasma_shell`, `plasma_rest`, `plasma_rest_instance`):
   `ω² = ω_p² + c²k²` is `(ω − ck)(ω + ck) = ω_p²`, the interval of the wave's light-cone
   components; the boost of Doppler ratio `κ` with `κ²(ω − ck) = ω + ck` brings the wave to rest
   (`u′ = v′`, so no momentum) at frequency `√(ω_p²)`, and the frame's velocity is
   `β(κ) = ck/ω`. For `(ω, ck) = (5, 4)` it is the rest frequency 3 at velocity `4/5`.
6. **The beat is the slip** (`slip`, `slip_contact`, `slip_eq_zero_iff`, `fifth_lock`,
   `tempered_fifth_beats`): two tones beat at the slip `n f₁ − m f₂` of their pair contact
   `[f₁ | −f₂]`; it vanishes exactly at the lock `q f₁ = p f₂`, the fifth tuned by ear is
   `f₂/f₁ = 3/2`, and a tempered fifth `r¹² = 2⁷` always beats.

The computational object is the helical pair interaction: an echo is a contact's return, and a
resonator is a ring whose round trip `ρ` places its modes. Of the winding guide's six general
objects this touches the pair (the return), the cell holonomy (the round trip `ρ` and its
residue class) and faces and placement (where the pluck enters and the transform's bins); the
helix, the tube and the tower thread stay attached.

Consumers: the atlas rows `wave.echo-stretch-and-delay`, `wave.round-trip-modes`,
`wave.round-trip-sum-doppler`, `plasma.cutoff-rest-frequency` and `pair.beat-is-slip`, and the
record's Owed list.
-/

namespace Holonics.Physics.Spacetime.Echo

open Finset
open Holonics.Physics.Spacetime.Boost
open Holonics.Compression.Landmark.FixedPoint (doppler)

/-! ## 1. The round trip reads only relative rapidity -/

/-- [proved-derived; formal-checked] `D(y/c) = (c + y)/(c − y)`. -/
theorem doppler_div {c y : ℚ} (hc : c ≠ 0) : doppler (y / c) = (c + y) / (c - y) := by
  unfold doppler
  rw [one_add_div hc, one_sub_div hc, div_div_div_cancel_right₀ hc]

/-- [proved-derived; formal-checked] **The echo identity**: the emitter of velocity `a` hears its
echo off the wall of velocity `b`, in a medium of sound speed `c`, at the ratio
`(c − b)(c + a)/((c − a)(c + b)) = D(a/c)/D(b/c)`. -/
theorem echo_identity {a b c : ℚ} (hc : c ≠ 0) :
    (c - b) * (c + a) / ((c - a) * (c + b)) = doppler (a / c) / doppler (b / c) := by
  rw [doppler_div hc, doppler_div hc, div_div_div_eq]
  ring

/-- [proved-derived; formal-checked] **Einstein's subtraction**:
`D(x)/D(y) = D((x − y)/(1 − xy))`. -/
theorem doppler_sub {x y : ℚ} (hx : 1 - x ≠ 0) (hy : 1 + y ≠ 0) (hxy : 1 - x * y ≠ 0) :
    doppler x / doppler y = doppler ((x - y) / (1 - x * y)) := by
  unfold doppler
  rw [one_add_div hxy, one_sub_div hxy, div_div_div_cancel_right₀ hxy, div_div_div_eq]
  have hd : 1 - x * y - (x - y) ≠ 0 := by
    rw [show 1 - x * y - (x - y) = (1 - x) * (1 + y) by ring]
    exact mul_ne_zero hx hy
  rw [div_eq_div_iff (mul_ne_zero hx hy) hd]
  ring

/-- The frequency ratio a receiver of velocity `b` hears from an emitter of velocity `a` behind it,
in a medium of sound speed `c`: `(c − b)/(c − a)`. -/
def heard (a b c : ℚ) : ℚ := (c - b) / (c - a)

/-- [proved-derived; formal-checked] The echo is the wall's hearing times the return's, the return
read in the mirrored axis: `heard(a, b) · heard(−b, −a) = (c − b)(c + a)/((c − a)(c + b))`. -/
theorem heard_mul_return (a b c : ℚ) :
    heard a b c * heard (-b) (-a) c = (c - b) * (c + a) / ((c - a) * (c + b)) := by
  unfold heard
  rw [div_mul_div_comm, sub_neg_eq_add, sub_neg_eq_add]

/-- [proved-derived; formal-checked] Equal velocities give the echo `1`. -/
theorem echo_self {a c : ℚ} (h₁ : c - a ≠ 0) (h₂ : c + a ≠ 0) :
    (c - a) * (c + a) / ((c - a) * (c + a)) = 1 :=
  div_self (mul_ne_zero h₁ h₂)

/-- [proved-derived; formal-checked] The receipt's instances at `c = 5`: `(a, b) = (−3, −2)` and
`(0, 25/19)` both echo `7/12`, while the wall hears `7/8` against `14/19`. -/
theorem echo_instances :
    ((5 : ℚ) - -2) * (5 + -3) / ((5 - -3) * (5 + -2)) = 7 / 12 ∧
      ((5 : ℚ) - 25 / 19) * (5 + 0) / ((5 - 0) * (5 + 25 / 19)) = 7 / 12 ∧
      heard (-3) (-2) 5 = 7 / 8 ∧ heard 0 (25 / 19) 5 = 14 / 19 := by
  norm_num [heard]

/-- [proved-derived; formal-checked] **The delay reads the medium**: a round trip of length `L`
along a wind `u` takes `L/(c − u) + L/(c + u) = 2Lc/(c² − u²)`, across it `2L/w` with
`w² = c² − u²`, and their ratio is `c/w`. -/
theorem round_trip_wind {L c u w : ℚ} (hL : L ≠ 0) (hw : w ≠ 0) (hcw : w ^ 2 = c ^ 2 - u ^ 2)
    (h₁ : c - u ≠ 0) (h₂ : c + u ≠ 0) :
    L / (c - u) + L / (c + u) = 2 * L * c / (c ^ 2 - u ^ 2) ∧
      2 * L * c / (c ^ 2 - u ^ 2) / (2 * L / w) = c / w := by
  have h : c ^ 2 - u ^ 2 ≠ 0 := by
    rw [show c ^ 2 - u ^ 2 = (c - u) * (c + u) by ring]
    exact mul_ne_zero h₁ h₂
  constructor
  · rw [div_add_div _ _ h₁ h₂, div_eq_div_iff (mul_ne_zero h₁ h₂) h]
    ring
  · rw [← hcw, div_div_div_eq,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hw) (mul_ne_zero two_ne_zero hL)) hw]
    ring

/-- [proved-derived; formal-checked] At `c = 5`, `u = 3`, `w = 4` the ratio is `5/4`. -/
theorem round_trip_wind_instance :
    2 * 1 * 5 / ((5 : ℚ) ^ 2 - 3 ^ 2) / (2 * 1 / 4) = 5 / 4 ∧ (4 : ℚ) ^ 2 = 5 ^ 2 - 3 ^ 2 := by
  norm_num

/-! ## 2. A resonator's modes lie on its round trip's residue class -/

section Modes

variable {K : Type*} [Field K]

/-- [proved-derived; formal-checked] `x[t + qN] = ρ^q x[t]`. -/
theorem round_trip_pow {N : ℕ} {ρ : K} {x : ℕ → K} (hx : ∀ t, x (t + N) = ρ * x t) (t q : ℕ) :
    x (t + q * N) = ρ ^ q * x t := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show t + (q + 1) * N = t + q * N + N by ring, hx, ih, pow_succ]
    ring

/-- [proved-derived; formal-checked] A sum over one period of a periodic sequence does not see
where the period starts. -/
theorem periodic_shift_sum {P : ℕ} (g : ℕ → K) (hg : ∀ t, g (t + P) = g t) (N : ℕ) :
    ∑ t ∈ range P, g (N + t) = ∑ t ∈ range P, g t := by
  have h1 := Finset.sum_range_add g N P
  have h2 := Finset.sum_range_add g P N
  rw [Nat.add_comm N P] at h1
  have h3 : ∑ t ∈ range N, g (P + t) = ∑ t ∈ range N, g t :=
    Finset.sum_congr rfl fun t _ => by rw [Nat.add_comm]; exact hg t
  rw [h3] at h2
  linear_combination h2 - h1

/-- [proved-derived; formal-checked] **The transform vanishes off the round trip's class**: if
`x[t + N] = ρ x[t]`, `ρ⁴ = 1` and `ω^(4N) = 1`, the `4N`-point transform at `m` vanishes wherever
`ρ ω^(mN) ≠ 1`. -/
theorem transform_vanishes {N : ℕ} {ω ρ : K} {x : ℕ → K} (hx : ∀ t, x (t + N) = ρ * x t)
    (hρ : ρ ^ 4 = 1) (hω : ω ^ (4 * N) = 1) {m : ℕ} (hz : ρ * ω ^ (m * N) ≠ 1) :
    ∑ t ∈ range (4 * N), x t * ω ^ (m * t) = 0 := by
  set g : ℕ → K := fun t => x t * ω ^ (m * t) with hg_def
  have hper : ∀ t, g (t + 4 * N) = g t := by
    intro t
    simp only [hg_def]
    rw [round_trip_pow hx t 4, hρ, one_mul,
      show m * (t + 4 * N) = m * t + 4 * N * m by ring, pow_add, pow_mul ω (4 * N) m, hω, one_pow,
      mul_one]
  have hshift : ∀ t, g (N + t) = (ρ * ω ^ (m * N)) * g t := by
    intro t
    simp only [hg_def]
    rw [Nat.add_comm N t, hx, show m * (t + N) = m * t + m * N by ring, pow_add]
    ring
  have h := periodic_shift_sum g hper N
  simp only [hshift] at h
  rw [← Finset.mul_sum] at h
  have h0 : (ρ * ω ^ (m * N) - 1) * ∑ t ∈ range (4 * N), g t = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hz)

/-- [proved-derived; formal-checked] **The mode class**: over a field holding a primitive `4N`-th
root of unity `ω`, a round trip `ρ` with `ρ⁴ = 1` is `(ω^N)^r` for one `r < 4`, and the
`4N`-point transform of `x[t + N] = ρ x[t]` vanishes at every `m` with `4 ∤ r + m`: `ρ = 1` keeps
all harmonics, `ρ = −1` the odd half-harmonics, `ρ = ±i` one quarter class. -/
theorem mode_class {N : ℕ} (hN : 0 < N) {ω ρ : K} (hω : IsPrimitiveRoot ω (4 * N))
    (hρ : ρ ^ 4 = 1) {x : ℕ → K} (hx : ∀ t, x (t + N) = ρ * x t) :
    ∃ r < 4, ρ = (ω ^ N) ^ r ∧
      ∀ m, ¬ 4 ∣ r + m → ∑ t ∈ range (4 * N), x t * ω ^ (m * t) = 0 := by
  have hμ : IsPrimitiveRoot (ω ^ N) 4 := by
    have h := hω.pow_of_dvd hN.ne' (dvd_mul_left N 4)
    rwa [Nat.mul_div_cancel _ hN] at h
  obtain ⟨r, hr, hrρ⟩ := hμ.eq_pow_of_pow_eq_one hρ
  refine ⟨r, hr, hrρ.symm, fun m hm => transform_vanishes hx hρ hω.pow_eq_one ?_⟩
  rw [← hrρ, ← pow_mul, ← pow_add, ne_eq, hω.pow_eq_one_iff_dvd]
  intro h
  apply hm
  have h' : 4 * N ∣ (r + m) * N := by
    rwa [show (r + m) * N = N * r + m * N by ring]
  exact (mul_dvd_mul_iff_right hN.ne').mp h'

end Modes

/-- [proved-derived; formal-checked] **The modes are the branches of the log of the round trip**:
for a lossless round trip (`|ρ| = 1`), `e^(iθ) ρ = 1` exactly when `θ ∈ −arg ρ + 2πℤ`. -/
theorem mode_condition {ρ : ℂ} (hρ : ‖ρ‖ = 1) (θ : ℝ) :
    Complex.exp (θ * Complex.I) * ρ = 1 ↔ ∃ n : ℤ, θ = -Complex.arg ρ + n * (2 * Real.pi) := by
  have hρ' : ρ = Complex.exp (Complex.arg ρ * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I ρ
    rw [hρ] at h
    simpa using h.symm
  conv_lhs => rw [hρ', ← Complex.exp_add]
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := congrArg Complex.im hn
    simp at h
    linear_combination h
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    subst hn
    push_cast
    ring

/-- [proved-derived; formal-checked] The width is the modulus: `log ρ = log |ρ| + i arg ρ`. -/
theorem round_trip_log {ρ : ℂ} {g : ℝ} (hg : ‖ρ‖ = g) :
    Complex.log ρ = (Real.log g : ℂ) + (Complex.arg ρ : ℂ) * Complex.I := by
  subst hg
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]

/-! ## 3. Young's rule: where the pluck sits decides what sounds -/

section Young

open Real

/-- [definition] **The string of `N` cells plucked at cell `a`**: the triangle with its corner at
`a`, at integer heights, `y_j = j (N − a)` up to `a` and `a (N − j)` past it. -/
noncomputable def pluck (N a j : ℕ) : ℝ :=
  if j ≤ a then (j : ℝ) * ((N : ℝ) - a) else (a : ℝ) * ((N : ℝ) - j)

theorem pluck_of_le {N a j : ℕ} (h : j ≤ a) : pluck N a j = (j : ℝ) * ((N : ℝ) - a) := by
  unfold pluck
  exact if_pos h

theorem pluck_of_ge {N a j : ℕ} (h : a ≤ j) : pluck N a j = (a : ℝ) * ((N : ℝ) - j) := by
  unfold pluck
  split_ifs with h'
  · have hj : j = a := le_antisymm h' h
    subst hj
    ring
  · rfl

/-- [proved-derived; formal-checked] **The pluck has one corner**: its second difference is `−N`
at `a` and zero elsewhere. -/
theorem pluck_second_difference (N a i : ℕ) :
    pluck N a (i + 1 + 1) - 2 * pluck N a (i + 1) + pluck N a i =
      if i + 1 = a then -(N : ℝ) else 0 := by
  rcases Nat.lt_or_ge (i + 1) a with h | h
  · rw [pluck_of_le (show i + 1 + 1 ≤ a by omega), pluck_of_le (show i + 1 ≤ a by omega),
      pluck_of_le (show i ≤ a by omega), if_neg (show ¬ (i + 1 = a) by omega)]
    push_cast
    ring
  · rcases h.lt_or_eq with h | h
    · rw [pluck_of_ge (show a ≤ i + 1 + 1 by omega), pluck_of_ge (show a ≤ i + 1 by omega),
        pluck_of_ge (show a ≤ i by omega), if_neg (show ¬ (i + 1 = a) by omega)]
      push_cast
      ring
    · subst h
      rw [pluck_of_ge (show i + 1 ≤ i + 1 + 1 by omega), pluck_of_le (le_refl (i + 1)),
        pluck_of_le (show i ≤ i + 1 by omega), if_pos rfl]
      push_cast
      ring

/-- [definition] **The `n`-th sine mode** of the string of `N` cells: `sin(πnj/N)` at cell `j`. -/
noncomputable def sineMode (N n j : ℕ) : ℝ := Real.sin (π * n * j / N)

/-- [proved-derived; formal-checked] The sine mode's three-term recurrence:
`s_(j+1) + s_(j−1) = 2 cos(πn/N) s_j`. -/
theorem sineMode_recurrence (N n i : ℕ) :
    sineMode N n (i + 1 + 1) + sineMode N n i =
      2 * Real.cos (π * n / N) * sineMode N n (i + 1) := by
  have e1 : π * (n : ℝ) * ((i + 1 + 1 : ℕ) : ℝ) / N =
      π * (n : ℝ) * ((i + 1 : ℕ) : ℝ) / N + π * n / N := by
    push_cast
    ring
  have e2 : π * (n : ℝ) * ((i : ℕ) : ℝ) / N =
      π * (n : ℝ) * ((i + 1 : ℕ) : ℝ) / N - π * n / N := by
    push_cast
    ring
  simp only [sineMode]
  rw [e1, e2, Real.sin_add, Real.sin_sub]
  ring

/-- [proved-derived; formal-checked] **Green's identity for the second difference**: summing
`(Δ²y) s − y (Δ²s)` over the interior telescopes to the boundary. -/
theorem green (y s : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ range M, ((y (i + 1 + 1) - 2 * y (i + 1) + y i) * s (i + 1) -
        y (i + 1) * (s (i + 1 + 1) - 2 * s (i + 1) + s i)) =
      (y (M + 1) * s M - y M * s (M + 1)) - (y 1 * s 0 - y 0 * s 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- [definition] **The `n`-th sine coefficient of the pluck**: `Σ_(0<j<N) y_j sin(πnj/N)`. -/
noncomputable def sineCoefficient (N a n : ℕ) : ℝ :=
  ∑ i ∈ range (N - 1), pluck N a (i + 1) * sineMode N n (i + 1)

/-- [proved-derived; formal-checked] **The coefficient is the corner read by the mode**:
`(2 − 2cos(πn/N)) S_n = N sin(πna/N)`. -/
theorem sineCoefficient_eq {N a : ℕ} (ha : 0 < a) (haN : a < N) (n : ℕ) :
    (2 - 2 * Real.cos (π * n / N)) * sineCoefficient N a n = N * sineMode N n a := by
  have hg := green (pluck N a) (sineMode N n) (N - 1)
  rw [Nat.sub_add_cancel (show 1 ≤ N by omega)] at hg
  have hy0 : pluck N a 0 = 0 := by rw [pluck_of_le (Nat.zero_le a)]; simp
  have hyN : pluck N a N = 0 := by rw [pluck_of_ge haN.le]; simp
  have hs0 : sineMode N n 0 = 0 := by simp [sineMode]
  have hsN : sineMode N n N = 0 := by
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    unfold sineMode
    rw [show π * (n : ℝ) * (N : ℝ) / N = (n : ℝ) * π by
      rw [mul_div_assoc, div_self hN0, mul_one, mul_comm]]
    exact Real.sin_nat_mul_pi n
  rw [hyN, hsN, hy0, hs0] at hg
  have hterm : ∀ i ∈ range (N - 1),
      ((pluck N a (i + 1 + 1) - 2 * pluck N a (i + 1) + pluck N a i) * sineMode N n (i + 1) -
          pluck N a (i + 1) *
            (sineMode N n (i + 1 + 1) - 2 * sineMode N n (i + 1) + sineMode N n i)) =
        (if i + 1 = a then -(N : ℝ) * sineMode N n (i + 1) else 0) -
          (2 * Real.cos (π * n / N) - 2) * (pluck N a (i + 1) * sineMode N n (i + 1)) := by
    intro i _
    rw [pluck_second_difference]
    have hr := sineMode_recurrence N n i
    split_ifs <;> linear_combination (-pluck N a (i + 1)) * hr
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum] at hg
  have hite : ∑ i ∈ range (N - 1), (if i + 1 = a then -(N : ℝ) * sineMode N n (i + 1) else 0) =
      -(N : ℝ) * sineMode N n a := by
    rw [Finset.sum_eq_single (a - 1)]
    · rw [if_pos (show a - 1 + 1 = a by omega), Nat.sub_add_cancel (show 1 ≤ a by omega)]
    · intro b _ hb
      rw [if_neg (show ¬ (b + 1 = a) by omega)]
    · intro h
      exact absurd (Finset.mem_range.mpr (show a - 1 < N - 1 by omega)) h
  rw [hite] at hg
  unfold sineCoefficient
  linear_combination hg

/-- [proved-derived; formal-checked] **Young's rule**: for `0 < a < N` and `0 < n < N`, the `n`-th
sine coefficient of the string plucked at `a/N` vanishes iff `N ∣ na`. -/
theorem young {N a n : ℕ} (ha : 0 < a) (haN : a < N) (hn : 0 < n) (hnN : n < N) :
    sineCoefficient N a n = 0 ↔ N ∣ n * a := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0 : (N : ℝ) ≠ 0 := hN.ne'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ0 : 0 < π * n / N := div_pos (mul_pos Real.pi_pos hn') hN
  have hθπ : π * n / N < π := by
    rw [div_lt_iff₀ hN]
    have h' : (n : ℝ) < N := by exact_mod_cast hnN
    exact mul_lt_mul_of_pos_left h' Real.pi_pos
  have hcos : Real.cos (π * n / N) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθπ.le hθ0
    rwa [Real.cos_zero] at h
  have hc : 2 - 2 * Real.cos (π * n / N) ≠ 0 := by linarith
  have key := sineCoefficient_eq ha haN n
  constructor
  · intro h
    rw [h, mul_zero] at key
    have hs : sineMode N n a = 0 := (mul_eq_zero.mp key.symm).resolve_left hN0
    unfold sineMode at hs
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
    have h3 : (k : ℝ) * π * N = π * n * a := by
      rw [hk, div_mul_cancel₀ _ hN0]
    have h4 : (k : ℝ) * N = n * a := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      linear_combination h3
    have h5 : k * (N : ℤ) = (n : ℤ) * a := by exact_mod_cast h4
    have h6 : (N : ℤ) ∣ ((n * a : ℕ) : ℤ) := by
      push_cast
      exact Dvd.intro_left k h5
    exact Int.natCast_dvd_natCast.mp h6
  · rintro ⟨q, hq⟩
    have hs : sineMode N n a = 0 := by
      unfold sineMode
      have hq' : (n : ℝ) * a = N * q := by exact_mod_cast hq
      have he : π * (n : ℝ) * a / N = (q : ℝ) * π := by
        field_simp
        linear_combination π * hq'
      rw [he]
      exact Real.sin_nat_mul_pi q
    rw [hs, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_left hc

/-- [proved-derived; formal-checked] The receipt's string of 16 cells: the pluck at `a = 8`
silences the even harmonics, at `a = 4` the multiples of 4, and at `a = 3` or `5` nothing. -/
theorem young_sixteen :
    ∀ n < 16, 0 < n →
      ((16 ∣ n * 8 ↔ 2 ∣ n) ∧ (16 ∣ n * 4 ↔ 4 ∣ n) ∧ ¬ 16 ∣ n * 3 ∧ ¬ 16 ∣ n * 5) := by
  decide

end Young

/-! ## 4. The sum of all round trips -/

section RoundTrips

/-- [proved-derived; formal-checked] **The remainder after `m` trips**:
`Σ_(j<m) ρʲ − 1/(1 − ρ) = −ρᵐ/(1 − ρ)`. -/
theorem round_trip_remainder {K : Type*} [Field K] {ρ : K} (h : ρ ≠ 1) (m : ℕ) :
    ∑ j ∈ range m, ρ ^ j - 1 / (1 - ρ) = -ρ ^ m / (1 - ρ) := by
  have h1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr h
  have h2 : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [geom_sum_eq h, div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h2]
  ring

/-- [proved-derived; formal-checked] **The Poisson kernel**:
`Re((1 + ρ)/(1 − ρ)) = (1 − |ρ|²)/|1 − ρ|²`. -/
theorem poisson_kernel (ρ : ℂ) :
    ((1 + ρ) / (1 - ρ)).re = (1 - Complex.normSq ρ) / Complex.normSq (1 - ρ) := by
  rw [Complex.div_re, Complex.normSq_apply ρ]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im, Complex.sub_im,
    Complex.one_im]
  ring

/-- [proved-standard; formal-checked] **The answer is the sum of all echoes**: for `|ρ| < 1`,
`Σ_(j≥0) ρʲ = 1/(1 − ρ)`. -/
theorem round_trip_sum {ρ : ℂ} (h : ‖ρ‖ < 1) : HasSum (fun j : ℕ => ρ ^ j) (1 - ρ)⁻¹ :=
  hasSum_geometric_of_norm_lt_one h

/-- [proved-derived; formal-checked] The `m`-th echo adds only `g^m`: `|ρᵐ|² = (|ρ|²)ᵐ`. -/
theorem round_trip_gain (ρ : ℂ) (m : ℕ) : Complex.normSq (ρ ^ m) = Complex.normSq ρ ^ m :=
  map_pow Complex.normSq ρ m

/-- [proved-derived; formal-checked] For `ρ = g e^(iφ)`, `|1 − ρ|² = (1 − g)² + 4g sin²(φ/2)`. -/
theorem normSq_one_sub (g φ : ℝ) :
    Complex.normSq (1 - g * Complex.exp (φ * Complex.I)) =
      (1 - g) ^ 2 + 4 * g * Real.sin (φ / 2) ^ 2 := by
  have hc : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have h := Real.cos_two_mul (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    rw [h, Real.cos_sq']
    ring
  have hs := Real.sin_sq_add_cos_sq φ
  rw [Complex.normSq_apply]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination g ^ 2 * hs + (-2 * g) * hc

/-- [proved-derived; formal-checked] **The Doppler factor at resonance**: the Poisson reading
`(1 − g²)/|1 − ρ|²` is `k = (1 + g)/(1 − g)` at `ρ = g` and `1/k` at `ρ = −g`. -/
theorem poisson_doppler {g : ℝ} (h₁ : 1 - g ≠ 0) (h₂ : 1 + g ≠ 0) :
    (1 - g ^ 2) / (1 - g) ^ 2 = (1 + g) / (1 - g) ∧
      (1 - g ^ 2) / (1 + g) ^ 2 = 1 / ((1 + g) / (1 - g)) := by
  constructor
  · rw [div_eq_div_iff (pow_ne_zero 2 h₁) h₁]
    ring
  · rw [one_div_div, div_eq_div_iff (pow_ne_zero 2 h₂) h₂]
    ring

/-- [proved-derived; formal-checked] The receipt's factors: `k = 3, 15, 199` for
`g = 1/2, 7/8, 99/100`. -/
theorem poisson_doppler_instances :
    (1 + (1 / 2 : ℚ)) / (1 - 1 / 2) = 3 ∧ (1 + (7 / 8 : ℚ)) / (1 - 7 / 8) = 15 ∧
      (1 + (99 / 100 : ℚ)) / (1 - 99 / 100) = 199 := by
  norm_num

/-- [proved-derived; formal-checked] **Half power**: the Airy reading
`(1 − g)²/((1 − g)² + 4gs)` is `1/2` exactly at `s = (1 − g)²/(4g)`. -/
theorem half_power {g s : ℝ} (hg : 0 < g) (hg1 : g ≠ 1) (hs : 0 ≤ s) :
    (1 - g) ^ 2 / ((1 - g) ^ 2 + 4 * g * s) = 1 / 2 ↔ s = (1 - g) ^ 2 / (4 * g) := by
  have h1 : 0 < (1 - g) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hg1))))
  have h4 : 0 ≤ 4 * g * s := mul_nonneg (mul_nonneg (by norm_num) hg.le) hs
  have hd : (1 - g) ^ 2 + 4 * g * s ≠ 0 := (add_pos_of_pos_of_nonneg h1 h4).ne'
  rw [div_eq_div_iff hd two_ne_zero, eq_div_iff (mul_ne_zero four_ne_zero hg.ne')]
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

/-- [proved-derived; formal-checked] **Fabry–Pérot**: the Airy reading is the Poisson reading
over `k`, `(1 − g)²/D = ((1 − g²)/D) / ((1 + g)/(1 − g))`. -/
theorem airy_eq_poisson_div {g D : ℝ} (h₁ : 1 - g ≠ 0) (h₂ : 1 + g ≠ 0) (hD : D ≠ 0) :
    (1 - g) ^ 2 / D = (1 - g ^ 2) / D / ((1 + g) / (1 - g)) := by
  rw [div_div_div_eq, div_eq_div_iff hD (mul_ne_zero hD h₂)]
  ring

end RoundTrips

/-! ## 5. The plasma shell and its rest frame -/

section Plasma

variable {K : Type*} [Field K]

/-- [proved-derived; formal-checked] **The plasma shell is an interval**: `ω² = ω_p² + c²k²` is
`(ω − ck)(ω + ck) = ω_p²`, the interval `uv` of the wave's light-cone components. -/
theorem plasma_shell {ω ck ωp : K} (h : ω ^ 2 = ωp ^ 2 + ck ^ 2) :
    interval (⟨ω - ck, ω + ck⟩ : LightCone K) = ωp ^ 2 := by
  simp only [interval]
  linear_combination h

/-- [proved-derived; formal-checked] **The boost to rest**: the boost of Doppler ratio `κ` with
`κ²(ω − ck) = ω + ck` carries the wave to `u′ = v′` (no momentum), its component squared is the
interval `(ω − ck)(ω + ck)`, the rest frequency squared, and the frame moves at `β(κ) = ck/ω`. -/
theorem plasma_rest [CharZero K] {κ ω ck : K} (hκ : κ ≠ 0) (hω : ω ≠ 0)
    (hkk : κ ^ 2 * (ω - ck) = ω + ck) :
    (boost κ ⟨ω - ck, ω + ck⟩).u = (boost κ ⟨ω - ck, ω + ck⟩).v ∧
      (boost κ ⟨ω - ck, ω + ck⟩).u ^ 2 = (ω - ck) * (ω + ck) ∧
      betaOf κ = ck / ω := by
  have h1 : κ ^ 2 + 1 ≠ 0 := by
    intro h
    have h2 : (2 : K) * ω = 0 := by linear_combination -hkk + (ω - ck) * h
    exact hω ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
  refine ⟨?_, ?_, ?_⟩
  · simp only [boost]
    rw [← hkk]
    field_simp <;> ring
  · simp only [boost]
    linear_combination (ω - ck) * hkk
  · unfold betaOf
    rw [div_eq_div_iff h1 hω]
    linear_combination hkk

/-- [proved-derived; formal-checked] The receipt's instance: for `(ω, ck) = (5, 4)` the boost of
ratio 3 brings `(u, v) = (1, 9)` to rest at frequency 3, at velocity `4/5`. -/
theorem plasma_rest_instance :
    boost (3 : ℚ) ⟨5 - 4, 5 + 4⟩ = ⟨3, 3⟩ ∧ betaOf (3 : ℚ) = 4 / 5 := by
  constructor
  · ext <;> norm_num [boost]
  · norm_num [betaOf]

end Plasma

/-! ## 6. The beat is the slip -/

section Beat

variable {K : Type*} [Field K]

/-- The slip of the pair contact `J = [f₁ | −f₂]` of two tones at the harmonic pair `(n, m)`: the
beat `n f₁ − m f₂`. -/
def slip (f₁ f₂ n m : K) : K := n * f₁ - m * f₂

/-- [proved-derived; formal-checked] The slip is the contact `[f₁ | −f₂]` applied to `(n, m)`. -/
theorem slip_contact (f₁ f₂ n m : K) : slip f₁ f₂ n m = n * f₁ + m * -f₂ := by
  unfold slip
  ring

/-- [proved-derived; formal-checked] **Zero beat is the lock**: the slip at `(q, p)` vanishes
exactly when `q f₁ = p f₂`, the Farey address `p/q`. -/
theorem slip_eq_zero_iff {f₁ f₂ q p : K} : slip f₁ f₂ q p = 0 ↔ q * f₁ = p * f₂ := by
  unfold slip
  exact sub_eq_zero

/-- [proved-derived; formal-checked] **The fifth tuned by ear**: zeroing the lower note's third
harmonic against the upper note's second sets `f₂/f₁ = 3/2`. -/
theorem fifth_lock [CharZero K] {f₁ f₂ : K} (hf : f₁ ≠ 0) :
    slip f₁ f₂ 3 2 = 0 ↔ f₂ / f₁ = 3 / 2 := by
  rw [slip_eq_zero_iff, div_eq_div_iff hf two_ne_zero]
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

/-- [proved-derived; formal-checked] **Equal temperament leaves every fifth a slow beat**: a ratio
`r` with `r¹² = 2⁷` is never `3/2` (the Pythagorean comma `3¹²/2¹⁹ ≠ 1`), so the slip of the
tempered fifth never vanishes. -/
theorem tempered_fifth_beats {r f : ℝ} (hr : r ^ 12 = 2 ^ 7) (hf : f ≠ 0) :
    slip f (r * f) 3 2 ≠ 0 := by
  intro h
  rw [slip_eq_zero_iff] at h
  have h3 : r = 3 / 2 := by
    have h' : (3 - 2 * r) * f = 0 := by linear_combination h
    have h'' := (mul_eq_zero.mp h').resolve_right hf
    linarith
  rw [h3] at hr
  norm_num at hr

end Beat

end Holonics.Physics.Spacetime.Echo
