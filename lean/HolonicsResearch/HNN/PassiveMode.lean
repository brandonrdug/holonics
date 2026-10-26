import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The passive mode's bound: a push scaled by `√(1 − ρ²)` never lifts a mode past `√((1 + ρ)/(1 − ρ))`

The moment tower's mode moves as `h_t = λ_t h′_(t−1) + γ_t B x_t` with `γ_t = √(1 − |λ_t|²)`
(`research/records/2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO.md`,
§Owed). The ungated tower holds `|λ_t| = |λ|`; the gated tower moves the radius, `ρ_t ≤ ρ_max < 1`;
the rotor tower first hands each mode one mode's state, `h′_(t−1) = P^σ h_(t−1)`
(`research/records/2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`,
§11 and #410 (i)). One bound covers the three.

[proved-standard; formal-checked] What is proved.

1. **The margin** (`passive_margin`): for `0 ≤ ρ ≤ ρ_max < 1` and `K = √((1 + ρ_max)/(1 − ρ_max))`,
   `ρ K + √(1 − ρ²) ≤ K`. Equivalently `√(1 − ρ²)/(1 − ρ) = √((1 + ρ)/(1 − ρ))` increases with `ρ`,
   so a slower decay is paid for by a smaller push.
2. **One step keeps the bound** (`passive_step`): if `|h′| ≤ K M`, `|u| ≤ M` and `|a| = ρ`, then
   `|a h′ + √(1 − ρ²) u| ≤ K M`.
3. **The bound holds along every passage** (`passive_recursion`): for modes `h_t : ι → ℂ`, any
   hand-over `σ_t : ι → ι` (a permutation is the rotor's case, the identity the plain tower's), any
   turns `a_t` with `|a_t| ≤ ρ_max < 1` and pushes `|u_t| ≤ M`, if
   `h_(t+1)(j) = a_t(j)·h_t(σ_t(j)) + √(1 − |a_t(j)|²)·u_t(j)` and the start is within `K M`, then
   every `|h_t(j)| ≤ K M`. With `ρ_max = |λ|` it is the ungated tower's bound
   `|h| ≤ √((1 + |λ|)/(1 − |λ|)) max|Bx|`; with a moving radius it is the gated tower's; with a
   permutation it is the rotor's, which therefore keeps the passivity bound unchanged.

Consumers: the atlas rows `hnn.moment-tower`, `hnn.tower-gated-mode` and `hnn.tower-rotor`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.PassiveMode

open Complex

/-- [definition] The passive bound's factor `K(ρ) = √((1 + ρ)/(1 − ρ))`. -/
noncomputable def passiveBound (ρ : ℝ) : ℝ := Real.sqrt ((1 + ρ) / (1 - ρ))

/-- [proved-standard; formal-checked] **The margin:** `ρ K(ρ_max) + √(1 − ρ²) ≤ K(ρ_max)` for
`0 ≤ ρ ≤ ρ_max < 1`. -/
theorem passive_margin {ρ ρmax : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρmax) (hmax : ρmax < 1) :
    ρ * passiveBound ρmax + Real.sqrt (1 - ρ ^ 2) ≤ passiveBound ρmax := by
  have h1 : 0 < 1 - ρmax := by linarith
  have hρ1 : 0 ≤ 1 - ρ := by linarith
  have key : Real.sqrt (1 - ρ ^ 2) ≤ passiveBound ρmax * (1 - ρ) := by
    rw [passiveBound, ← Real.sqrt_sq hρ1,
      ← Real.sqrt_mul (div_nonneg (show (0 : ℝ) ≤ 1 + ρmax by linarith) h1.le)]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div, le_div_iff₀ h1]
    nlinarith [mul_nonneg hρ1 (sub_nonneg.2 h)]
  have hsplit : passiveBound ρmax * (1 - ρ) = passiveBound ρmax - ρ * passiveBound ρmax := by ring
  linarith

/-- [proved-standard; formal-checked] **One step keeps the bound:** a turn of modulus `ρ` and a push
scaled by `√(1 − ρ²)` keep a mode within `K(ρ_max)·M`. -/
theorem passive_step {ρ ρmax M : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρmax) (hmax : ρmax < 1) (hM : 0 ≤ M)
    {a h' u : ℂ} (ha : ‖a‖ = ρ) (hh : ‖h'‖ ≤ passiveBound ρmax * M) (hu : ‖u‖ ≤ M) :
    ‖a * h' + (Real.sqrt (1 - ρ ^ 2) : ℂ) * u‖ ≤ passiveBound ρmax * M := by
  have hs : 0 ≤ Real.sqrt (1 - ρ ^ 2) := Real.sqrt_nonneg _
  calc ‖a * h' + (Real.sqrt (1 - ρ ^ 2) : ℂ) * u‖
      ≤ ‖a * h'‖ + ‖(Real.sqrt (1 - ρ ^ 2) : ℂ) * u‖ := norm_add_le _ _
    _ = ρ * ‖h'‖ + Real.sqrt (1 - ρ ^ 2) * ‖u‖ := by
        rw [norm_mul, norm_mul, ha, Complex.norm_real, Real.norm_of_nonneg hs]
    _ ≤ ρ * (passiveBound ρmax * M) + Real.sqrt (1 - ρ ^ 2) * M :=
        add_le_add (mul_le_mul_of_nonneg_left hh h0) (mul_le_mul_of_nonneg_left hu hs)
    _ = (ρ * passiveBound ρmax + Real.sqrt (1 - ρ ^ 2)) * M := by ring
    _ ≤ passiveBound ρmax * M :=
        mul_le_mul_of_nonneg_right (passive_margin h0 h hmax) hM

/-- [proved-standard; formal-checked] **The bound holds along every passage:** whatever mode each
mode is handed (`σ_t`), whatever turns of modulus at most `ρ_max < 1` and pushes of size at most `M`
arrive, every mode stays within `K(ρ_max)·M` once it starts there. -/
theorem passive_recursion {ι : Type*} {ρmax M : ℝ} (hmax : ρmax < 1) (hM : 0 ≤ M)
    (h : ℕ → ι → ℂ) (a : ℕ → ι → ℂ) (σ : ℕ → ι → ι) (u : ℕ → ι → ℂ)
    (ha : ∀ t j, ‖a t j‖ ≤ ρmax) (hu : ∀ t j, ‖u t j‖ ≤ M)
    (hstep : ∀ t j, h (t + 1) j =
      a t j * h t (σ t j) + (Real.sqrt (1 - ‖a t j‖ ^ 2) : ℂ) * u t j)
    (h0 : ∀ j, ‖h 0 j‖ ≤ passiveBound ρmax * M) :
    ∀ t j, ‖h t j‖ ≤ passiveBound ρmax * M := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro j
    rw [hstep]
    exact passive_step (norm_nonneg _) (ha t j) hmax hM rfl (ih (σ t j)) (hu t j)

/-- [proved-standard; formal-checked] **A mode started at rest stays within the bound:** the
tower's founding state `h_0 = 0` is within it. -/
theorem passive_from_rest {ι : Type*} {ρmax M : ℝ} (hmax : ρmax < 1) (hM : 0 ≤ M)
    (h : ℕ → ι → ℂ) (a : ℕ → ι → ℂ) (σ : ℕ → ι → ι) (u : ℕ → ι → ℂ)
    (ha : ∀ t j, ‖a t j‖ ≤ ρmax) (hu : ∀ t j, ‖u t j‖ ≤ M)
    (hstep : ∀ t j, h (t + 1) j =
      a t j * h t (σ t j) + (Real.sqrt (1 - ‖a t j‖ ^ 2) : ℂ) * u t j)
    (hrest : ∀ j, h 0 j = 0) :
    ∀ t j, ‖h t j‖ ≤ passiveBound ρmax * M :=
  passive_recursion hmax hM h a σ u ha hu hstep fun j => by
    rw [hrest, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) hM

end Holonics.HNN.PassiveMode
