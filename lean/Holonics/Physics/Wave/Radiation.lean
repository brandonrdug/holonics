import Holonics.Physics.Wave.Telegrapher

/-!
# Radiation is the change: a stationary configuration emits nothing

[definition] Rebuild step 6, K3 (#74), battle test 2, and the light-is-change record §1: a charge
in uniform motion radiates nothing, and only its change is seen far away. On the LC chain of
`Physics/Wave/Telegrapher` a source current enters node `0` on a schedule `src`. A configuration
is **stationary** under a constant source value when one tick returns it (`Stationary`). What a
distant receiver at node `w` reads is the chain's state there; what it can detect is its
**change**.

[proved-derived; formal-checked] What is proved, exactly over `ℚ`, for every material.

1. **A stationary configuration emits nothing** (`stationary_emits_nothing`), by construction:
   `Stationary` is the one-tick fixed point, and iterating it returns the configuration at every
   tick, so no node reads any change. The content is items 2–5.
2. **The radiated field is the propagated change of the source** (`radiation_is_the_change`): the
   deviation of the run from a stationary configuration is exactly the zero-state response of the
   chain to the source's deviation `src − s̄`. The bound part (the stationary configuration) is
   carried along; only the change propagates.
3. **The change travels in its cone** (`response_silent_before`, `response_cone`): until the
   source first changes at tick `n₀` the response is zero, and `w` ticks after that first
   injection it is supported in `[−w, w]`.
4. **The receiver reads exactly the change** (`receiver_reads_the_change`): on a positive uniform
   chain a receiver at node `w` reads nothing through tick `n₀ + w`, and at tick `n₀ + 1 + w` it
   reads `(gain · coupling)ʷ · gain · δ(n₀)` (`response_front`), nonzero exactly when the source
   changed.
5. **Uniform motion radiates nothing** (`uniform_current_stationary`): a uniform current with no
   voltage, the chain's charge in uniform motion, is stationary under a silent source for every
   material.

No `axiom`, no `sorry`.
-/

namespace Holonics.Physics.Wave.Radiation

open Holonics.Physics.Wave.Telegrapher

/-- [definition] **A stationary configuration** under the constant source value `s`. -/
def Stationary (m : Material) (h s : ℚ) (x : State) : Prop := step m h s x = x

theorem state_sub_self (x : State) : x - x = 0 := by ext i <;> simp

theorem zero_supported (lo hi : ℤ) : Supported lo hi (0 : State) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- [proved-derived; formal-checked] **A stationary configuration emits nothing**, by
construction: `Stationary` is the one-tick fixed point, iterated over the run. -/
theorem stationary_emits_nothing {m : Material} {h s : ℚ} {x : State} (hx : Stationary m h s x)
    (src : ℕ → ℚ) (hsrc : ∀ n, src n = s) (n : ℕ) : run m h src x n = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, hsrc]; exact hx

/-- [proved-derived; formal-checked] **The radiated field is the propagated change of the
source**: the deviation from a stationary configuration is the zero-state response to
`src − s`. -/
theorem radiation_is_the_change {m : Material} {h s : ℚ} {x : State} (hx : Stationary m h s x)
    (src : ℕ → ℚ) (n : ℕ) :
    run m h src x n - x = run m h (fun k => src k - s) 0 n := by
  have hconst := stationary_emits_nothing hx (fun _ => s) (fun _ => rfl) n
  calc run m h src x n - x = run m h src x n - run m h (fun _ => s) x n := by rw [hconst]
    _ = run m h (src - fun _ => s) (x - x) n := run_sub m h _ _ _ _ n
    _ = run m h (fun k => src k - s) 0 n := by rw [state_sub_self]; rfl

/-- [proved-derived; formal-checked] **Silent until the change**: a source deviation that is zero
before tick `n₀` leaves the zero state untouched through tick `n₀`. -/
theorem response_silent_before {m : Material} {h : ℚ} {δ : ℕ → ℚ} {n₀ : ℕ}
    (hδ : ∀ k < n₀, δ k = 0) : ∀ n ≤ n₀, run m h δ 0 n = 0 := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, ih (by omega), hδ n (by omega)]
    ext i
    · simp [step, currentStep, inject]
    · simp [step, currentStep]

/-- [proved-derived; formal-checked] **The change travels in its cone**: `w` ticks after the
first injection at tick `n₀`, the response is supported in `[−w, w]`. -/
theorem response_cone {m : Material} {h : ℚ} {δ : ℕ → ℚ} {n₀ : ℕ} (hδ : ∀ k < n₀, δ k = 0)
    (w : ℕ) : Supported (-w) w (run m h δ 0 (n₀ + 1 + w)) := by
  induction w with
  | zero =>
    rw [add_zero, run_succ, response_silent_before hδ n₀ le_rfl]
    simpa using step_supported (m := m) (h := h) (s := δ n₀) (zero_supported 1 (-1))
      (Or.inr ⟨le_rfl, le_rfl⟩)
  | succ w ih =>
    rw [show n₀ + 1 + (w + 1) = (n₀ + 1 + w) + 1 by ring, run_succ]
    have := step_supported (m := m) (h := h) (s := δ (n₀ + 1 + w)) ih
      (Or.inr ⟨by omega, by omega⟩)
    push_cast
    rw [show -((w : ℤ) + 1) = -(w : ℤ) - 1 by ring]
    exact this

/-- [proved-derived; formal-checked] **The front of the change** on a uniform chain: at tick
`n₀ + 1 + w` node `w` reads `(gain · coupling)ʷ · gain · δ(n₀)`. -/
theorem response_front {C G L h : ℚ} {δ : ℕ → ℚ} {n₀ : ℕ} (hδ : ∀ k < n₀, δ k = 0) (w : ℕ) :
    (run (Material.uniform C G L) h δ 0 (n₀ + 1 + w)).V w =
      frontFactor (Material.uniform C G L) h 0 0 ^ w *
        (gain (Material.uniform C G L) h 0 * δ n₀) := by
  induction w with
  | zero =>
    rw [add_zero, run_succ, response_silent_before hδ n₀ le_rfl]
    simp [step, currentStep, inject]
  | succ w ih =>
    rw [show n₀ + 1 + (w + 1) = (n₀ + 1 + w) + 1 by ring, run_succ]
    have := step_front_right (m := Material.uniform C G L) (h := h) (s := δ (n₀ + 1 + w))
      (response_cone (m := Material.uniform C G L) (h := h) hδ w) (by positivity)
    push_cast
    rw [this, ih, pow_succ]
    simp only [frontFactor, gain, coupling, Material.uniform]
    ring

/-- [proved-derived; formal-checked] **The receiver reads exactly the change.** On a positive
uniform chain a receiver at node `w` reads nothing through tick `n₀ + w`; at tick `n₀ + 1 + w`
its reading is nonzero exactly when the source changed at tick `n₀`. -/
theorem receiver_reads_the_change {C G L h : ℚ} (hC : 0 < C) (hL : 0 < L) (hh : 0 < h)
    (hG : 0 ≤ G) {δ : ℕ → ℚ} {n₀ : ℕ} (hδ : ∀ k < n₀, δ k = 0) (w : ℕ) :
    (∀ n ≤ n₀ + w, (run (Material.uniform C G L) h δ 0 n).V w = 0) ∧
      ((run (Material.uniform C G L) h δ 0 (n₀ + 1 + w)).V w ≠ 0 ↔ δ n₀ ≠ 0) := by
  constructor
  · intro n hn
    rcases le_or_gt n n₀ with hle | hlt
    · rw [response_silent_before hδ n hle]; rfl
    · obtain ⟨w', rfl⟩ : ∃ w', n = n₀ + 1 + w' := ⟨n - n₀ - 1, by omega⟩
      exact (response_cone hδ w').1 w (Or.inr (by omega))
  · rw [response_front hδ w]
    have hff := frontFactor_ne_zero hC hL hh hG 0 0
    have hg : gain (Material.uniform C G L) h 0 ≠ 0 := by
      simp only [gain, Material.uniform]
      have : 0 < 2 * C + h * G := by positivity
      positivity
    constructor
    · intro hne h0; rw [h0, mul_zero, mul_zero] at hne; exact hne rfl
    · intro hne; exact mul_ne_zero (pow_ne_zero _ hff) (mul_ne_zero hg hne)

/-- [proved-derived; formal-checked] **Uniform motion radiates nothing**: a uniform current with
no voltage is stationary under a silent source, for every material. -/
theorem uniform_current_stationary (m : Material) (h c : ℚ) :
    Stationary m h 0 ⟨0, fun _ => c⟩ := by
  ext i
  · simp [step, currentStep, inject]
  · simp [step, currentStep]

section Audit

#print axioms stationary_emits_nothing
#print axioms radiation_is_the_change
#print axioms response_cone
#print axioms receiver_reads_the_change
#print axioms uniform_current_stationary

end Audit

end Holonics.Physics.Wave.Radiation
