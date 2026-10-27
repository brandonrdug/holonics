import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# The passage credit: a mode's carried moments are its derivatives over the whole passage

The record `research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY.md`
("The passage credit", atlas `hnn.tower-passage-credit`) carries a mode's derivative moments
forward over the passage (`hnn::tower::{LevelCredit, TowerState::rest_with_credit}`). For a mode
`h_t = λ_t h_(t−1) + γ_t B x_t`, the push row's moments are
`P_T = (λ_(T−1) ⋯ λ_0) P_0 + Σ_s π_s γ_s x_s`, `π_s = λ_(T−1) ⋯ λ_(s+1)`, and the gate's are
`W_T = (λ_(T−1) ⋯ λ_0) W_0 + Σ_s π_s d_s x_s`; a section's covector is paired with them at its
opening. #410 owes that these moments are the derivatives of the state over the whole passage, so
the pairing gives the passage's covector (`the_opening_credit_completes_the_passage_covector`
checks it in Rust). This file proves it.

The mode lives in any normed `ℝ`-algebra `𝔸` (`ℂ` for a ring's mode, a matrix algebra for a coupled
bank); the moves are multiplied on the left in order, so nothing assumes they commute. A parameter
is read along one real line `x`: the move `λ_t(x)`, the drive `u_t(x)` (`γ_t B x_t` for the push
row) and the opening `h_0(x)` all depend on it, which covers the push row (the move fixed) and the
gate (the move and the push both keyed) alike.

[proved-derived; formal-checked] What is proved.

1. **The moments are the derivatives** (`hasDerivAt_state`): the moments carried by
   `P_(t+1) = λ_t P_t + d_t` from `P_0 = h_0'` with the step's own source `d_t = λ_t' h_t + u_t'`
   (`source`) are the derivatives of the state, `d h_T/dx = P_T`, over the whole passage. For the
   push row the move is fixed and `d_t = u_t'` (`source_of_fixed_move`).
2. **Their closed form** (`carried_eq_sum`): from an opening `P` at step `m`,
   `P_(m+n) = (λ_(m+n−1) ⋯ λ_m) P + Σ_(k<n) (λ_(m+n−1) ⋯ λ_(m+k+1)) d_(m+k)` (`carry`), the record's
   `P_T` and `W_T` at `m = 0`.
3. **The credit** (`carried_add`, `carried_opening`): the moments of a passage are those of its
   second section opened on the first's carried moments, and a section opened on a credit `P`
   carries the transport of `P` beside its own moments from rest.
4. **The passage's covector** (`hasDerivAt_passage`, `passage_covector_split`): for readings
   `ℓ_t` of the state with derivatives `G_t`, the passage's code `Σ_t ℓ_t(h_t)` has derivative
   `Σ_t G_t(P_t)`, and over a passage split at `m` this is the first section's covector, plus the
   second section's from rest, plus the second section's covector at its opening
   (`openingCovector`, each later reading carried back through the transport) paired with the
   carried moments `P_m`. Without the credit the second section misses exactly that pairing.

The computational object is the helical pair interaction's ring: a mode is a parametron ring
stepped by its move each cell, and its moments are the ring's derivative carried with the stream.
Of the winding guide's six general objects this touches the tube (the passage as one clocked span
cut into sections and glued at an opening); the helix, the pair, faces and placement, the cell
holonomy and the tower thread stay attached.

Consumers: the atlas row `hnn.tower-passage-credit` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.PassageCredit

open Finset

/-! ## 1. The carried moments and their transport -/

section Moments

variable {𝔸 : Type*} [Ring 𝔸]

/-- [definition] The moments carried from an opening `P` at step `m`, `n` steps on:
`P ← λ_(m+i) P + d_(m+i)`. -/
def carried (lam d : ℕ → 𝔸) (m : ℕ) (P : 𝔸) : ℕ → 𝔸
  | 0 => P
  | n + 1 => lam (m + n) * carried lam d m P n + d (m + n)

/-- [definition] The transport over `n` steps from step `m`, `λ_(m+n−1) ⋯ λ_m`. -/
def carry (lam : ℕ → 𝔸) (m : ℕ) : ℕ → 𝔸
  | 0 => 1
  | n + 1 => lam (m + n) * carry lam m n

theorem carried_zero (lam d : ℕ → 𝔸) (m : ℕ) (P : 𝔸) : carried lam d m P 0 = P := rfl

theorem carried_succ (lam d : ℕ → 𝔸) (m : ℕ) (P : 𝔸) (n : ℕ) :
    carried lam d m P (n + 1) = lam (m + n) * carried lam d m P n + d (m + n) := rfl

theorem carry_zero (lam : ℕ → 𝔸) (m : ℕ) : carry lam m 0 = 1 := rfl

theorem carry_succ (lam : ℕ → 𝔸) (m n : ℕ) :
    carry lam m (n + 1) = lam (m + n) * carry lam m n := rfl

/-- [proved-derived; formal-checked] **The closed form**: from an opening `P` at step `m`,
`P_(m+n) = (λ_(m+n−1) ⋯ λ_m) P + Σ_(k<n) (λ_(m+n−1) ⋯ λ_(m+k+1)) d_(m+k)`. -/
theorem carried_eq_sum (lam d : ℕ → 𝔸) (m : ℕ) (P : 𝔸) (n : ℕ) :
    carried lam d m P n =
      carry lam m n * P + ∑ k ∈ range n, carry lam (m + k + 1) (n - 1 - k) * d (m + k) := by
  induction n with
  | zero => simp [carried_zero, carry_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, carried_succ, carry_succ, ih, mul_add, Finset.mul_sum,
      ← mul_assoc]
    have hlast : n + 1 - 1 - n = 0 := by omega
    rw [hlast, carry_zero, one_mul]
    have hsum : ∑ k ∈ range n, lam (m + n) * (carry lam (m + k + 1) (n - 1 - k) * d (m + k)) =
        ∑ k ∈ range n, carry lam (m + k + 1) (n + 1 - 1 - k) * d (m + k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < n := Finset.mem_range.1 hk
      have e1 : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      have e2 : m + k + 1 + (n - 1 - k) = m + n := by omega
      rw [e1, carry_succ, e2, mul_assoc]
    rw [hsum]
    abel

/-- [proved-derived; formal-checked] **The credit**: the moments of a passage are those of its
second section opened on the first section's carried moments. -/
theorem carried_add (lam d : ℕ → 𝔸) (j : ℕ) (P : 𝔸) (m n : ℕ) :
    carried lam d j P (m + n) = carried lam d (j + m) (carried lam d j P m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, carried_succ, carried_succ, ih, Nat.add_assoc]

/-- [proved-derived; formal-checked] **A section opened on a credit** carries the transport of the
credit beside its own moments from rest. -/
theorem carried_opening (lam d : ℕ → 𝔸) (m : ℕ) (P : 𝔸) (n : ℕ) :
    carried lam d m P n = carried lam d m 0 n + carry lam m n * P := by
  induction n with
  | zero => simp [carried_zero, carry_zero]
  | succ n ih =>
    rw [carried_succ, carried_succ, carry_succ, ih, mul_add, ← mul_assoc]
    abel

end Moments

/-! ## 2. The moments are the derivatives over the passage -/

section Passage

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- [definition] The mode's passage along a parameter line: `h_0 = h_0(x)`,
`h_(t+1) = λ_t(x) h_t + u_t(x)`. -/
def state (lam u : ℕ → ℝ → 𝔸) (h0 : ℝ → 𝔸) (x : ℝ) : ℕ → 𝔸
  | 0 => h0 x
  | t + 1 => lam t x * state lam u h0 x t + u t x

/-- [definition] The step's own source at `x0`, `d_t = λ_t' h_t + u_t'`: the move's derivative
acting on the state it meets, beside the drive's. -/
def source (lam u : ℕ → ℝ → 𝔸) (h0 : ℝ → 𝔸) (lam' u' : ℕ → 𝔸) (x0 : ℝ) (t : ℕ) : 𝔸 :=
  lam' t * state lam u h0 x0 t + u' t

/-- [proved-derived; formal-checked] For the push row the move is fixed, and the source is the
drive's derivative, `γ_t x_t` for `u_t = γ_t B x_t`. -/
theorem source_of_fixed_move (lam u : ℕ → ℝ → 𝔸) (h0 : ℝ → 𝔸) (lam' u' : ℕ → 𝔸) (x0 : ℝ)
    (hfixed : ∀ t, lam' t = 0) (t : ℕ) : source lam u h0 lam' u' x0 t = u' t := by
  simp [source, hfixed]

/-- [proved-derived; formal-checked] **The moments are the derivatives**: carried from
`P_0 = h_0'` with the source `d_t = λ_t' h_t + u_t'`, the moments are `d h_T/dx` over the whole
passage. -/
theorem hasDerivAt_state {lam u : ℕ → ℝ → 𝔸} {h0 : ℝ → 𝔸} {lam' u' : ℕ → 𝔸} {P0 : 𝔸} {x0 : ℝ}
    (hlam : ∀ t, HasDerivAt (lam t) (lam' t) x0) (hu : ∀ t, HasDerivAt (u t) (u' t) x0)
    (hh0 : HasDerivAt h0 P0 x0) (T : ℕ) :
    HasDerivAt (fun x => state lam u h0 x T)
      (carried (fun t => lam t x0) (source lam u h0 lam' u' x0) 0 P0 T) x0 := by
  induction T with
  | zero => exact hh0
  | succ T ih =>
    have h := ((hlam T).fun_mul ih).fun_add (hu T)
    rw [carried_succ, Nat.zero_add]
    refine h.congr_deriv ?_
    simp only [source]
    abel

/-- [proved-derived; formal-checked] **The passage's covector**: for readings `ℓ_t` of the state
with derivatives `G_t`, the code `Σ_(t<T) ℓ_t(h_t)` has derivative `Σ_(t<T) G_t(P_t)`. -/
theorem hasDerivAt_passage {lam u : ℕ → ℝ → 𝔸} {h0 : ℝ → 𝔸} {lam' u' : ℕ → 𝔸} {P0 : 𝔸}
    {x0 : ℝ} (hlam : ∀ t, HasDerivAt (lam t) (lam' t) x0) (hu : ∀ t, HasDerivAt (u t) (u' t) x0)
    (hh0 : HasDerivAt h0 P0 x0) (ℓ : ℕ → 𝔸 → ℝ) (G : ℕ → 𝔸 →L[ℝ] ℝ)
    (hℓ : ∀ t, HasFDerivAt (ℓ t) (G t) (state lam u h0 x0 t)) (T : ℕ) :
    HasDerivAt (fun x => ∑ t ∈ range T, ℓ t (state lam u h0 x t))
      (∑ t ∈ range T, G t (carried (fun t => lam t x0) (source lam u h0 lam' u' x0) 0 P0 t))
      x0 := by
  have h : ∀ t ∈ range T, HasDerivAt (fun x => ℓ t (state lam u h0 x t))
      (G t (carried (fun t => lam t x0) (source lam u h0 lam' u' x0) 0 P0 t)) x0 :=
    fun t _ => (hℓ t).comp_hasDerivAt x0 (hasDerivAt_state hlam hu hh0 t)
  exact HasDerivAt.fun_sum h

/-- [definition] The section's covector at its opening: the section's readings `G_(m+k)`, each
carried back to the opening through the transport, as a reading of the opening's moments. -/
def openingCovector (lam : ℕ → 𝔸) (G : ℕ → 𝔸 →L[ℝ] ℝ) (m n : ℕ) (P : 𝔸) : ℝ :=
  ∑ k ∈ range n, G (m + k) (carry lam m k * P)

/-- [proved-derived; formal-checked] **The opening credit completes the passage's covector**: over a
passage split at `m`, the whole covector is the first section's, plus the second section's from
rest, plus the second section's covector at its opening paired with the carried moments `P_m`. -/
theorem passage_covector_split (lam d : ℕ → 𝔸) (G : ℕ → 𝔸 →L[ℝ] ℝ) (P0 : 𝔸) (m n : ℕ) :
    ∑ t ∈ range (m + n), G t (carried lam d 0 P0 t) =
      ∑ t ∈ range m, G t (carried lam d 0 P0 t) +
        ∑ k ∈ range n, G (m + k) (carried lam d m 0 k) +
          openingCovector lam G m n (carried lam d 0 P0 m) := by
  rw [Finset.sum_range_add, add_assoc, openingCovector, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [carried_add lam d 0 P0 m k, Nat.zero_add,
    carried_opening lam d m (carried lam d 0 P0 m) k, map_add]

end Passage

end Holonics.HNN.PassageCredit
