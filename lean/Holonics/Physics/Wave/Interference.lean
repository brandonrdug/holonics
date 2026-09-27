import Mathlib

/-!
# Interference joins coherent amplitudes before the intensity is read

[definition] Rebuild step 6, K3 (#74), battle test 2, first half. A wave's paths arrive at a
receiver as complex amplitudes `u_j` (each already transported along its path by its connection
phase). The **coherent** reading joins them first and reads the intensity of the join,
`|Σ u_j|²`; the **incoherent** reading reads each intensity first and sums, `Σ |u_j|²`.

[proved-derived; formal-checked] What is proved.

1. **The interference identity** (`intensity_eq`): for every finite family,
   `|Σ_j u_j|² = Σ_j |u_j|² + 2 Re Σ_(j<k) ū_j u_k`. The difference between the two readings is
   exactly the cross terms (`cross_is_the_difference`).
2. **Reading intensities first loses the cross terms.** `1 + (−1)` reads `0` coherently and `2`
   incoherently (`opposite_amplitudes_cancel`); `1 + 1` reads `4` and `2`
   (`equal_amplitudes_reinforce`). Hence no function of the incoherent reading returns the
   coherent intensity (`coherent_not_a_function_of_incoherent`): the cross terms are information
   the intensity-first receiver has already discarded.
3. **The phases the two readings see.** A joint phase `e` with `|e| = 1` leaves the coherent
   intensity unchanged (`common_phase_invariant`): only relative phase is physical. The incoherent
   reading is blind to every per-path phase (`incoherent_phase_blind`), while the coherent reading
   is not: turning one path by a half-turn moves `4` to `0` (`relative_phase_moves_intensity`).
   The unit modulus is load-bearing: a joint factor `2` scales the intensity by `4`
   (`nonunit_factor_scales`).
4. **Resolved modes.** When each path carries a mode tag and the receiver reads each mode's
   coherent intensity, the cross terms survive only between paths of one mode
   (`resolved_intensity_eq`); distinct modes, such as orthogonal path tags or an instrument that
   separates the paths, give the incoherent reading (`distinct_modes_no_cross_terms`), and one
   shared mode gives the coherent reading (`single_mode_is_coherent`).

The atlas row `holon.interference-before-intensity` stated the two-term identity as
`proved-standard`; this is its checked, finite-family form. It is distinct from
`Physics/PhaseContactPassage.interpolation_intensity_defect` (a convex mix of two amplitudes) and
from `Computation/HolonicPolarizedCrystalTransport` (paths through a crystal, research library).

No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Physics.Wave.Interference

open Finset ComplexConjugate

/-- [definition] **The coherent join** of the first `n` amplitudes. -/
def coherent (u : ℕ → ℂ) (n : ℕ) : ℂ := ∑ j ∈ range n, u j

/-- [definition] **The incoherent reading**: each intensity read first, then summed. -/
def incoherent (u : ℕ → ℂ) (n : ℕ) : ℝ := ∑ j ∈ range n, Complex.normSq (u j)

/-- [definition] **The cross terms** `2 Re Σ_(j<k) ū_j u_k`. -/
def cross (u : ℕ → ℂ) (n : ℕ) : ℝ :=
  2 * ∑ k ∈ range n, ∑ j ∈ range k, (conj (u j) * u k).re

/-- [proved-derived; formal-checked] **The interference identity**:
`|Σ u_j|² = Σ |u_j|² + 2 Re Σ_(j<k) ū_j u_k`. -/
theorem intensity_eq (u : ℕ → ℂ) (n : ℕ) :
    Complex.normSq (coherent u n) = incoherent u n + cross u n := by
  induction n with
  | zero => simp [coherent, incoherent, cross]
  | succ n ih =>
    have hc : (∑ j ∈ range n, u j * conj (u n)).re = ∑ j ∈ range n, (conj (u j) * u n).re := by
      rw [Complex.re_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [← Complex.conj_re (u j * conj (u n)), map_mul, Complex.conj_conj]
    simp only [coherent, incoherent, cross, sum_range_succ] at ih ⊢
    rw [Complex.normSq_add, ih, sum_mul, hc]
    ring

/-- [proved-derived; formal-checked] The two readings differ by exactly the cross terms. -/
theorem cross_is_the_difference (u : ℕ → ℂ) (n : ℕ) :
    Complex.normSq (coherent u n) - incoherent u n = cross u n := by
  rw [intensity_eq]; ring

/-- The two-path family `(a, b)`. -/
def pair (a b : ℂ) : ℕ → ℂ := fun j => if j = 0 then a else if j = 1 then b else 0

theorem coherent_pair (a b : ℂ) : coherent (pair a b) 2 = a + b := by
  simp [coherent, pair, sum_range_succ]

theorem incoherent_pair (a b : ℂ) :
    incoherent (pair a b) 2 = Complex.normSq a + Complex.normSq b := by
  simp [incoherent, pair, sum_range_succ]

/-- [counterexample; formal-checked] **`1 + (−1) = 0` must not become `|1|² + |−1|² = 2`.**
Opposite amplitudes cancel coherently while their intensities add. -/
theorem opposite_amplitudes_cancel :
    Complex.normSq (coherent (pair 1 (-1)) 2) = 0 ∧ incoherent (pair 1 (-1)) 2 = 2 := by
  rw [coherent_pair, incoherent_pair]
  norm_num

/-- [counterexample; formal-checked] Equal amplitudes reinforce: `|1 + 1|² = 4 ≠ 2`. -/
theorem equal_amplitudes_reinforce :
    Complex.normSq (coherent (pair 1 1) 2) = 4 ∧ incoherent (pair 1 1) 2 = 2 := by
  rw [coherent_pair, incoherent_pair]
  norm_num [Complex.normSq_apply]

/-- [counterexample; formal-checked] **The coherent intensity is not a function of the
incoherent reading**: two families with one incoherent reading, `2`, have coherent intensities `4`
and `0`. -/
theorem coherent_not_a_function_of_incoherent :
    ¬ ∃ f : ℝ → ℝ, ∀ (u : ℕ → ℂ) (n : ℕ),
      Complex.normSq (coherent u n) = f (incoherent u n) := by
  rintro ⟨f, hf⟩
  have h1 := hf (pair 1 1) 2
  have h2 := hf (pair 1 (-1)) 2
  rw [equal_amplitudes_reinforce.1, equal_amplitudes_reinforce.2] at h1
  rw [opposite_amplitudes_cancel.1, opposite_amplitudes_cancel.2] at h2
  rw [← h1] at h2
  norm_num at h2

/-- [proved-derived; formal-checked] **Only relative phase is physical**: a joint unit phase
leaves the coherent intensity unchanged. -/
theorem common_phase_invariant (u : ℕ → ℂ) (n : ℕ) {e : ℂ} (he : Complex.normSq e = 1) :
    Complex.normSq (coherent (fun j => e * u j) n) = Complex.normSq (coherent u n) := by
  simp only [coherent, ← mul_sum, Complex.normSq_mul, he, one_mul]

/-- [counterexample; formal-checked] **The unit modulus is load-bearing**: the joint factor `2`
(the family `2 · (1, 0) = (2, 0)`) is not a phase, and it scales the intensity by `4`. -/
theorem nonunit_factor_scales :
    Complex.normSq (coherent (pair 2 0) 2) = 4 ∧
      Complex.normSq (coherent (pair 1 0) 2) = 1 := by
  rw [coherent_pair, coherent_pair]
  norm_num [Complex.normSq_apply]

/-- [proved-derived; formal-checked] **The incoherent reading is blind to every per-path phase.** -/
theorem incoherent_phase_blind (u e : ℕ → ℂ) (n : ℕ) (he : ∀ j, Complex.normSq (e j) = 1) :
    incoherent (fun j => e j * u j) n = incoherent u n := by
  simp only [incoherent, Complex.normSq_mul, he, one_mul]

/-- [counterexample; formal-checked] **The coherent reading sees relative phase**: a half-turn on
one path moves the intensity from `4` to `0`, while the incoherent reading stays `2`. -/
theorem relative_phase_moves_intensity :
    Complex.normSq (coherent (fun j => (pair 1 (-1)) j * pair 1 1 j) 2) = 0 ∧
      Complex.normSq (coherent (pair 1 1) 2) = 4 ∧
      incoherent (fun j => (pair 1 (-1)) j * pair 1 1 j) 2 = incoherent (pair 1 1) 2 := by
  refine ⟨?_, equal_amplitudes_reinforce.1, ?_⟩
  · simp [coherent, pair, sum_range_succ]
  · simp [incoherent, pair, sum_range_succ]

/-! ## Resolved modes: cross terms only between paths that reach one mode -/

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- [definition] **The resolved reading.** Each path carries a mode tag `t j` (an orthogonal path
tag, or the detector cell it reaches); the receiver joins the amplitudes of each mode coherently,
reads that mode's intensity, and sums over modes. -/
def resolved (t : ℕ → M) (u : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∑ m, Complex.normSq (∑ j ∈ (range n).filter (fun j => t j = m), u j)

/-- [definition] The cross terms `2 Re Σ_(j<k, t j = t k) ū_j u_k` between paths of one mode. -/
def sameModeCross (t : ℕ → M) (u : ℕ → ℂ) (n : ℕ) : ℝ :=
  2 * ∑ k ∈ range n, ∑ j ∈ (range k).filter (fun j => t j = t k), (conj (u j) * u k).re

/-- [proved-derived; formal-checked] **The resolved interference identity**: the resolved reading
is the incoherent reading plus the cross terms of the pairs that reach one mode. -/
theorem resolved_intensity_eq (t : ℕ → M) (u : ℕ → ℂ) (n : ℕ) :
    resolved t u n = incoherent u n + sameModeCross t u n := by
  induction n with
  | zero => simp [resolved, incoherent, sameModeCross]
  | succ n ih =>
    have hsplit : ∀ m, ∑ j ∈ (range (n + 1)).filter (fun j => t j = m), u j =
        (∑ j ∈ (range n).filter (fun j => t j = m), u j) + if t n = m then u n else 0 := by
      intro m
      rw [sum_filter, sum_filter, sum_range_succ]
    have hterm : ∀ m, Complex.normSq (∑ j ∈ (range (n + 1)).filter (fun j => t j = m), u j) =
        Complex.normSq (∑ j ∈ (range n).filter (fun j => t j = m), u j) +
          if t n = m then Complex.normSq (u n) +
            2 * ((∑ j ∈ (range n).filter (fun j => t j = m), u j) * conj (u n)).re else 0 := by
      intro m
      rw [hsplit m]
      by_cases h : t n = m
      · simp only [h, if_true, Complex.normSq_add]
        ring
      · simp [h]
    have hc : ((∑ j ∈ (range n).filter (fun j => t j = t n), u j) * conj (u n)).re =
        ∑ j ∈ (range n).filter (fun j => t j = t n), (conj (u j) * u n).re := by
      rw [sum_mul, Complex.re_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [← Complex.conj_re (u j * conj (u n)), map_mul, Complex.conj_conj]
    have hres : resolved t u (n + 1) = resolved t u n + (Complex.normSq (u n) +
        2 * ∑ j ∈ (range n).filter (fun j => t j = t n), (conj (u j) * u n).re) := by
      simp only [resolved]
      rw [sum_congr rfl fun m _ => hterm m, sum_add_distrib, sum_ite_eq]
      simp only [mem_univ, if_true, hc]
    rw [hres, ih]
    simp only [incoherent, sameModeCross, sum_range_succ]
    ring

/-- [proved-derived; formal-checked] **Distinct resolved modes give no cross terms.** When no two
paths reach one mode, the resolved reading is the incoherent reading. -/
theorem distinct_modes_no_cross_terms (t : ℕ → M) (u : ℕ → ℂ) (n : ℕ)
    (ht : ∀ j k, j < n → k < n → t j = t k → j = k) :
    resolved t u n = incoherent u n := by
  rw [resolved_intensity_eq]
  have hzero : sameModeCross t u n = 0 := by
    unfold sameModeCross
    rw [sum_eq_zero, mul_zero]
    intro k hk
    refine sum_eq_zero fun j hj => ?_
    simp only [mem_filter, mem_range] at hj hk
    exact absurd (ht j k (hj.1.trans hk) hk hj.2) hj.1.ne
  rw [hzero, add_zero]

/-- [proved-derived; formal-checked] **One shared mode is the coherent reading.** -/
theorem single_mode_is_coherent (u : ℕ → ℂ) (n : ℕ) :
    resolved (fun _ => ()) u n = Complex.normSq (coherent u n) := by
  simp [resolved, coherent]

section Audit

#print axioms intensity_eq
#print axioms resolved_intensity_eq
#print axioms distinct_modes_no_cross_terms
#print axioms single_mode_is_coherent
#print axioms coherent_not_a_function_of_incoherent
#print axioms common_phase_invariant
#print axioms relative_phase_moves_intensity

end Audit

end Holonics.Physics.Wave.Interference
