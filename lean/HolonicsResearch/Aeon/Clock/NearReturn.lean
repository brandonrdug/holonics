import Holonics.Aeon.Clock.Lock

/-!
# The convergent near-return is strict until the last step, where it is exact

`Aeon/Clock/Lock` reads the convergents `p_n / q_n` of the frequency ratio `α` of two clocks as
their near-returns. For irrational `α` it proves `|q_n α − p_n| ≤ 1/q_(n+1)`
(`convergent_near_return`, Mathlib's non-strict `GenContFract.abs_sub_convs_le`), and for rational
`α` that some convergent closes exactly (`rational_ratio_locks_at_a_convergent`). #410 owes the
near-return of a rational clock, whose expansion terminates, and the strict bound
`|q_n α − p_n| < 1/q_(n+1)`. Both come from one exact reading of the miss.

[proved-standard; formal-checked] What is proved, for every real `α` whose continued fraction has
not terminated at step `n` (every `n` when `α` is irrational, every `n` before the last step when
`α` is rational).

1. **The exact miss** (`exact_miss`): with `r = 1/fr_n` the `n`-th complete quotient (the inverse of
   the fractional part of the `n`-th stream pair),
   `q_n α − p_n = (−1)ⁿ / (r q_n + q_(n−1))`, and the next denominator is
   `q_(n+1) = q_(n−1) + ⌊r⌋ q_n` (`q_(−1) = 0`, Mathlib's `contsAux n`).
2. **The near-return** (`near_return_le`): `|q_n α − p_n| ≤ 1/q_(n+1)` for every real `α`, rational
   included, since `⌊r⌋ ≤ r`. Once the expansion has terminated the miss is zero
   (`closes_of_terminatedAt`), so the bound holds at every step (`near_return_le_all`).
3. **Strict while the expansion continues** (`near_return_lt`): if the expansion has not terminated
   at step `n + 1`, the floor is strict (`⌊r⌋ < r`, the next fractional part is not zero) and so is
   the bound. For irrational `α` this holds at every step (`convergent_near_return_strict`).
4. **Exact at the last step** (`near_return_eq_of_terminatedAt`): if the expansion terminates at
   step `n + 1`, then `r` is an integer and the miss is exactly `1/q_(n+1)`. So the bound is strict
   exactly when the expansion continues (`near_return_lt_iff`).
5. **Farey neighbours before termination** (`farey_neighbours_of_not_terminated`):
   `p_n q_(n+1) − q_n p_(n+1) = (−1)^(n+1)`, rational `α` included.
6. **The rational clock** (`rational_clock_near_returns`): for `α = x ∈ ℚ` there is a first step
   `N` at which the expansion terminates. The aeon of `q_N` ticks closes exactly
   (`q_N x − p_N = 0`). Every earlier step `n` with `n + 1 < N` misses by strictly less than
   `1/q_(n+1)`, and the step just before closure misses by exactly `1/q_N`.

The computational object is the helical pair interaction of two clocks: the aeon of `q_n` ticks of
the second clock reads the first clock's open phase `q_n α − p_n`, the pair contact's slip at that
grain, and each convergent is the carry at which the next finer grain begins. Of the winding
guide's six general objects this touches the helix (the carry of whole windings `p_n`) and the pair
(the slip `q_n α − p_n`); faces and placement, the cell holonomy, the tube and the tower thread stay
attached.

Consumers: the atlas rows `aeon.convergent-near-return`, `aeon.rational-near-return` and
`aeon.two-clocks-lock`, the Rust owner `holonics::aeon::TwoClocks`, and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Aeon.Clock.NearReturn

open GenContFract
open Holonics.Aeon.Clock.Lock

variable {α : ℝ} {n : ℕ}

/-! ## 1. The exact miss -/

/-- [proved-standard; formal-checked] **The exact miss.** Before termination, with `r = 1/fr_n`,
`q_n α − p_n = (−1)ⁿ / (r q_n + q_(n−1))` and `q_(n+1) = q_(n−1) + ⌊r⌋ q_n`; the next stream pair is
`(⌊r⌋, fract r)`. -/
theorem exact_miss (h : ¬ (GenContFract.of α).TerminatedAt n) :
    ∃ ifp : IntFractPair ℝ, IntFractPair.stream α n = some ifp ∧ ifp.fr ≠ 0 ∧
      IntFractPair.stream α (n + 1) = some (IntFractPair.of ifp.fr⁻¹) ∧
      (GenContFract.of α).dens (n + 1) =
        ((GenContFract.of α).contsAux n).b + ⌊ifp.fr⁻¹⌋ * (GenContFract.of α).dens n ∧
      (GenContFract.of α).dens n * α - (GenContFract.of α).nums n =
        (-1) ^ n /
          (ifp.fr⁻¹ * (GenContFract.of α).dens n + ((GenContFract.of α).contsAux n).b) := by
  obtain ⟨gp, hs⟩ : ∃ gp, (GenContFract.of α).s.get? n = some gp := Option.ne_none_iff_exists'.mp h
  have ha : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a hs)
  obtain ⟨ifs, hifs, hb⟩ : ∃ ifp : IntFractPair ℝ,
      IntFractPair.stream α (n + 1) = some ifp ∧ (ifp.b : ℝ) = gp.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hs
  obtain ⟨ifp, hstream, hfr, hof⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hifs
  subst hof
  have e0 : (GenContFract.of α).dens n = ((GenContFract.of α).contsAux (n + 1)).b := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have e1 : (GenContFract.of α).dens (n + 1) = ((GenContFract.of α).contsAux (n + 2)).b := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have hrec := contsAux_recurrence hs (rfl : (GenContFract.of α).contsAux n = _)
    (rfl : (GenContFract.of α).contsAux (n + 1) = _)
  have hB : 0 < (GenContFract.of α).dens n := dens_pos α n
  have hpB : 0 ≤ ((GenContFract.of α).contsAux n).b := zero_le_of_contsAux_b
  have hr : 0 < ifp.fr⁻¹ :=
    inv_pos.mpr (lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg hstream) hfr.symm)
  have hD : 0 < ifp.fr⁻¹ * (GenContFract.of α).dens n + ((GenContFract.of α).contsAux n).b :=
    add_pos_of_pos_of_nonneg (mul_pos hr hB) hpB
  refine ⟨ifp, hstream, hfr, hifs, ?_, ?_⟩
  · rw [e1, e0, hrec, ha, ← hb]
    simp only [IntFractPair.of]
    ring
  · have hsub := sub_convs_eq (v := α) hstream
    simp only [hfr, if_false] at hsub
    rw [conv_eq_num_div_den, ← e0] at hsub
    calc (GenContFract.of α).dens n * α - (GenContFract.of α).nums n
        = (GenContFract.of α).dens n *
            (α - (GenContFract.of α).nums n / (GenContFract.of α).dens n) := by
          rw [mul_sub, mul_div_cancel₀ _ hB.ne']
      _ = (GenContFract.of α).dens n * ((-1) ^ n / ((GenContFract.of α).dens n *
            (ifp.fr⁻¹ * (GenContFract.of α).dens n + ((GenContFract.of α).contsAux n).b))) := by
          rw [hsub]
      _ = (-1) ^ n /
            (ifp.fr⁻¹ * (GenContFract.of α).dens n + ((GenContFract.of α).contsAux n).b) := by
          rw [← mul_div_assoc, mul_div_mul_left _ _ hB.ne']

/-- [proved-standard; formal-checked] The expansion terminates at step `n + 1` exactly when the
`n + 1`-th fractional part `fract r` is zero. -/
theorem terminatedAt_succ_iff {ifp : IntFractPair ℝ}
    (hs : IntFractPair.stream α (n + 1) = some (IntFractPair.of ifp.fr⁻¹)) :
    (GenContFract.of α).TerminatedAt (n + 1) ↔ Int.fract ifp.fr⁻¹ = 0 := by
  rw [of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none,
    IntFractPair.succ_nth_stream_eq_none_iff]
  constructor
  · rintro (h0 | ⟨p, hp, hp0⟩)
    · rw [hs] at h0
      exact absurd h0 (Option.some_ne_none _)
    · rw [hs] at hp
      have hpe := Option.some.inj hp
      subst hpe
      exact hp0
  · intro h0
    exact Or.inr ⟨_, hs, h0⟩

/-! ## 2. The near-return, strict until the last step -/

/-- [proved-standard; formal-checked] **The near-return**, for every real ratio before
termination: `|q_n α − p_n| ≤ 1/q_(n+1)`. -/
theorem near_return_le (h : ¬ (GenContFract.of α).TerminatedAt n) :
    |(GenContFract.of α).dens n * α - (GenContFract.of α).nums n| ≤
      1 / (GenContFract.of α).dens (n + 1) := by
  obtain ⟨ifp, hstream, hfr, -, hrec, hmiss⟩ := exact_miss h
  have hB : 0 < (GenContFract.of α).dens n := dens_pos α n
  have hpB : 0 ≤ ((GenContFract.of α).contsAux n).b := zero_le_of_contsAux_b
  have hr : 0 < ifp.fr⁻¹ :=
    inv_pos.mpr (lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg hstream) hfr.symm)
  rw [hmiss, abs_div, abs_neg_one_pow, abs_of_pos (add_pos_of_pos_of_nonneg (mul_pos hr hB) hpB)]
  apply one_div_le_one_div_of_le (dens_pos α (n + 1))
  rw [hrec]
  have := mul_le_mul_of_nonneg_right (Int.floor_le ifp.fr⁻¹) hB.le
  linarith

/-- [proved-standard; formal-checked] **The closure**: once the expansion has terminated at step
`n`, the aeon of `q_n` ticks closes exactly, `q_n α − p_n = 0`. -/
theorem closes_of_terminatedAt (h : (GenContFract.of α).TerminatedAt n) :
    (GenContFract.of α).dens n * α - (GenContFract.of α).nums n = 0 := by
  have hv := of_correctness_of_terminatedAt h
  rw [conv_eq_num_div_den] at hv
  have hq := dens_pos α n
  rw [sub_eq_zero]
  calc (GenContFract.of α).dens n * α
      = (GenContFract.of α).dens n *
          ((GenContFract.of α).nums n / (GenContFract.of α).dens n) := by rw [← hv]
    _ = (GenContFract.of α).nums n := mul_div_cancel₀ _ hq.ne'

/-- [proved-standard; formal-checked] **The near-return at every step**, for every real ratio:
`|q_n α − p_n| ≤ 1/q_(n+1)`, the miss being zero once the expansion has terminated. -/
theorem near_return_le_all (n : ℕ) :
    |(GenContFract.of α).dens n * α - (GenContFract.of α).nums n| ≤
      1 / (GenContFract.of α).dens (n + 1) := by
  by_cases h : (GenContFract.of α).TerminatedAt n
  · rw [closes_of_terminatedAt h, abs_zero]
    exact (one_div_pos.mpr (dens_pos α (n + 1))).le
  · exact near_return_le h

/-- [proved-standard; formal-checked] **Strict while the expansion continues**: if it has not
terminated at step `n + 1`, then `|q_n α − p_n| < 1/q_(n+1)`. -/
theorem near_return_lt (h : ¬ (GenContFract.of α).TerminatedAt (n + 1)) :
    |(GenContFract.of α).dens n * α - (GenContFract.of α).nums n| <
      1 / (GenContFract.of α).dens (n + 1) := by
  have hn : ¬ (GenContFract.of α).TerminatedAt n := fun hn => h (terminated_stable n.le_succ hn)
  obtain ⟨ifp, hstream, hfr, hs, hrec, hmiss⟩ := exact_miss hn
  have hB : 0 < (GenContFract.of α).dens n := dens_pos α n
  have hpB : 0 ≤ ((GenContFract.of α).contsAux n).b := zero_le_of_contsAux_b
  have hr : 0 < ifp.fr⁻¹ :=
    inv_pos.mpr (lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg hstream) hfr.symm)
  have hfract : 0 < Int.fract ifp.fr⁻¹ :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm fun h0 => h ((terminatedAt_succ_iff hs).mpr h0))
  have hfloor : (⌊ifp.fr⁻¹⌋ : ℝ) < ifp.fr⁻¹ := by
    rw [← Int.self_sub_floor] at hfract
    linarith
  rw [hmiss, abs_div, abs_neg_one_pow, abs_of_pos (add_pos_of_pos_of_nonneg (mul_pos hr hB) hpB)]
  apply one_div_lt_one_div_of_lt (dens_pos α (n + 1))
  rw [hrec]
  have := mul_lt_mul_of_pos_right hfloor hB
  linarith

/-- [proved-standard; formal-checked] **The strict bound for an irrational ratio**, at every step:
`|q_n α − p_n| < 1/q_(n+1)`. -/
theorem convergent_near_return_strict (hα : Irrational α) (n : ℕ) :
    |(GenContFract.of α).dens n * α - (GenContFract.of α).nums n| <
      1 / (GenContFract.of α).dens (n + 1) :=
  near_return_lt (not_terminatedAt_of_irrational hα (n + 1))

/-- [proved-standard; formal-checked] **Exact at the last step**: if the expansion has not
terminated at step `n` but terminates at step `n + 1`, the miss is exactly `1/q_(n+1)`. -/
theorem near_return_eq_of_terminatedAt (h : ¬ (GenContFract.of α).TerminatedAt n)
    (h' : (GenContFract.of α).TerminatedAt (n + 1)) :
    |(GenContFract.of α).dens n * α - (GenContFract.of α).nums n| =
      1 / (GenContFract.of α).dens (n + 1) := by
  obtain ⟨ifp, hstream, hfr, hs, hrec, hmiss⟩ := exact_miss h
  have hB : 0 < (GenContFract.of α).dens n := dens_pos α n
  have hpB : 0 ≤ ((GenContFract.of α).contsAux n).b := zero_le_of_contsAux_b
  have hr : 0 < ifp.fr⁻¹ :=
    inv_pos.mpr (lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg hstream) hfr.symm)
  have hfract : Int.fract ifp.fr⁻¹ = 0 := (terminatedAt_succ_iff hs).mp h'
  have hfloor : (⌊ifp.fr⁻¹⌋ : ℝ) = ifp.fr⁻¹ := by
    rw [← Int.self_sub_floor] at hfract
    linarith
  rw [hmiss, abs_div, abs_neg_one_pow, abs_of_pos (add_pos_of_pos_of_nonneg (mul_pos hr hB) hpB),
    hrec, hfloor, add_comm]

/-- [proved-standard; formal-checked] **The bound is strict exactly when the expansion
continues.** -/
theorem near_return_lt_iff (h : ¬ (GenContFract.of α).TerminatedAt n) :
    |(GenContFract.of α).dens n * α - (GenContFract.of α).nums n| <
        1 / (GenContFract.of α).dens (n + 1) ↔
      ¬ (GenContFract.of α).TerminatedAt (n + 1) := by
  refine ⟨fun hlt h' => ?_, near_return_lt⟩
  rw [near_return_eq_of_terminatedAt h h'] at hlt
  exact lt_irrefl _ hlt

/-- [proved-standard; formal-checked] **Consecutive convergents are Farey neighbours before
termination**, rational ratios included: `p_n q_(n+1) − q_n p_(n+1) = (−1)^(n+1)`. -/
theorem farey_neighbours_of_not_terminated (h : ¬ (GenContFract.of α).TerminatedAt n) :
    (GenContFract.of α).nums n * (GenContFract.of α).dens (n + 1) -
      (GenContFract.of α).dens n * (GenContFract.of α).nums (n + 1) = (-1) ^ (n + 1) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      -(((GenContFract.of α).partNums.get? i).getD 0) = (-1 : ℝ) := by
    intro i hi
    have hi' : i ≤ n := Nat.le_of_succ_le_succ (Finset.mem_range.mp hi)
    obtain ⟨gp, hs⟩ : ∃ gp, (GenContFract.of α).s.get? i = some gp :=
      Option.ne_none_iff_exists'.mp fun hi0 => h (terminated_stable hi' hi0)
    rw [partNum_eq_s_a hs, Option.getD_some, of_partNum_eq_one (partNum_eq_s_a hs)]
  rw [determinant, Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_range]

/-! ## 3. The rational clock -/

/-- [proved-standard; formal-checked] **The near-returns of a rational clock.** For `x ∈ ℚ` the
expansion terminates at a first step `N`, where the aeon of `q_N` ticks closes exactly. Every
earlier step with `n + 1 < N` misses by strictly less than `1/q_(n+1)`, and the step just before
closure misses by exactly `1/q_N`. -/
theorem rational_clock_near_returns (x : ℚ) :
    ∃ N : ℕ, (GenContFract.of (x : ℝ)).TerminatedAt N ∧
      (GenContFract.of (x : ℝ)).dens N * x - (GenContFract.of (x : ℝ)).nums N = 0 ∧
      (∀ n, n + 1 < N →
        |(GenContFract.of (x : ℝ)).dens n * x - (GenContFract.of (x : ℝ)).nums n| <
          1 / (GenContFract.of (x : ℝ)).dens (n + 1)) ∧
      (∀ n, n + 1 = N →
        |(GenContFract.of (x : ℝ)).dens n * x - (GenContFract.of (x : ℝ)).nums n| =
          1 / (GenContFract.of (x : ℝ)).dens (n + 1)) := by
  classical
  have hterm : ∃ N, (GenContFract.of (x : ℝ)).TerminatedAt N :=
    (terminates_iff_rat (x : ℝ)).mpr ⟨x, rfl⟩
  refine ⟨Nat.find hterm, Nat.find_spec hterm, ?_, fun n hn => ?_, fun n hn => ?_⟩
  · exact closes_of_terminatedAt (Nat.find_spec hterm)
  · exact near_return_lt (Nat.find_min hterm (by omega))
  · refine near_return_eq_of_terminatedAt (Nat.find_min hterm (by omega)) ?_
    rw [hn]
    exact Nat.find_spec hterm

end Holonics.Aeon.Clock.NearReturn
