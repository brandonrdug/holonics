import Holonics.HNN.CarriedCuts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# HNN.ReleaseRun: a run closes on a condition, and how many halvings a move needs

[proved-derived; formal-checked] Two counts of the native chain were chosen constants: the run
length `W = 8` (the most moves from an opening state to its close, `HNN/ExecutedComparison`
§12) and the halving count `LADDER_DEPTH = 8` (`hnn::executed`, retired: the halvings now end at
the lattice). This module states what the chain's own laws fix in their place.

**1. The run closes on a condition, not a length** (`close_at_any_length`). The close test
(`ReleaseExcursion::closes`) reads the opening's code length, the current one and the grain `σ`.
The moves read the whole continuing state, whose deposit clock and carried Gram advance at every
adopted move, so no state of a run repeats. The repayment law admits a first close at every length,
so no length follows from it: `W` is a bound on work.

**2. The halvings a move needs.** The halvings already end where the carried move moves no lattice
coordinate (`attempted_halvings_le_lattice`: `2^k ≤ 1/λ`). Where the comparison has a curvature
bound `K` along the move from its slope `d < 0`, the halving whose step is at most the curvature
length `|d|/K` adopts with half the first-order decrease (`halving_within_curvature`), the first
such halving decreases by more than `d²/(4K)` (`least_halving_decrease`), and with a crossing at
`η_c` the step must also lie below it (`halving_adopts_before_crossing`). For a Gauss–Newton
first step (`η₀ = 1`, the model's curvature `−d`), the `m`-th halving lies within the curvature
length when the comparison's curvature is at most `2^m` times the model's (`gauss_newton_halvings`).

The record: `research/records/2026-10-02_A_RUN_CLOSES_ON_A_CONDITION_NOT_A_LENGTH_AND_THE_HALVINGS_END_AT_THE_LATTICE.md`.
-/

namespace Holonics.HNN.ReleaseRun

open Filter Topology

/-! ## 1. The run closes on a condition, not a length -/

/-- [proved-derived; formal-checked] **The repayment law admits a first close at any length.** The
law's hypotheses are a positive held decrease at every move (`m k < f k`, the held-commitment code
length at the successor below the incumbent's released one) and any jumps. For every length `W`
and grain `σ` they admit a path whose released code length stays at or above `f 0 − σ` through
move `W` and lies below it at move `W + 1`, each move changing it by at most `σ + 1`. So the law fixes when a run closes, never how many
moves it takes. -/
theorem close_at_any_length (W : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ f m : ℕ → ℝ, (∀ k, m k < f k) ∧ (∀ k, k ≤ W → f 0 - σ ≤ f k) ∧
      f (W + 1) < f 0 - σ ∧ (∀ k, |f (k + 1) - f k| ≤ σ + 1) := by
  refine ⟨fun k => if k ≤ W then 0 else -σ - 1, fun k => (if k ≤ W then 0 else -σ - 1) - 1,
    fun k => by simp, ?_, ?_, ?_⟩
  · intro k hk
    simp only [hk, Nat.zero_le, if_true]
    linarith
  · simp only [Nat.zero_le, if_true, show ¬ (W + 1 ≤ W) by omega, if_false]
    linarith
  · intro k
    by_cases h1 : k + 1 ≤ W
    · simp [h1, show k ≤ W by omega]; linarith
    · by_cases h2 : k ≤ W
      · simp only [h1, h2, if_true, if_false]
        rw [abs_le]; constructor <;> linarith
      · simp [h1, h2]; linarith

/-! ## 2. How many halvings a move needs -/

/-- [proved-derived; formal-checked] **The halvings end at the lattice**: with the first step
`η₀` within the entry scale (`η₀ · 2u ≤ 1`), a halving `k` is tried only while its carried move
still moves a lattice coordinate (`λ ≤ η₀/2^k · 2u`), so `2^k ≤ 1/λ`. -/
theorem attempted_halvings_le_lattice {lam u η₀ : ℝ} (k : ℕ) (hlam : 0 < lam)
    (hstart : η₀ * (2 * u) ≤ 1) (hat : lam ≤ η₀ / 2 ^ k * (2 * u)) : (2 : ℝ) ^ k ≤ 1 / lam := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : η₀ / 2 ^ k * (2 * u) = η₀ * (2 * u) / 2 ^ k := by ring
  have h2 : lam ≤ 1 / 2 ^ k := by
    rw [h1] at hat
    exact hat.trans (div_le_div_of_nonneg_right hstart hpow.le)
  rw [le_div_iff₀ hlam]
  rw [le_div_iff₀ hpow] at h2
  linarith

/-- [proved-derived; formal-checked] **A halving within the curvature length adopts**: if the
comparison along the move lies below its first-order line plus the curvature term,
`f η ≤ f 0 + dη + Kη²/2` on `(0, η₀]`, with `K > 0`, then every halving whose step is
at most the curvature length `|d|/K` decreases by at least half the first-order decrease. -/
theorem halving_within_curvature {f : ℝ → ℝ} {d K η₀ : ℝ} (hK : 0 < K)
    (hη₀ : 0 < η₀) (hf : ∀ η, 0 < η → η ≤ η₀ → f η ≤ f 0 + d * η + K / 2 * η ^ 2) (k : ℕ)
    (hk : η₀ / 2 ^ k ≤ -d / K) : f (η₀ / 2 ^ k) ≤ f 0 + d * (η₀ / 2 ^ k) / 2 := by
  set η := η₀ / 2 ^ k with hη
  have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hpos : 0 < η := by positivity
  have hle : η ≤ η₀ := div_le_self hη₀.le hpow
  have hKη : K * η ≤ -d := by
    have := (le_div_iff₀ hK).mp hk
    linarith
  have hq : K / 2 * η ^ 2 ≤ -d * η / 2 := by nlinarith
  have := hf η hpos hle
  linarith

/-- **Some halving lies within the curvature length.** -/
theorem exists_halving_within {d K η₀ : ℝ} (hd : d < 0) (hK : 0 < K) :
    ∃ k : ℕ, η₀ / 2 ^ k ≤ -d / K := by
  have hpos : 0 < -d / K := div_pos (by linarith) hK
  have ht : Tendsto (fun k : ℕ => η₀ / 2 ^ k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, ← inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul η₀
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hpos)).exists
  exact ⟨k, hk.le⟩

/-- [proved-derived; formal-checked] **The first halving within the curvature length decreases by
more than `d²/(4K)`**: if the previous step `η₀/2^k` lay beyond `|d|/K`, the next one's
half-first-order decrease exceeds `d²/(4K)`. So the adopted decrease reaches the receiver's
grain `w` whenever `w ≤ d²/(4K)`. -/
theorem least_halving_decrease {d K η₀ : ℝ} (hd : d < 0) (hK : 0 < K) (k : ℕ)
    (hprev : -d / K < η₀ / 2 ^ k) : d ^ 2 / (4 * K) < -d * (η₀ / 2 ^ (k + 1)) / 2 := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hsplit : η₀ / 2 ^ (k + 1) = η₀ / 2 ^ k / 2 := by rw [pow_succ]; field_simp
  rw [hsplit]
  have h1 : -d < K * (η₀ / 2 ^ k) := by
    have := (div_lt_iff₀ hK).mp hprev
    linarith
  have h2 : d ^ 2 < -d * (K * (η₀ / 2 ^ k)) := by nlinarith
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * K)]
  nlinarith

/-- [proved-derived; formal-checked] **With a crossing, the step must also lie below it**: if the
released comparison `f` equals the fixed-order comparison `g` on `[0, η_c)` and `g` has the
curvature bound, a halving within both the curvature length and the crossing adopts. -/
theorem halving_adopts_before_crossing {f g : ℝ → ℝ} {d K η₀ ηc : ℝ} (hK : 0 < K)
    (hη₀ : 0 < η₀) (hfg : ∀ η, 0 ≤ η → η < ηc → f η = g η)
    (hg : ∀ η, 0 < η → η ≤ η₀ → g η ≤ g 0 + d * η + K / 2 * η ^ 2) (k : ℕ)
    (hk : η₀ / 2 ^ k ≤ -d / K) (hc : η₀ / 2 ^ k < ηc) :
    f (η₀ / 2 ^ k) ≤ f 0 + d * (η₀ / 2 ^ k) / 2 := by
  have hpos : 0 < η₀ / 2 ^ k := by positivity
  rw [hfg _ hpos.le hc, hfg 0 le_rfl (hpos.trans hc)]
  exact halving_within_curvature hK hη₀ hg k hk

/-- [proved-derived; formal-checked] **The Gauss–Newton first step's halvings read the curvature's
excess over the model's**: the first step `η₀ = 1` is the model's minimizer, whose curvature along
the move is `−d`. If the comparison's curvature is at most `2^m` times the model's, the `m`-th
halving lies within the curvature length. -/
theorem gauss_newton_halvings {d K : ℝ} (hK : 0 < K) (m : ℕ)
    (hratio : K ≤ 2 ^ m * (-d)) : (1 : ℝ) / 2 ^ m ≤ -d / K := by
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_le_div_iff₀ hpow hK]
  linarith

/-- [proved-derived; formal-checked] **Below the lattice's end a halving resolves no direction**:
when the step moves an entry by less than half the lattice unit (`2η|d| < u`, with `u` here the
lattice unit), its carried coordinate moves by at most one, and only where its remainder lies next
to a cut (`CarriedCuts.coordinate_moves_lt`). So `η · 2u < λ`, the halvings' end in `ladder` (there
`u` is the move's largest entry change and `λ` the lattice unit), is the lattice's resolution of
the move: below it every entry's carried change is a single unit or none,
set by the remainders, not by the direction. -/
theorem below_floor_one_coordinate (r d c η : ℝ) {u : ℝ} (hu : 0 < u) (hη : 0 ≤ η)
    (hfloor : η * |d| * 2 < u) :
    |CarriedCuts.coordinate r d u c η - CarriedCuts.coordinate r d u c 0| ≤ 1 := by
  have h := CarriedCuts.coordinate_moves_lt r d c 0 η hu
  rw [sub_zero, abs_of_nonneg hη] at h
  have hlt : η * |d| / u < 1 / 2 := by
    rw [div_lt_iff₀ hu]; linarith
  have h2 : |((CarriedCuts.coordinate r d u c η - CarriedCuts.coordinate r d u c 0 : ℤ) : ℝ)| < 2 := by
    linarith
  have h3 : |CarriedCuts.coordinate r d u c η - CarriedCuts.coordinate r d u c 0| < 2 := by
    exact_mod_cast h2
  omega

/-- [proved-derived; formal-checked] **A per-move scale bounds the reach**: if no move changes an
entry by more than `s`, `n` moves change it by at most `n s`. With the entry scale `s = ½`, the
chain's sixteen moves reach at most `8 = 2³` per entry, the entry bound itself. -/
theorem reach_le_moves (e : ℕ → ℝ) {s : ℝ} (h : ∀ k, |e (k + 1) - e k| ≤ s) (n : ℕ) :
    |e n - e 0| ≤ n * s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := abs_sub_le (e (n + 1)) (e n) (e 0)
    push_cast
    linarith [h n]

end Holonics.HNN.ReleaseRun

section Audit
open Holonics.HNN.ReleaseRun
#print axioms close_at_any_length
#print axioms attempted_halvings_le_lattice
#print axioms halving_within_curvature
#print axioms exists_halving_within
#print axioms least_halving_decrease
#print axioms halving_adopts_before_crossing
#print axioms gauss_newton_halvings
#print axioms below_floor_one_coordinate
#print axioms reach_le_moves
end Audit
