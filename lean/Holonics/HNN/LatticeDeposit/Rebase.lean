import Holonics.HNN.LatticeDeposit

/-!
# HNN.LatticeDeposit.Rebase: re-basing a carrier onto a finer lattice

[definition; agent-inferred] The confirmable grain of a running machine refines with its reading
count (`HNN/Ratio/Resolution.refiningGrain`, `L(N) = ⌈√(N ln 2/2)⌉`). It does not refine by integer
factors, so a schedule that keeps every coarser read is dyadic, `2^⌈log₂ L(N)⌉`
(`HNN/Ratio/Resolution.grainRead_of_refined`). A carrier on the lattice `2^(−L)ℤ` then moves to
`2^(−L−j)ℤ`. This module states that move for the lattice deposit's carrier (`HNN/LatticeDeposit`,
realized by `hnn::constitution`'s `BudgetedCarry` and `Carry`) and proves that it loses nothing the
carrier stored. It is the item #62 owed after PR #151.

**The re-base.** The carried remainder `r ∈ [−u/2, u/2)` is divided at the finer unit
`u′ = 2^(−L−j)`, `r = q′u′ + r′` with `r′ ∈ [−u′/2, u′/2)` (the owner's `div_rem_spec`). The value
takes the lattice part, `value′ = value + q′u′`, and the remainder `r′` is carried. The clock is kept,
so the precision schedule `k_m` continues. Nothing is released.

[proved-derived; formal-checked] What is proved.

1. **The re-base is exact** (`rebase_value_add_rem`, `rebase_shift`, `rebase_onLattice`,
   `rebase_clock`). `value′ + r′ = value + r` at every entry: the stored accumulation is unchanged.
   The value moves by `r − r′`, lands on the finer lattice, and the remainder is in the finer half
   cell and on the finer fine lattice of the same clock.
2. **The accounting runs across a re-base** (`rebase_run_accounting`). Deposits before the re-base
   at `L`, the re-base, then deposits at `L + j`: the final value and remainder plus both segments'
   releases equal the starting value and remainder plus every exact update. The re-base adds no
   term.
3. **The release bound across a re-base** (`release_across_rebase_le`,
   `release_across_rebase_lt`, `within_founding_unit_across_rebase`). Each deposit releases at most
   half its own fine cell, and the clock does not reset, so the two segments' releases together
   are at most `(u/2) Σ_(m ∈ (c₀, c₂]) 2^(−k_m) < u/2`, with `u` the unit before the re-base. The
   value stays within `u/2 + u′/2` of the exact accumulation.

[definition] **What this means for the contacts.** The bound is in the founding unit, not the
current one. After a re-base the half-cap at the current unit `u′/2` no longer holds: the releases
since the founding can reach `u/2`, which is `2^(j−1)` current units. So under a refining grain a
contact's dropped residuals are still bounded, but by the coarsest unit it was carried on; the
drift relative to the current grain grows with every refinement. The same proof iterates over any
number of re-bases: each deposit's release is at most half its own cell, every unit is at most the
founding one, and the Kraft sum over the whole clock is below one, so the total stays below the
founding `u/2`.

No `axiom`, no `sorry`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LatticeDeposit

variable {L : ℕ} {E : Type*}

/-! ## 1. The re-base -/

section Rebase

/-- [definition] **A carrier re-based onto the finer lattice `2^(−L−j)ℤ`.** The remainder is divided
at the finer unit; its lattice part joins the value and its remainder is carried. The clock is
kept. -/
def Carried.rebase (s : Carried L E) (j : ℕ) : Carried (L + j) E where
  value i := s.value i + quot (L + j) (s.rem i) * unit (L + j)
  rem i := LatticeDeposit.rem (L + j) (s.rem i)
  clock := s.clock
  rem_bounded i := rem_bounds (L + j) (s.rem i)
  rem_fine i := by
    obtain ⟨a, ha⟩ := s.rem_fine i
    refine ⟨a * 2 ^ j - quot (L + j) (s.rem i) * 2 ^ gammaLength s.clock, ?_⟩
    unfold LatticeDeposit.rem
    rw [ha]
    have e1 : unit (L + gammaLength s.clock) = 2 ^ j * unit (L + j + gammaLength s.clock) := by
      rw [show L + j + gammaLength s.clock = (L + gammaLength s.clock) + j by ring]
      exact unit_eq_pow_mul _ _
    have e2 : unit (L + j) = 2 ^ gammaLength s.clock * unit (L + j + gammaLength s.clock) :=
      unit_eq_pow_mul _ _
    rw [e1]
    conv_lhs => rw [e2]
    push_cast
    ring

/-- [proved-derived; formal-checked] **The re-base keeps the stored accumulation.** -/
theorem rebase_value_add_rem (s : Carried L E) (j : ℕ) (i : E) :
    (s.rebase j).value i + (s.rebase j).rem i = s.value i + s.rem i := by
  have h := div_rem_spec (L + j) (s.rem i)
  simp only [Carried.rebase]
  linarith

/-- [proved-derived; formal-checked] **The value moves by the remainder's lattice part.** -/
theorem rebase_shift (s : Carried L E) (j : ℕ) (i : E) :
    (s.rebase j).value i - s.value i = s.rem i - (s.rebase j).rem i := by
  have := rebase_value_add_rem s j i
  linarith

/-- [proved-derived; formal-checked] **A lattice value lands on the finer lattice.** -/
theorem rebase_onLattice (s : Carried L E) (j : ℕ) {i : E} (h : OnLattice L (s.value i)) :
    OnLattice (L + j) ((s.rebase j).value i) := by
  obtain ⟨a, ha⟩ := h.mono (Nat.le_add_right L j)
  refine ⟨a + quot (L + j) (s.rem i), ?_⟩
  simp only [Carried.rebase]
  rw [ha]
  push_cast
  ring

theorem rebase_clock (s : Carried L E) (j : ℕ) : (s.rebase j).clock = s.clock := rfl

end Rebase

/-! ## 2. The accounting and the release bound across a re-base -/

section Across

/-- [proved-derived; formal-checked] **`rebase_run_accounting`.** Deposits `Δs₁` at `L`, a re-base
by `j`, then deposits `Δs₂` at `L + j`: the final value and remainder plus both segments' releases
equal the starting value and remainder plus every exact update. -/
theorem rebase_run_accounting (s : Carried L E) (j : ℕ) (Δs₁ Δs₂ : List (E → ℚ)) (i : E) :
    (run ((run s Δs₁).rebase j) Δs₂).value i + (run ((run s Δs₁).rebase j) Δs₂).rem i +
        released s Δs₁ i + released ((run s Δs₁).rebase j) Δs₂ i =
      s.value i + s.rem i + (Δs₁.map (· i)).sum + (Δs₂.map (· i)).sum := by
  have h1 := run_accounting s Δs₁ i
  have h2 := run_accounting ((run s Δs₁).rebase j) Δs₂ i
  have hr := rebase_value_add_rem (run s Δs₁) j i
  linarith

/-- [proved-derived; formal-checked] **The two segments' releases share one Kraft sum.** Measured
in the unit before the re-base, they are at most `(u/2) Σ_(m ∈ (c₀, c₂]) 2^(−k_m)`. -/
theorem release_across_rebase_le (s : Carried L E) (j : ℕ) (Δs₁ Δs₂ : List (E → ℚ)) (i : E) :
    |released s Δs₁ i + released ((run s Δs₁).rebase j) Δs₂ i| ≤
      unit L / 2 * ∑ m ∈ Finset.Ioc s.clock (run ((run s Δs₁).rebase j) Δs₂).clock,
        gammaWeight m := by
  set t := (run s Δs₁).rebase j
  have h1 := released_le s Δs₁ i
  have h2 := released_le t Δs₂ i
  have hct : t.clock = (run s Δs₁).clock := rfl
  have hc1 := run_clock_ge s Δs₁
  have hc2 := run_clock_ge t Δs₂
  rw [hct] at h2 hc2
  have hfine : unit (L + j) / 2 ≤ unit L / 2 := by
    have := unit_eq_pow_mul L j
    have hp : (1 : ℚ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hu := unit_pos (L + j)
    nlinarith
  have hw : 0 ≤ ∑ m ∈ Finset.Ioc (run s Δs₁).clock (run t Δs₂).clock, gammaWeight m :=
    Finset.sum_nonneg fun m _ => gammaWeight_nonneg m
  have hsplit : ∑ m ∈ Finset.Ioc s.clock (run t Δs₂).clock, gammaWeight m =
      ∑ m ∈ Finset.Ioc s.clock (run s Δs₁).clock, gammaWeight m +
        ∑ m ∈ Finset.Ioc (run s Δs₁).clock (run t Δs₂).clock, gammaWeight m := by
    rw [← Finset.sum_union (Finset.disjoint_left.mpr fun m h1 h2 => by
      simp only [Finset.mem_Ioc] at h1 h2; omega)]
    congr 1
    ext m; simp only [Finset.mem_Ioc, Finset.mem_union]; omega
  rw [hsplit, mul_add]
  calc |released s Δs₁ i + released t Δs₂ i|
      ≤ |released s Δs₁ i| + |released t Δs₂ i| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_right hfine hw))

/-- [proved-derived; formal-checked] **`release_across_rebase_lt`.** Since the founding, across a
re-base, the releases at an entry total less than half the unit before the re-base. -/
theorem release_across_rebase_lt (s : Carried L E) (j : ℕ) (Δs₁ Δs₂ : List (E → ℚ)) (i : E) :
    |released s Δs₁ i + released ((run s Δs₁).rebase j) Δs₂ i| < unit L / 2 := by
  have hu : 0 < unit L / 2 := by have := unit_pos L; positivity
  calc _ ≤ _ := release_across_rebase_le s j Δs₁ Δs₂ i
    _ < unit L / 2 * 1 := mul_lt_mul_of_pos_left (gamma_window_lt_one _ _) hu
    _ = unit L / 2 := mul_one _

/-- [proved-derived; formal-checked] **`within_founding_unit_across_rebase`.** After a re-base the
value stays within `u/2 + u′/2` of the exact accumulation since the founding: the carried remainder
is in the finer half cell, and the releases are below half the coarser unit. -/
theorem within_founding_unit_across_rebase (s : Carried L E) (j : ℕ)
    (Δs₁ Δs₂ : List (E → ℚ)) (i : E) :
    |(run ((run s Δs₁).rebase j) Δs₂).value i -
        (s.value i + s.rem i + (Δs₁.map (· i)).sum + (Δs₂.map (· i)).sum)| <
      unit L / 2 + unit (L + j) / 2 := by
  have hacc := rebase_run_accounting s j Δs₁ Δs₂ i
  have hrel := release_across_rebase_lt s j Δs₁ Δs₂ i
  have hb := (run ((run s Δs₁).rebase j) Δs₂).rem_bounded i
  rw [abs_lt] at hrel ⊢
  constructor <;> linarith [hb.1, hb.2, hrel.1, hrel.2]

end Across

section Audit

#print axioms Carried.rebase
#print axioms rebase_value_add_rem
#print axioms rebase_shift
#print axioms rebase_onLattice
#print axioms rebase_run_accounting
#print axioms release_across_rebase_le
#print axioms release_across_rebase_lt
#print axioms within_founding_unit_across_rebase

end Audit

end Holonics.HNN.LatticeDeposit

end
