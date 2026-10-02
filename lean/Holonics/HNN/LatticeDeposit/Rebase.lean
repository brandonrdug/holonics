import Holonics.HNN.LatticeDeposit

/-!
# HNN.LatticeDeposit.Rebase: re-basing a carrier onto a finer lattice

[definition; agent-inferred] The confirmable grain of a running machine refines with its reading
count (`HNN/Ratio/Resolution.refiningGrain`, `L(N) = ⌈√(N ln 2/2)⌉`). It does not refine by integer
factors, so a schedule that keeps every coarser read is dyadic, `2^⌈log₂ L(N)⌉`
(`HNN/Ratio/Resolution.grainRead_of_refined`). A carrier on the lattice `2^(−L)ℤ` then moves to
`2^(−L−j)ℤ`. This module states that move for the lattice deposit's carrier (`HNN/LatticeDeposit`)
and proves that it loses nothing the carrier stored, over any number of re-bases. It is the item
#62 owed after PR #151. Its Rust owner is `hnn::constitution`'s `BudgetedCarry::rebase`, which
re-bases every array a locus carries before a deposit stages an entry, and at the machine
`Constitution::rebased`, which re-bases a contact's channel; the declared schedule keeps one lattice
per locus and never calls it.

**The re-base.** The carried remainder `r ∈ [−u/2, u/2)` is divided at the finer unit
`u′ = 2^(−L−j)`, `r = q′u′ + r′` with `r′ ∈ [−u′/2, u′/2)` (the owner's `div_rem_spec`). The value
takes the lattice part, `value′ = value + q′u′`, and the remainder `r′` is carried. The clock is kept,
so the precision schedule `k_m` continues. Nothing is released.

[proved-derived; formal-checked] What is proved.

1. **The re-base is exact** (`rebase_value_add_rem`, `rebase_shift`, `rebase_onLattice`,
   `rebase_clock`). `value′ + r′ = value + r` at every entry: the stored accumulation is unchanged.
   The value moves by `r − r′`, lands on the finer lattice, and the remainder is in the finer half
   cell and on the finer fine lattice of the same clock.
2. **Any history of deposits and re-bases** (`Move`, `Tracked`, `Invariant`, `invariant_deposit`,
   `invariant_rebase`, `invariant_history`). A history interleaves deposit runs on the current
   lattice with re-bases onto finer ones, as many as it likes. One invariant holds after every move:
   the stored accumulation plus the releases equals the founding accumulation plus the updates, and
   the releases are at most half the founding unit times the Kraft weight of the clocks since the
   founding. A deposit run keeps it because its releases are at most half its own unit times its
   clocks' weight (`released_le`), its unit is at most the founding one (`unit_anti`), and its
   clocks follow the earlier ones. A re-base keeps it because it keeps value plus carry and the
   clock and releases nothing.
3. **What every history guarantees** (`history_accounting`, `history_release_lt`,
   `history_within_founding_unit`). Re-bases add no term to the accounting. The releases since the
   founding total less than `u/2`, with `u` the founding unit, because the clock never resets and
   the Kraft sum over all its clocks is below one. The value stays within `u/2 + u_now/2` of the
   exact accumulation, with `u_now` the current unit.

[definition] **What this means for the contacts.** The bound is in the founding unit, not the
current one. After re-bases totalling `j` levels the half-cap at the current unit no longer holds:
the releases since the founding are below `u/2` and can come arbitrarily close to it (before any
re-base already, `Freeze.release_bound_tight`), which is just under `2^(j−1)` current units. So
under a refining grain a contact's dropped residuals stay bounded, but by the coarsest unit it was
carried on; measured in the current grain, that bound grows with every refinement.

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

/-! ## 2. Any history of deposits and re-bases -/

section History

/-- A coarser lattice has the larger unit. -/
theorem unit_anti {a b : ℕ} (h : a ≤ b) : unit b ≤ unit a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have e := unit_eq_pow_mul a k
  have hp : (1 : ℚ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hu := unit_pos (a + k)
  nlinarith

/-- [definition] **One move of a carrier's history**: a run of deposits on its current lattice, or
a re-base onto the lattice `j` levels finer. -/
inductive Move (E : Type*) where
  | deposit (Δs : List (E → ℚ))
  | rebase (j : ℕ)

/-- [definition] **A carrier with its history's totals**: its current lattice and carrier, and, per
entry, the exact updates and the releases since the history began. The totals are bookkeeping for
the statement, not state the machine keeps. -/
structure Tracked (E : Type*) where
  lat : ℕ
  carrier : Carried lat E
  acc : E → ℚ
  rel : E → ℚ

/-- [definition] The start of a history: the carrier, no updates, no releases. -/
def Tracked.start (s : Carried L E) : Tracked E := ⟨L, s, 0, 0⟩

/-- [definition] One move: a deposit run adds its updates and releases; a re-base adds neither. -/
noncomputable def Tracked.step (σ : Tracked E) : Move E → Tracked E
  | .deposit Δs => ⟨σ.lat, run σ.carrier Δs, fun i => σ.acc i + (Δs.map (· i)).sum,
      fun i => σ.rel i + released σ.carrier Δs i⟩
  | .rebase j => ⟨σ.lat + j, σ.carrier.rebase j, σ.acc, σ.rel⟩

/-- [definition] A history: the moves in order. -/
noncomputable def Tracked.history (σ : Tracked E) (ms : List (Move E)) : Tracked E :=
  ms.foldl Tracked.step σ

/-- [definition] **The invariant** against the founding carrier `s₀` on `2^(−L)ℤ`: the lattice is at
least as fine as the founding one, the clock has not gone back, the stored accumulation plus the
releases equals the founding accumulation plus the updates, and the releases are at most half the
founding unit times the Kraft weight of the clocks since the founding. -/
def Invariant (s₀ : Carried L E) (σ : Tracked E) : Prop :=
  L ≤ σ.lat ∧ s₀.clock ≤ σ.carrier.clock ∧ ∀ i,
    σ.carrier.value i + σ.carrier.rem i + σ.rel i = s₀.value i + s₀.rem i + σ.acc i ∧
    |σ.rel i| ≤ unit L / 2 * ∑ m ∈ Finset.Ioc s₀.clock σ.carrier.clock, gammaWeight m

theorem invariant_start (s₀ : Carried L E) : Invariant s₀ (Tracked.start s₀) := by
  refine ⟨le_refl _, le_refl _, fun i => ⟨?_, ?_⟩⟩ <;> simp [Tracked.start]

/-- [proved-derived; formal-checked] **A deposit run keeps the invariant.** Its releases are at most
half its own unit times the Kraft weight of its clocks (`released_le`); its unit is at most the
founding one, and its clocks follow the earlier ones. -/
theorem invariant_deposit {s₀ : Carried L E} {σ : Tracked E} (h : Invariant s₀ σ)
    (Δs : List (E → ℚ)) : Invariant s₀ (σ.step (.deposit Δs)) := by
  obtain ⟨hL, hc, hi⟩ := h
  have hc1 := run_clock_ge σ.carrier Δs
  refine ⟨hL, hc.trans hc1, fun i => ⟨?_, ?_⟩⟩
  · have hacc := run_accounting σ.carrier Δs i
    have := (hi i).1
    simp only [Tracked.step]
    linarith
  · simp only [Tracked.step]
    have hrel := released_le σ.carrier Δs i
    have hu : unit σ.lat / 2 ≤ unit L / 2 := by linarith [unit_anti hL]
    have hw : 0 ≤ ∑ m ∈ Finset.Ioc σ.carrier.clock (run σ.carrier Δs).clock, gammaWeight m :=
      Finset.sum_nonneg fun m _ => gammaWeight_nonneg m
    have hsplit : ∑ m ∈ Finset.Ioc s₀.clock (run σ.carrier Δs).clock, gammaWeight m =
        ∑ m ∈ Finset.Ioc s₀.clock σ.carrier.clock, gammaWeight m +
          ∑ m ∈ Finset.Ioc σ.carrier.clock (run σ.carrier Δs).clock, gammaWeight m := by
      rw [← Finset.sum_union (Finset.disjoint_left.mpr fun m h1 h2 => by
        simp only [Finset.mem_Ioc] at h1 h2; omega)]
      congr 1
      ext m; simp only [Finset.mem_Ioc, Finset.mem_union]; omega
    rw [hsplit, mul_add]
    calc |σ.rel i + released σ.carrier Δs i|
        ≤ |σ.rel i| + |released σ.carrier Δs i| := abs_add_le _ _
      _ ≤ _ := add_le_add (hi i).2 (hrel.trans (mul_le_mul_of_nonneg_right hu hw))

/-- [proved-derived; formal-checked] **A re-base keeps the invariant**: it keeps value plus carry and
the clock, and releases nothing. -/
theorem invariant_rebase {s₀ : Carried L E} {σ : Tracked E} (h : Invariant s₀ σ) (j : ℕ) :
    Invariant s₀ (σ.step (.rebase j)) := by
  obtain ⟨hL, hc, hi⟩ := h
  refine ⟨le_trans hL (Nat.le_add_right _ _), hc, fun i => ⟨?_, (hi i).2⟩⟩
  have := rebase_value_add_rem σ.carrier j i
  have := (hi i).1
  simp only [Tracked.step]
  linarith

/-- [proved-derived; formal-checked] **Every history keeps the invariant**, whatever its deposits
and however many re-bases. -/
theorem invariant_history {s₀ : Carried L E} {σ : Tracked E} (h : Invariant s₀ σ)
    (ms : List (Move E)) : Invariant s₀ (σ.history ms) := by
  induction ms generalizing σ with
  | nil => exact h
  | cons m ms ih =>
    have hstep : Invariant s₀ (σ.step m) := by
      cases m with
      | deposit Δs => exact invariant_deposit h Δs
      | rebase j => exact invariant_rebase h j
    exact ih hstep

/-- [proved-derived; formal-checked] **`history_accounting`.** After any history of deposits and
re-bases from `s₀`, the value and remainder plus the releases equal the founding value and remainder
plus every exact update: re-bases add no term. -/
theorem history_accounting (s₀ : Carried L E) (ms : List (Move E)) (i : E) :
    ((Tracked.start s₀).history ms).carrier.value i + ((Tracked.start s₀).history ms).carrier.rem i +
        ((Tracked.start s₀).history ms).rel i =
      s₀.value i + s₀.rem i + ((Tracked.start s₀).history ms).acc i :=
  ((invariant_history (invariant_start s₀) ms).2.2 i).1

/-- [proved-derived; formal-checked] **`history_release_lt`.** After any history of deposits and
re-bases, the releases at an entry since the founding total less than half the founding unit. -/
theorem history_release_lt (s₀ : Carried L E) (ms : List (Move E)) (i : E) :
    |((Tracked.start s₀).history ms).rel i| < unit L / 2 := by
  have h := ((invariant_history (invariant_start s₀) ms).2.2 i).2
  have hu : 0 < unit L / 2 := by have := unit_pos L; positivity
  calc _ ≤ _ := h
    _ < unit L / 2 * 1 := mul_lt_mul_of_pos_left (gamma_window_lt_one _ _) hu
    _ = unit L / 2 := mul_one _

/-- [proved-derived; formal-checked] **`history_within_founding_unit`.** After any history, the value
is within half the founding unit plus half the current unit of the exact accumulation since the
founding: the carried remainder lies in the current half cell, and the releases below the founding
half unit. -/
theorem history_within_founding_unit (s₀ : Carried L E) (ms : List (Move E)) (i : E) :
    |((Tracked.start s₀).history ms).carrier.value i - (s₀.value i + s₀.rem i +
        ((Tracked.start s₀).history ms).acc i)| <
      unit L / 2 + unit ((Tracked.start s₀).history ms).lat / 2 := by
  have hacc := history_accounting s₀ ms i
  have hrel := history_release_lt s₀ ms i
  have hb := ((Tracked.start s₀).history ms).carrier.rem_bounded i
  rw [abs_lt] at hrel ⊢
  constructor <;> linarith [hb.1, hb.2, hrel.1, hrel.2]

end History

section Audit

#print axioms Carried.rebase
#print axioms rebase_value_add_rem
#print axioms rebase_shift
#print axioms rebase_onLattice
#print axioms unit_anti
#print axioms invariant_deposit
#print axioms invariant_rebase
#print axioms invariant_history
#print axioms history_accounting
#print axioms history_release_lt
#print axioms history_within_founding_unit

end Audit

end Holonics.HNN.LatticeDeposit

end
