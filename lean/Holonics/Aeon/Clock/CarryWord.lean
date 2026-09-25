import Mathlib.NumberTheory.Rayleigh
import Holonics.Aeon.Clock.Lock
import Holonics.Aeon.Clock.Epoch
import Holonics.Geometry.Turn

/-!
# The carry word: the epochs of a rate-`α` clock read at the unit clock's sections

[definition] `docs/ELEMENTARY_OBJECTS.md` §3 (a helix is circle + carry) and §12, and §5 of
`research/records/2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS.md`.
Two clocks share one joint motion; the first advances `α` turns per turn of the second, and the
aeon of `n` ticks of the second reads `Lock.jointReading α n = (n α, n)`. Started at open phase
`ρ`, the first clock reads `helixReading α ρ n = n α + ρ`. Across the unit tick `n → n + 1` its
whole windings (`Winding.windings`) advance by

`carry α ρ n = windings((n + 1) α + ρ) − windings(n α + ρ) = windings α + Winding.carry (n α + ρ) α`,

the joint clock's carry (`carry_eq_windings_add_carry`, through `Winding.windings_add`). The word
`n ↦ carry α ρ n` is the classical mechanical word of slope `α` and intercept `ρ`: the epoch
reading of the rate-`α` clock at the unit clock's sections.

[proved-derived; formal-checked] What is proved.

1. **Helix = circle + carry.** Every letter is `windings α` or `windings α + 1` (`carry_mem`, from
   `Winding.carry_nonneg` and `Winding.carry_le_one`); below one turn per tick the letter is the
   joint clock's carry itself (`carry_eq_jointCarry`). The letters telescope to the windings of
   the reading (`sum_carry`, `sum_carry_eq_windings`), and two factors of equal length carry counts
   differing by at most one (`carry_balanced`).
2. **Periodicity ⇔ cycle.** The word is eventually periodic with period `T` exactly when the aeon
   of `T` ticks is a cycle of the joint clock, `Lock.IsCycle (jointReading α T)`, that is
   `T α ∈ ℤ` (`eventually_periodic_iff_isCycle`); a cycle carries its whole windings
   (`windings_add_of_isCycle`, `sum_carry_of_isCycle`). At the Farey address `p / q` the lock
   `Lock.lock_at_address`, a cycle of the real joint clock (`Lock.isCycle_of_rational`), is a
   period `q` of the word carrying `p` (`carry_periodic_of_rational`,
   `sum_carry_period_of_rational`), and with `p, q` coprime the periods are exactly the multiples
   of `q` (`eventually_periodic_rational_iff`, from `Lock.cycle_iff_period_dvd`). An irrational rate
   has no cycle (`Lock.no_cycle_of_irrational`), so its word never locks
   (`not_eventually_periodic_of_irrational`), and a word that never locks has an irrational rate
   (`never_locks_iff_irrational`): **the quasicrystal is an aeon of the joint clock with no
   cycle.** A lock strictly between two neighbouring locks has period at least their mediant's
   (`period_ge_mediant_of_between`, the owner `PairResonance.between_neighbours_costs_at_least_the_mediant`),
   and a crystal whose rate lies strictly between two consecutive convergents of an irrational
   rate recurs no sooner than their mediant (`period_ge_convergent_mediant`, the owner
   `Lock.between_consecutive_convergents_costs_the_mediant`); both read the addresses
   cross-multiplied against the cycle (`Lock.div_lt_rate_iff`, `Lock.rate_lt_div_iff`).
3. **The carry word is the aeon's epoch reading.** For `0 ≤ α < 1` the letter `1` marks an arrival:
   the tick `n` carries exactly when the rate-`α` clock crosses an integer section during it
   (`carry_eq_one_iff_arrival`). The arrivals are a certified section of the aeon of `N` unit
   ticks (`carrySection`); the epoch (`Epoch.epochOf`) of the micro-step `j` is the windings the
   reading has advanced (`epochOf_carrySection`), from an open phase `ρ ∈ [0, 1)` the windings
   `windings (j α + ρ)` themselves (`epochOf_carrySection_eq_windings`), and the aeon is cut into
   one more epoch than the windings it completes (`carrySection_epochs_attained`, over
   `Epoch.epochs_attained`). **The Odometer is the case `α = 1/n`:** from phase `0` the carry
   section of rate `1/n` is the digit clock's section `Epoch.digitTicks n N`
   (`carrySection_inv_eq_digitTicks`), so its epoch is the Odometer's upper digit and the whole
   windings of the reading (`odometer_counts_carrySection_epochs`, joining
   `Epoch.odometer_counts_epochs` to `epochOf_carrySection_eq_windings`).
4. **The rational join.** At rate `p / q` and phase `r / q` the letter is the Odometer's whole turns
   `PhaseCarry.winding q p` plus its carry `PhaseCarry.carry q (n p + r) p`
   (`carry_rational_eq_phaseCarry`, through `Winding.windings_of_microsteps` and
   `Winding.carry_of_microsteps`: the Aeon split commutes with the rational chart,
   `Winding.windings_ratCast`, `Winding.jointCarry_ratCast`).
5. **Tube, window and projection.** The lattice points `(n, m)` in the strip
   `n α + ρ − 1 < m ≤ n α + ρ` are exactly the whole windings of the reading (`mem_tube_iff`, from
   `Winding.split_unique`), one per tick (`existsUnique_mem_tube`), and in the internal coordinate
   `n α − m` the strip is the window `[−ρ, 1 − ρ)` (`internal_mem_window_iff`). The strip alone
   projects onto all of `ℤ`; the quasicrystal needs the physical projection `n + β m`, injective on
   `ℤ²` for irrational `β` (`physicalProjection_injective`), whose consecutive selected sites are
   spaced `1 + β s_n`, two lengths in the order of the carry word (`physicalSite_succ_sub`).
6. **The golden approximants** (joined to `Turn` §6). `F_(n+1) φ⁻¹ = F_n + goldenClockResidue (n+1)`
   (`fib_succ_mul_inv_goldenRatio`); the first `F_(n+1)` ticks of the rate-`φ⁻¹` word from phase `0`
   carry `F_n` for even `n` and `F_n − 1` for odd `n` (`sum_carry_golden_of_even`, `_of_odd`), and
   the crystal of rate `F_n / F_(n+1)` carries exactly `F_n` (`sum_carry_golden_crystal`). The
   Fibonacci fixed word of `0 ↦ 01, 1 ↦ 0` is the word of rate `φ⁻²` at intercept `φ⁻²`; the rate
   `φ⁻¹` from phase `0` used here is its complementary coding up to intercept and shift.
7. **Beatty and Wythoff positions** (joined to Mathlib `NumberTheory/Rayleigh`). For `0 < α < 1` at
   phase `0` the ones sit at `⌈k / α⌉ − 1` (the arrival at section `k`) and the zeros at
   `⌊k / (1 − α)⌋`; Rayleigh's complement theorem is the statement that the word partitions the
   ticks (`carry_eq_one_iff_beattySeq'`, `carry_eq_zero_iff_beattySeq`). At the golden rate these
   are the Wythoff pair `φ`, `φ²` (`carry_golden_iff`).

**Part of the line served.** Navigators: a rate clock; terrain: the unit clock's sections;
landmarks: locks at Farey addresses; kernel and cokernel: none stated here.

The computational object is the helical pair interaction: the unit clock and the rate-`α` clock
meeting on the torus of their joint motion. Of the six objects of the winding guide this module
touches the helix (circle + carry), the pair (torus with a modular address; a cycle is a lock),
faces and placement (the window face) and the tube (the strip); cell holonomy and the tower thread
stay attached and are not used here (the Odometer's tower of epochs is `Epoch.odometer_tower`).

[open] Owed, not proved here: the three-distance theorem (Sós, Świerczkowski, Surányi 1958) and
Sturmian factor complexity `n + 1` (Morse–Hedlund 1940); which receiver hears the projected point
set (the regular-model-set diffraction of Hof 1995) is not proved here.

No `axiom`, no `sorry`, no `native_decide`.
-/

set_option linter.dupNamespace false

namespace Holonics.Aeon.Clock.CarryWord

open Holonics.Aeon.Clock.Winding (windings openPhase windings_add reading_split split_unique
  windings_ratCast jointCarry_ratCast)
open Holonics.Aeon.Clock.Lock (jointReading IsCycle jointReading_isCycle_iff isCycle_ratCast_iff
  isCycle_of_rational div_lt_rate_iff rate_lt_div_iff)
open scoped BigOperators

/-! ## 1. The reading of the rate-`α` clock and its carry word -/

/-- [definition] **The reading of the rate-`α` clock** after `n` ticks of the unit clock, started
at open phase `ρ`: the first reading of the aeon `Lock.jointReading α n`, shifted by `ρ`. -/
noncomputable def helixReading (α ρ : ℝ) (n : ℤ) : ℝ := (jointReading α n).1 + ρ

/-- [proved-derived; formal-checked] The reading is `n α + ρ`. -/
theorem helixReading_eq (α ρ : ℝ) (n : ℤ) : helixReading α ρ n = n * α + ρ := rfl

/-- [proved-derived; formal-checked] `k` more unit ticks advance the reading by the joint reading
of `k` ticks. -/
theorem helixReading_add (α ρ : ℝ) (n k : ℤ) :
    helixReading α ρ (n + k) = helixReading α ρ n + (jointReading α k).1 := by
  simp only [helixReading_eq, jointReading]
  push_cast
  ring

/-- [proved-derived; formal-checked] One unit tick advances the reading by the rate. -/
theorem helixReading_succ (α ρ : ℝ) (n : ℤ) :
    helixReading α ρ (n + 1) = helixReading α ρ n + α := by
  rw [helixReading_add]
  simp [jointReading]

/-- [definition] **The carry word**: the whole windings the rate-`α` clock advances across the unit
tick `n → n + 1`. -/
noncomputable def carry (α ρ : ℝ) (n : ℤ) : ℤ :=
  windings (helixReading α ρ (n + 1)) - windings (helixReading α ρ n)

/-- [proved-derived; formal-checked] **The letter is the rate's whole windings plus the joint
clock's carry** (`Winding.windings_add`): `s_n = windings α + carry(n α + ρ, α)`. -/
theorem carry_eq_windings_add_carry (α ρ : ℝ) (n : ℤ) :
    carry α ρ n = windings α + Winding.carry (helixReading α ρ n) α := by
  rw [carry, helixReading_succ, windings_add]
  ring

/-- [proved-derived; formal-checked] **Every letter is `windings α` or `windings α + 1`**, since the
joint clock's carry is a single turn or none (`Winding.carry_nonneg`, `Winding.carry_le_one`). -/
theorem carry_mem (α ρ : ℝ) (n : ℤ) :
    carry α ρ n = windings α ∨ carry α ρ n = windings α + 1 := by
  have h0 := Winding.carry_nonneg (helixReading α ρ n) α
  have h1 := Winding.carry_le_one (helixReading α ρ n) α
  rw [carry_eq_windings_add_carry]
  omega

/-- [proved-derived; formal-checked] **Below one turn per tick the letter is the joint clock's
carry.** -/
theorem carry_eq_jointCarry {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) (n : ℤ) :
    carry α ρ n = Winding.carry (helixReading α ρ n) α := by
  have hα : windings α = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  rw [carry_eq_windings_add_carry, hα, zero_add]

/-- [proved-derived; formal-checked] Below one turn per tick the word is binary: a single turn or
none, as the Odometer's carry is. -/
theorem carry_mem_zero_one {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) (n : ℤ) :
    carry α ρ n = 0 ∨ carry α ρ n = 1 := by
  have hα : windings α = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  simpa [hα] using carry_mem α ρ n

/-! ## 2. The carries telescope to the windings, and the word is balanced -/

/-- [proved-derived; formal-checked] **The carries of `k` consecutive ticks sum to the windings the
reading advances across them.** Helix = circle + carry. -/
theorem sum_carry (α ρ : ℝ) (n : ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range k, carry α ρ (n + i) =
      windings (helixReading α ρ (n + k)) - windings (helixReading α ρ n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, carry]
    have h : n + ((k + 1 : ℕ) : ℤ) = n + k + 1 := by push_cast; ring
    rw [h]
    ring

/-- [proved-derived; formal-checked] From phase `0` the first `k` letters sum to the whole windings
of the joint reading of `k` ticks. -/
theorem sum_carry_eq_windings (α : ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range k, carry α 0 i = windings (jointReading α (k : ℤ)).1 := by
  have h := sum_carry α 0 0 k
  simp only [zero_add] at h
  rw [h, helixReading_eq, helixReading_eq]
  simp [jointReading, windings]

/-- [proved-derived; formal-checked] Over `k` ticks the reading advances by the whole windings of
the joint reading of `k` ticks, or one more, from any starting tick (`Winding.windings_add`). -/
theorem windings_advance_mem (α ρ : ℝ) (n : ℤ) (k : ℕ) :
    windings (helixReading α ρ (n + k)) - windings (helixReading α ρ n) =
        windings (jointReading α (k : ℤ)).1 ∨
      windings (helixReading α ρ (n + k)) - windings (helixReading α ρ n) =
        windings (jointReading α (k : ℤ)).1 + 1 := by
  have h0 := Winding.carry_nonneg (helixReading α ρ n) (jointReading α (k : ℤ)).1
  have h1 := Winding.carry_le_one (helixReading α ρ n) (jointReading α (k : ℤ)).1
  rw [helixReading_add, windings_add]
  omega

/-- [proved-derived; formal-checked] **The carry word is balanced.** Two factors of the same length
carry counts that differ by at most one: the helix spreads its crossings as evenly as the integer
sections allow. -/
theorem carry_balanced (α ρ : ℝ) (n m : ℤ) (k : ℕ) :
    |∑ i ∈ Finset.range k, carry α ρ (n + i) - ∑ i ∈ Finset.range k, carry α ρ (m + i)| ≤ 1 := by
  rw [sum_carry, sum_carry, abs_le]
  rcases windings_advance_mem α ρ n k with h | h <;>
    rcases windings_advance_mem α ρ m k with h' | h' <;>
    constructor <;> omega

/-! ## 3. Periodicity is a cycle of the joint clock -/

/-- [proved-derived; formal-checked] **A cycle carries its whole windings.** When the aeon of `q`
ticks is a cycle, `q` more ticks advance the reading's windings by exactly the cycle's whole
windings: the open phase of the cycle is zero, so the joint clock's carry vanishes. -/
theorem windings_add_of_isCycle {α : ℝ} {q : ℤ} (h : IsCycle (jointReading α q)) (ρ : ℝ)
    (n : ℤ) :
    windings (helixReading α ρ (n + q)) =
      windings (helixReading α ρ n) + windings (jointReading α q).1 := by
  rw [helixReading_add, windings_add]
  have hc : Winding.carry (helixReading α ρ n) (jointReading α q).1 = 0 := by
    have hz : Int.fract (jointReading α q).1 = 0 := h.1
    rw [Winding.carry, hz, add_zero, Int.floor_fract]
  rw [hc, add_zero]

/-- [proved-derived; formal-checked] **A cycle is a period of the word.** -/
theorem carry_add_period_of_isCycle {α : ℝ} {q : ℤ} (h : IsCycle (jointReading α q)) (ρ : ℝ)
    (n : ℤ) : carry α ρ (n + q) = carry α ρ n := by
  rw [carry, carry, show n + q + 1 = (n + 1) + q by ring, windings_add_of_isCycle h,
    windings_add_of_isCycle h]
  ring

/-- [proved-derived; formal-checked] Over one period of a cycle the word carries the cycle's whole
windings. -/
theorem sum_carry_of_isCycle {α : ℝ} {q : ℕ} (h : IsCycle (jointReading α (q : ℤ))) (ρ : ℝ)
    (n : ℤ) : ∑ i ∈ Finset.range q, carry α ρ (n + i) = windings (jointReading α (q : ℤ)).1 := by
  rw [sum_carry, windings_add_of_isCycle h]
  ring

/-- [proved-derived; formal-checked] **An eventual period is a cycle.** If the word repeats with
period `T` from some tick on, the aeon of `T` ticks is a cycle of the joint clock. The windings
advanced over one period are then constant, so the open phase left over `j` periods stays within
one crossing for every `j`, which only a zero open phase allows. -/
theorem isCycle_of_eventually_periodic {α ρ : ℝ} {T : ℕ} {N : ℤ}
    (hper : ∀ n ≥ N, carry α ρ (n + T) = carry α ρ n) :
    IsCycle (jointReading α (T : ℤ)) := by
  rw [jointReading_isCycle_iff]
  have hstep : ∀ n ≥ N, windings (helixReading α ρ (n + 1 + T)) -
      windings (helixReading α ρ (n + 1)) =
        windings (helixReading α ρ (n + T)) - windings (helixReading α ρ n) := by
    intro n hn
    have h := hper n hn
    rw [carry, carry] at h
    rw [show n + 1 + (T : ℤ) = n + T + 1 by ring]
    omega
  have hconst : ∀ j : ℕ, windings (helixReading α ρ (N + j + T)) -
      windings (helixReading α ρ (N + j)) =
        windings (helixReading α ρ (N + T)) - windings (helixReading α ρ N) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : N + ((j + 1 : ℕ) : ℤ) = N + j + 1 := by push_cast; ring
      rw [e, hstep _ (by omega), ih]
  obtain ⟨c, hc⟩ : ∃ c : ℤ,
      c = windings (helixReading α ρ (N + T)) - windings (helixReading α ρ N) := ⟨_, rfl⟩
  have hlin : ∀ j : ℕ,
      windings (helixReading α ρ (N + j * T)) = windings (helixReading α ρ N) + j * c := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h := hconst (j * T)
      have e1 : N + ((j * T : ℕ) : ℤ) = N + j * T := by push_cast; ring
      have e2 : N + ((j + 1 : ℕ) : ℤ) * T = N + j * T + T := by push_cast; ring
      rw [e1] at h
      rw [e2]
      push_cast
      rw [← hc] at h
      linear_combination h + ih
  refine ⟨c, ?_⟩
  rw [Int.cast_natCast]
  have hbound : ∀ j : ℕ, |(j : ℝ) * ((T : ℝ) * α - c)| < 1 := by
    intro j
    have hw : ⌊(N : ℝ) * α + ρ + j * (T * α)⌋ = ⌊(N : ℝ) * α + ρ⌋ + j * c := by
      have h := hlin j
      simp only [windings, helixReading_eq] at h
      rw [← h]
      congr 1
      push_cast
      ring
    have f1 := Int.floor_le ((N : ℝ) * α + ρ + j * (T * α))
    have f2 := Int.lt_floor_add_one ((N : ℝ) * α + ρ + j * (T * α))
    have g1 := Int.floor_le ((N : ℝ) * α + ρ)
    have g2 := Int.lt_floor_add_one ((N : ℝ) * α + ρ)
    rw [hw] at f1 f2
    push_cast at f1 f2
    rw [abs_lt, mul_sub]
    constructor <;> nlinarith
  by_contra hne
  have hpos : 0 < |(T : ℝ) * α - c| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / |(T : ℝ) * α - c|)
  have h := hbound j
  rw [abs_mul, Nat.abs_cast] at h
  rw [div_lt_iff₀ hpos] at hj
  linarith

/-- [proved-derived; formal-checked] **Periodicity ⇔ cycle.** The carry word is eventually periodic
with period `T` exactly when the aeon of `T` ticks is a cycle of the joint clock, that is when
`T α ∈ ℤ` (`Lock.jointReading_isCycle_iff`). -/
theorem eventually_periodic_iff_isCycle (α ρ : ℝ) (T : ℕ) :
    (∃ N : ℤ, ∀ n ≥ N, carry α ρ (n + T) = carry α ρ n) ↔ IsCycle (jointReading α (T : ℤ)) :=
  ⟨fun ⟨_, hper⟩ => isCycle_of_eventually_periodic hper,
    fun h => ⟨0, fun n _ => carry_add_period_of_isCycle h ρ n⟩⟩

/-- [proved-derived; formal-checked] **A rational rate is a lock: the crystal.** At rate `p / q`
the carry word repeats with period `q`, whatever the phase. -/
theorem carry_periodic_of_rational {α ρ : ℝ} {p : ℤ} {q : ℕ} (hq : 0 < q)
    (hα : α = (p : ℝ) / q) (n : ℤ) : carry α ρ (n + q) = carry α ρ n :=
  carry_add_period_of_isCycle (isCycle_of_rational hq hα) ρ n

/-- [proved-derived; formal-checked] Over one period of the lock `p / q` the word carries exactly
`p`: the crystal's windings per period are its numerator. -/
theorem sum_carry_period_of_rational {α ρ : ℝ} {p : ℤ} {q : ℕ} (hq : 0 < q)
    (hα : α = (p : ℝ) / q) (n : ℤ) : ∑ i ∈ Finset.range q, carry α ρ (n + i) = p := by
  rw [sum_carry_of_isCycle (isCycle_of_rational hq hα)]
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have h1 : (jointReading α (q : ℤ)).1 = p := by
    simp only [jointReading, hα, Int.cast_natCast]
    field_simp
  rw [h1]
  exact Int.floor_intCast p

/-- [proved-derived; formal-checked] **The lock's periods.** With `p` and `q` coprime the word of
rate `p / q` is eventually periodic with period `T` exactly when `q ∣ T`
(`Lock.cycle_iff_period_dvd`). -/
theorem eventually_periodic_rational_iff {p : ℤ} {q : ℕ} (hq : 0 < q)
    (hcop : IsCoprime (q : ℤ) p) (ρ : ℝ) (T : ℕ) :
    (∃ N : ℤ, ∀ n ≥ N, carry ((p : ℝ) / q) ρ (n + T) = carry ((p : ℝ) / q) ρ n) ↔ q ∣ T := by
  rw [eventually_periodic_iff_isCycle, show ((p : ℝ) / q) = (((p : ℚ) / q : ℚ) : ℝ) by norm_cast,
    isCycle_ratCast_iff, Lock.cycle_iff_period_dvd p q hq hcop]
  exact Int.natCast_dvd_natCast

/-- [proved-derived; formal-checked] **An irrational rate never locks.** The joint clock has no
cycle (`Lock.no_cycle_of_irrational`), so the word is not periodic from any tick on: the helix is a
one-dimensional quasicrystal rather than a crystal. -/
theorem not_eventually_periodic_of_irrational {α : ℝ} (hα : Irrational α) (ρ : ℝ) {T : ℕ}
    (hT : 0 < T) (N : ℤ) : ¬ ∀ n ≥ N, carry α ρ (n + T) = carry α ρ n := fun hper =>
  Lock.no_cycle_of_irrational hα (by exact_mod_cast hT.ne' : (T : ℤ) ≠ 0)
    (isCycle_of_eventually_periodic hper)

/-- [proved-derived; formal-checked] **The quasicrystal is an aeon of the joint clock with no
cycle.** The word never locks exactly when the rate is irrational: a rational rate `a / b` locks
with period `b`. -/
theorem never_locks_iff_irrational (α ρ : ℝ) :
    (∀ T : ℕ, 0 < T → ¬ ∃ N : ℤ, ∀ n ≥ N, carry α ρ (n + T) = carry α ρ n) ↔ Irrational α := by
  constructor
  · intro h
    by_contra hα
    obtain ⟨x, hx⟩ : α ∈ Set.range ((↑) : ℚ → ℝ) := by
      simpa [Irrational] using hα
    refine h x.den x.pos ((eventually_periodic_iff_isCycle α ρ x.den).mpr ?_)
    rw [jointReading_isCycle_iff]
    refine ⟨x.num, ?_⟩
    rw [← hx]
    have h' : (x.den : ℚ) * x = x.num := by rw [mul_comm]; exact Rat.mul_den_eq_num x
    exact_mod_cast h'
  · rintro hα T hT ⟨N, hper⟩
    exact not_eventually_periodic_of_irrational hα ρ hT N hper

/-- [proved-derived; formal-checked] **A lock strictly between two neighbouring locks recurs no
sooner than their mediant.** If the word locks with period `T` and its rate lies strictly between
the neighbouring locks `p / q` and `p' / q'` (`p' q − p q' = 1`), then `T ≥ q + q'`: the eventual
period is a cycle, and the mediant is the cheapest cycle in the gap
(`PairResonance.between_neighbours_costs_at_least_the_mediant`). -/
theorem period_ge_mediant_of_between {α ρ : ℝ} {T : ℕ} {N : ℤ}
    (hper : ∀ n ≥ N, carry α ρ (n + T) = carry α ρ n) (hT : 0 < T)
    {p q p' q' : ℤ} (hq : 0 < q) (hq' : 0 < q') (hadj : p' * q - p * q' = 1)
    (hleft : (p : ℝ) / q < α) (hright : α < (p' : ℝ) / q') :
    q + q' ≤ T := by
  obtain ⟨c, hc⟩ := (jointReading_isCycle_iff α (T : ℤ)).mp (isCycle_of_eventually_periodic hper)
  rw [Int.cast_natCast] at hc
  exact Geometry.PairResonance.between_neighbours_costs_at_least_the_mediant p q p' q' c T hq hq'
    hadj ((div_lt_rate_iff hc hT hq).mp hleft) ((rate_lt_div_iff hc hT hq').mp hright)

/-- [proved-derived; formal-checked] **The crystals between consecutive convergents.** A carry word
that locks with period `T` at a rate `β` strictly between two consecutive convergents `P / Q`,
`P' / Q'` of an irrational `α` has `T ≥ Q + Q'`
(`Lock.between_consecutive_convergents_costs_the_mediant`): a crystal approximating the
quasicrystal of rate `α` more finely than its convergents recurs no sooner than their mediant. -/
theorem period_ge_convergent_mediant {α β ρ : ℝ} (hα : Irrational α) (n : ℕ) {P Q P' Q' : ℤ}
    (hP : (GenContFract.of α).nums n = P) (hQ : (GenContFract.of α).dens n = Q)
    (hP' : (GenContFract.of α).nums (n + 1) = P') (hQ' : (GenContFract.of α).dens (n + 1) = Q')
    {T : ℕ} {N : ℤ} (hper : ∀ m ≥ N, carry β ρ (m + T) = carry β ρ m) (hT : 0 < T)
    (hbetween : ((P : ℝ) / Q < β ∧ β < (P' : ℝ) / Q') ∨ ((P' : ℝ) / Q' < β ∧ β < (P : ℝ) / Q)) :
    Q + Q' ≤ T := by
  obtain ⟨c, hc⟩ := (jointReading_isCycle_iff β (T : ℤ)).mp (isCycle_of_eventually_periodic hper)
  rw [Int.cast_natCast] at hc
  have hQpos : 0 < Q := by exact_mod_cast hQ ▸ Lock.dens_pos α n
  have hQ'pos : 0 < Q' := by exact_mod_cast hQ' ▸ Lock.dens_pos α (n + 1)
  refine Lock.between_consecutive_convergents_costs_the_mediant hα n hP hQ hP' hQ' c T
    (by exact_mod_cast hT) ?_
  rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨(div_lt_rate_iff hc hT hQpos).mp h1, (rate_lt_div_iff hc hT hQ'pos).mp h2⟩
  · exact Or.inr ⟨(div_lt_rate_iff hc hT hQ'pos).mp h1, (rate_lt_div_iff hc hT hQpos).mp h2⟩

/-! ## 4. The carry word is the aeon's epoch reading -/

/-- [proved-derived; formal-checked] **A carry is an arrival.** Below one turn per tick, the tick
`n` carries exactly when the rate-`α` clock crosses an integer section `m` during it:
`n α + ρ < m ≤ (n + 1) α + ρ`. -/
theorem carry_eq_one_iff_arrival {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) (n : ℤ) :
    carry α ρ n = 1 ↔
      ∃ m : ℤ, helixReading α ρ n < m ∧ (m : ℝ) ≤ helixReading α ρ (n + 1) := by
  constructor
  · intro h
    refine ⟨windings (helixReading α ρ (n + 1)), ?_, Int.floor_le _⟩
    have e : windings (helixReading α ρ n) < windings (helixReading α ρ (n + 1)) := by
      rw [carry] at h
      omega
    exact Int.floor_lt.mp e
  · rintro ⟨m, hlo, hhi⟩
    have a1 : windings (helixReading α ρ n) < m := Int.floor_lt.mpr hlo
    have a2 : m ≤ windings (helixReading α ρ (n + 1)) := Int.le_floor.mpr hhi
    rcases carry_mem_zero_one h0 h1 ρ n with h | h
    · rw [carry] at h
      omega
    · exact h

/-- [definition] **The carry section** of the aeon of `N` unit ticks: the interior micro-states `j`
at which the rate-`α` clock has just arrived on an integer section, that is the tick `j − 1`
carried. Its ticks lie strictly inside the aeon, so it is a certified section. -/
noncomputable def carrySection (α ρ : ℝ) (N : ℕ) : Epoch.CertifiedSection N :=
  ⟨(Finset.Ioo 0 N).filter (fun j => carry α ρ ((j : ℤ) - 1) = 1), Finset.filter_subset _ _⟩

/-- [proved-derived; formal-checked] The micro-state `j + 1` is a tick of the carry section exactly
when the tick `j` carries. -/
theorem succ_mem_carrySection_iff {α ρ : ℝ} {N j : ℕ} (hj : j + 1 < N) :
    j + 1 ∈ (carrySection α ρ N).ticks ↔ carry α ρ j = 1 := by
  simp only [carrySection, Finset.mem_filter, Finset.mem_Ioo, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right]
  exact ⟨fun h => h.2, fun h => ⟨⟨Nat.succ_pos j, hj⟩, h⟩⟩

/-- [proved-derived; formal-checked] **The epoch count is the winding.** Below one turn per tick,
the epoch of the micro-step `j` at the carry section is the whole windings the rate-`α` clock has
advanced since the aeon began. -/
theorem epochOf_carrySection {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) {N j : ℕ} (hj : j < N) :
    (Epoch.epochOf (carrySection α ρ N).ticks j : ℤ) =
      windings (helixReading α ρ j) - windings (helixReading α ρ 0) := by
  induction j with
  | zero =>
    have hz : Epoch.epochOf (carrySection α ρ N).ticks 0 = 0 := by
      rw [Epoch.epochOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t ht htle
      have := Finset.mem_Ioo.mp ((carrySection α ρ N).inside ht)
      omega
    simp [hz]
  | succ j ih =>
    have ih' := ih (by omega)
    have hstep : windings (helixReading α ρ ((j + 1 : ℕ) : ℤ)) =
        windings (helixReading α ρ j) + carry α ρ j := by
      rw [carry]
      push_cast
      ring
    rw [Epoch.epochOf_succ, hstep]
    rcases carry_mem_zero_one h0 h1 ρ j with hc | hc
    · have hn : j + 1 ∉ (carrySection α ρ N).ticks := by
        rw [succ_mem_carrySection_iff hj, hc]
        decide
      rw [if_neg hn]
      push_cast
      rw [ih', hc]
      ring
    · have hn : j + 1 ∈ (carrySection α ρ N).ticks := (succ_mem_carrySection_iff hj).mpr hc
      rw [if_pos hn]
      push_cast
      rw [ih', hc]
      ring

/-- [proved-derived; formal-checked] **The carry word is the aeon's epoch reading.** From an open
phase `ρ ∈ [0, 1)` and below one turn per tick, the epoch of the micro-step `j` at the carry
section is the whole windings `windings (j α + ρ)` of the reading. -/
theorem epochOf_carrySection_eq_windings {α ρ : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {N j : ℕ} (hj : j < N) :
    (Epoch.epochOf (carrySection α ρ N).ticks j : ℤ) = windings (helixReading α ρ j) := by
  rw [epochOf_carrySection h0 h1 ρ hj]
  have hz : windings (helixReading α ρ 0) = 0 := by
    rw [helixReading_eq, Int.cast_zero, zero_mul, zero_add]
    exact Int.floor_eq_zero_iff.mpr ⟨hρ0, hρ1⟩
  rw [hz, sub_zero]

/-- [proved-derived; formal-checked] The carry section of the aeon of `N` unit ticks has as many
ticks as the windings completed over it. -/
theorem card_carrySection {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) {N : ℕ} (hN : 0 < N) :
    ((carrySection α ρ N).ticks.card : ℤ) =
      windings (helixReading α ρ ((N - 1 : ℕ) : ℤ)) - windings (helixReading α ρ 0) := by
  have hlast : Epoch.epochOf (carrySection α ρ N).ticks (N - 1) = (carrySection α ρ N).ticks.card := by
    rw [Epoch.epochOf, Finset.filter_true_of_mem]
    intro t ht
    have := Finset.mem_Ioo.mp ((carrySection α ρ N).inside ht)
    omega
  rw [← hlast]
  exact epochOf_carrySection h0 h1 ρ (by omega)

/-- [proved-derived; formal-checked] **The carry section cuts the aeon into one more epoch than the
windings it completes** (`Epoch.epochs_attained`). -/
theorem carrySection_epochs_attained {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (ρ : ℝ) {N : ℕ}
    (hN : 0 < N) :
    (Finset.range N).image (Epoch.epochOf (carrySection α ρ N).ticks) =
        Finset.range ((carrySection α ρ N).ticks.card + 1) ∧
      ((carrySection α ρ N).ticks.card : ℤ) =
        windings (helixReading α ρ ((N - 1 : ℕ) : ℤ)) - windings (helixReading α ρ 0) :=
  ⟨Epoch.epochs_attained _ hN, card_carrySection h0 h1 ρ hN⟩

/-- [proved-derived; formal-checked] At rate `1/n` from phase `0` the reading after `m` unit ticks
has the whole windings of `m` micro-steps of a ring of `n` steps, the Odometer's
`PhaseCarry.winding n m` (`Winding.windings_ratCast`, `Winding.windings_of_microsteps`). -/
theorem windings_helixReading_inv (n : ℕ) (m : ℕ) :
    windings (helixReading (1 / n : ℝ) 0 m) = (Geometry.PhaseCarry.winding n m : ℤ) := by
  have e : helixReading (1 / n : ℝ) 0 m = (((m : ℚ) / n : ℚ) : ℝ) := by
    rw [helixReading_eq]
    push_cast
    ring
  rw [e, windings_ratCast, Winding.windings_of_microsteps]

/-- [proved-derived; formal-checked] **At rate `1/n` the carry section is the digit clock's
section.** From phase `0` the rate-`1/n` clock arrives on an integer section at the micro-state
`j` exactly when `n ∣ j`, so its carry section is `Epoch.digitTicks n N`, the ticks of the
Odometer of base `n` (`Nat.succ_div`: `(i + 1)/n − i/n` is one exactly when `n ∣ i + 1`). At
`n = 0` both are empty. -/
theorem carrySection_inv_eq_digitTicks (n N : ℕ) :
    (carrySection (1 / n : ℝ) 0 N).ticks = Epoch.digitTicks n N := by
  ext j
  simp only [carrySection, Epoch.digitTicks, Finset.mem_filter]
  refine and_congr_right fun hj => ?_
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by have := (Finset.mem_Ioo.mp hj).1; omega⟩
  have hc : carry (1 / n : ℝ) 0 (((i + 1 : ℕ) : ℤ) - 1) =
      if n ∣ i + 1 then 1 else 0 := by
    have hi : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := by push_cast; ring
    have hs : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hi, carry, hs, windings_helixReading_inv, windings_helixReading_inv,
      Geometry.PhaseCarry.winding, Geometry.PhaseCarry.winding, Nat.succ_div]
    split_ifs <;> push_cast <;> ring
  rw [hc]
  split_ifs with h <;> simp [h]

/-- [proved-derived; formal-checked] **The Odometer is the carry word at rate `1/n`.** From phase
`0` the epoch of the micro-step `j` at the carry section of rate `1/n` is the Odometer's upper digit
after `j` steps (`Epoch.odometer_counts_epochs`, through `carrySection_inv_eq_digitTicks`), and it
is the whole windings of the reading. For `n ≥ 2` the second equality is the case `α = 1/n`,
`ρ = 0` of `epochOf_carrySection_eq_windings`; here it is derived from the Odometer
(`Epoch.epochOf_digitTicks`), and it holds at `n = 1` as well. -/
theorem odometer_counts_carrySection_epochs {n N j : ℕ} (hn : 0 < n) (hj : j < N) :
    Epoch.epochOf (carrySection (1 / n : ℝ) 0 N).ticks j =
        ((Geometry.PhaseCarry.odometer n)^[j] (0, 0)).2 ∧
      (Epoch.epochOf (carrySection (1 / n : ℝ) 0 N).ticks j : ℤ) =
        windings (helixReading (1 / n : ℝ) 0 j) := by
  rw [carrySection_inv_eq_digitTicks]
  refine ⟨(Epoch.odometer_counts_epochs n N j hn hj).1.symm, ?_⟩
  rw [Epoch.epochOf_digitTicks n N j hj, windings_helixReading_inv]

/-! ## 5. The rational join: the real helix at a rational rate is the Odometer -/

/-- [proved-derived; formal-checked] **The real helix at a rational rate is the Odometer.** At rate
`p / q` and phase `r / q` the letter of the tick `n` is the whole turns `PhaseCarry.winding q p` of
the rate plus the Odometer's carry `PhaseCarry.carry q (n p + r) p` of adding the rate's phase `p`
to the lattice position `n p + r` on the circle of `q` steps (`Winding.windings_of_microsteps`,
`Winding.carry_of_microsteps`). -/
theorem carry_rational_eq_phaseCarry (p q r n : ℕ) (hq : 0 < q) :
    carry ((p : ℝ) / q) ((r : ℝ) / q) n =
      (Geometry.PhaseCarry.winding q p : ℤ) + (Geometry.PhaseCarry.carry q (n * p + r) p : ℤ) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have e1 : ((p : ℝ) / q) = (((p : ℚ) / q : ℚ) : ℝ) := by
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  have e2 : helixReading ((p : ℝ) / q) ((r : ℝ) / q) n = ((((n * p + r : ℕ) : ℚ) / q : ℚ) : ℝ) := by
    rw [helixReading_eq]
    push_cast
    ring
  rw [carry_eq_windings_add_carry, e2, e1, windings_ratCast, jointCarry_ratCast,
    Winding.windings_of_microsteps, Winding.carry_of_microsteps]

/-- [proved-derived; formal-checked] Below one turn per tick (`p < q`) the letter at a rational rate
is exactly the Odometer's carry. -/
theorem carry_rational_eq_phaseCarry_of_lt (p q r n : ℕ) (hpq : p < q) :
    carry ((p : ℝ) / q) ((r : ℝ) / q) n = (Geometry.PhaseCarry.carry q (n * p + r) p : ℤ) := by
  rw [carry_rational_eq_phaseCarry p q r n (by omega), Geometry.PhaseCarry.winding,
    Nat.div_eq_of_lt hpq]
  simp

/-! ## 6. Cut and project: the window face selects the pathways -/

/-- [proved-derived; formal-checked] **The lattice points in the tube are the reading's whole
windings.** A lattice point `(n, m)` lies in the strip `n α + ρ − 1 < m ≤ n α + ρ` exactly when `m`
is the whole windings of the reading, its offset being the open phase (`Winding.split_unique`,
`Winding.reading_split`). The lattice gives the pathways; the window face selects them. -/
theorem mem_tube_iff (α ρ : ℝ) (n m : ℤ) :
    (helixReading α ρ n - 1 < m ∧ (m : ℝ) ≤ helixReading α ρ n) ↔
      m = windings (helixReading α ρ n) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact (split_unique (t := helixReading α ρ n) m (helixReading α ρ n - m) (by ring)
      (by linarith) (by linarith)).1
  · rintro rfl
    obtain ⟨hs, h0, h1⟩ := reading_split (helixReading α ρ n)
    constructor <;> linarith

/-- [proved-derived; formal-checked] Each tick selects exactly one lattice point of the tube: the
window face has unit height, so the projected pathway is a graph. -/
theorem existsUnique_mem_tube (α ρ : ℝ) (n : ℤ) :
    ∃! m : ℤ, helixReading α ρ n - 1 < m ∧ (m : ℝ) ≤ helixReading α ρ n :=
  ⟨windings (helixReading α ρ n), (mem_tube_iff α ρ n _).mpr rfl,
    fun m hm => (mem_tube_iff α ρ n m).mp hm⟩

/-- [proved-derived; formal-checked] **The strip is a window in the internal coordinate.** The
selected lattice point is the one whose internal coordinate `n α − m`, read on the joint reading,
lies in `[−ρ, 1 − ρ)`. -/
theorem internal_mem_window_iff (α ρ : ℝ) (n m : ℤ) :
    (-ρ ≤ (jointReading α n).1 - m ∧ (jointReading α n).1 - m < 1 - ρ) ↔
      m = windings (helixReading α ρ n) := by
  rw [← mem_tube_iff, helixReading]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- [definition] **The physical projection** of the lattice point selected at tick `n`:
`n + β ⌊n α + ρ⌋`. With `β` irrational the projection `(n, m) ↦ n + β m` is injective on `ℤ²`
(`physicalProjection_injective`). -/
noncomputable def physicalSite (β α ρ : ℝ) (n : ℤ) : ℝ := n + β * windings (helixReading α ρ n)

/-- [proved-derived; formal-checked] **An irrational physical slope separates the lattice.**
`n + β m = n' + β m'` with `β` irrational forces `(n, m) = (n', m')`: distinct pathways project to
distinct physical sites. -/
theorem physicalProjection_injective {β : ℝ} (hβ : Irrational β) {n m n' m' : ℤ}
    (h : (n : ℝ) + β * m = n' + β * m') : n = n' ∧ m = m' := by
  by_cases hm : m = m'
  · subst hm
    refine ⟨?_, rfl⟩
    exact_mod_cast (add_right_cancel h)
  · exfalso
    have hne : ((m : ℝ) - m') ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hm)
    have hβeq : β = ((n' - n : ℤ) : ℝ) / ((m - m' : ℤ) : ℝ) := by
      push_cast
      field_simp
      linarith
    exact hβ ⟨((n' - n : ℤ) : ℚ) / ((m - m' : ℤ) : ℚ), by rw [hβeq]; push_cast; ring⟩

/-- [proved-derived; formal-checked] **The projected sites are spaced by the carry word.**
Consecutive sites differ by `1 + β s_n`: the pathways chosen by the window face, read in the
physical line, form a point set with two spacings (`1` and `1 + β` when `0 ≤ α < 1`) in the order
of the carry word. -/
theorem physicalSite_succ_sub (β α ρ : ℝ) (n : ℤ) :
    physicalSite β α ρ (n + 1) - physicalSite β α ρ n = 1 + β * carry α ρ n := by
  simp only [physicalSite, carry]
  push_cast
  ring

/-! ## 7. The golden approximants -/

/-- [proved-standard; formal-checked] `φ⁻¹ = φ − 1`. -/
theorem inv_goldenRatio_eq : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
  rw [Real.inv_goldenRatio]
  have h := Real.goldenRatio_add_goldenConj
  linarith

/-- [proved-derived; formal-checked] **The golden phase error is the golden clock residue.**
`F_(n+1) φ⁻¹ = F_n + goldenClockResidue (n + 1)`: the crystal of rate `F_n / F_(n+1)` misses the
golden helix after `F_(n+1)` ticks by the residue of `Turn` §6. -/
theorem fib_succ_mul_inv_goldenRatio (n : ℕ) :
    (Nat.fib (n + 1) : ℝ) * Real.goldenRatio⁻¹ =
      Nat.fib n + Geometry.Turn.goldenClockResidue (n + 1) := by
  unfold Geometry.Turn.goldenClockResidue
  rw [inv_goldenRatio_eq]
  have h : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  rw [h]
  push_cast
  ring

/-- [proved-derived; formal-checked] The golden residue at a positive index is less than one turn
in size. -/
theorem goldenRatio_inv_pow_mem (n : ℕ) :
    0 < Real.goldenRatio⁻¹ ^ (n + 1) ∧ Real.goldenRatio⁻¹ ^ (n + 1) < 1 := by
  have h0 : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have h1 : Real.goldenRatio⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  exact ⟨pow_pos h0 _, pow_lt_one₀ h0.le h1 (Nat.succ_ne_zero n)⟩

/-- [proved-derived; formal-checked] For even `n` the golden residue at `n + 1` is positive, so the
golden helix completes `F_n` windings in `F_(n+1)` ticks: the quasicrystal keeps pace with the
crystal. -/
theorem windings_fib_succ_mul_inv_goldenRatio_of_even {n : ℕ} (hn : Even n) :
    windings ((Nat.fib (n + 1) : ℝ) * Real.goldenRatio⁻¹) = Nat.fib n := by
  rw [fib_succ_mul_inv_goldenRatio, Geometry.Turn.goldenClock_oriented_residue, windings,
    Int.floor_eq_iff]
  have hs : Even (n + 1 + 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k + 1, by omega⟩
  rw [hs.neg_one_pow]
  obtain ⟨h0, h1⟩ := goldenRatio_inv_pow_mem n
  push_cast
  constructor <;> linarith

/-- [proved-derived; formal-checked] For odd `n` the golden residue at `n + 1` is negative, so the
golden helix completes `F_n − 1` windings in `F_(n+1)` ticks: the quasicrystal lags the crystal by
one crossing. -/
theorem windings_fib_succ_mul_inv_goldenRatio_of_odd {n : ℕ} (hn : Odd n) :
    windings ((Nat.fib (n + 1) : ℝ) * Real.goldenRatio⁻¹) = (Nat.fib n : ℤ) - 1 := by
  rw [fib_succ_mul_inv_goldenRatio, Geometry.Turn.goldenClock_oriented_residue, windings,
    Int.floor_eq_iff]
  have hs : Odd (n + 1 + 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k + 1, by omega⟩
  rw [hs.neg_one_pow]
  obtain ⟨h0, h1⟩ := goldenRatio_inv_pow_mem n
  push_cast
  constructor <;> linarith

/-- [proved-derived; formal-checked] The first `F_(n+1)` ticks of the golden helix from phase `0`
carry the windings of `F_(n+1) φ⁻¹`. -/
theorem sum_carry_golden (n : ℕ) :
    ∑ i ∈ Finset.range (Nat.fib (n + 1)), carry Real.goldenRatio⁻¹ 0 i =
      windings ((Nat.fib (n + 1) : ℝ) * Real.goldenRatio⁻¹) := by
  rw [sum_carry_eq_windings]
  simp [jointReading]

/-- [proved-derived; formal-checked] **The golden quasicrystal at an even approximant.** Over the
first `F_(n+1)` ticks the golden word carries `F_n`, as its crystal approximant does. -/
theorem sum_carry_golden_of_even {n : ℕ} (hn : Even n) :
    ∑ i ∈ Finset.range (Nat.fib (n + 1)), carry Real.goldenRatio⁻¹ 0 i = Nat.fib n := by
  rw [sum_carry_golden, windings_fib_succ_mul_inv_goldenRatio_of_even hn]

/-- [proved-derived; formal-checked] **The golden quasicrystal at an odd approximant.** Over the
first `F_(n+1)` ticks the golden word carries `F_n − 1`, one crossing short of its crystal
approximant: the residue's orientation alternates with the parity. -/
theorem sum_carry_golden_of_odd {n : ℕ} (hn : Odd n) :
    ∑ i ∈ Finset.range (Nat.fib (n + 1)), carry Real.goldenRatio⁻¹ 0 i =
      (Nat.fib n : ℤ) - 1 := by
  rw [sum_carry_golden, windings_fib_succ_mul_inv_goldenRatio_of_odd hn]

/-- [proved-derived; formal-checked] **The golden crystal approximant.** At rate `F_n / F_(n+1)`
the word is a lock of period `F_(n+1)` carrying exactly `F_n` per period, from any tick and phase.
-/
theorem sum_carry_golden_crystal (n : ℕ) (ρ : ℝ) (m : ℤ) :
    ∑ i ∈ Finset.range (Nat.fib (n + 1)),
        carry ((Nat.fib n : ℝ) / Nat.fib (n + 1)) ρ (m + i) = Nat.fib n :=
  sum_carry_period_of_rational (p := (Nat.fib n : ℤ)) (Nat.fib_pos.mpr (Nat.succ_pos n))
    (by push_cast; rfl) m

/-! ## 8. Beatty positions and Rayleigh's partition -/

/-- [proved-derived; formal-checked] **The ones of the word sit on a Beatty sequence.** For
`0 < α < 1` and phase `0`, the tick `n` carries exactly when `n = ⌈k / α⌉ − 1` for some integer
`k`: it is the tick of the arrival at the section `k` (`carry_eq_one_iff_arrival`). -/
theorem carry_eq_one_iff_beattySeq' {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (n : ℤ) :
    carry α 0 n = 1 ↔ ∃ k : ℤ, beattySeq' α⁻¹ k = n := by
  rw [carry_eq_one_iff_arrival h0.le h1]
  refine exists_congr fun k => ?_
  rw [helixReading_eq, helixReading_eq, beattySeq', sub_eq_iff_eq_add, Int.ceil_eq_iff,
    ← div_eq_mul_inv, lt_div_iff₀ h0, div_le_iff₀ h0]
  push_cast
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith

/-- [proved-derived; formal-checked] **The zeros of the word sit on the complementary Beatty
sequence** `⌊k / (1 − α)⌋`. With the previous theorem this is Rayleigh's complement theorem
(`compl_beattySeq'`, `1/α⁻¹ + 1/(1 − α)⁻¹ = 1`): the carry word partitions the ticks. -/
theorem carry_eq_zero_iff_beattySeq {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (n : ℤ) :
    carry α 0 n = 0 ↔ ∃ k : ℤ, beattySeq (1 - α)⁻¹ k = n := by
  have hc := compl_beattySeq' (Real.HolderConjugate.inv_one_sub_inv h0 h1)
  have hmem : (∃ k : ℤ, beattySeq (1 - α)⁻¹ k = n) ↔ ¬ ∃ k : ℤ, beattySeq' α⁻¹ k = n := by
    change n ∈ {x | ∃ k, beattySeq (1 - α)⁻¹ k = x} ↔ n ∉ {x | ∃ k, beattySeq' α⁻¹ k = x}
    rw [← hc]
    rfl
  rw [hmem, ← carry_eq_one_iff_beattySeq' h0 h1]
  rcases carry_mem_zero_one h0.le h1 0 n with h | h <;> simp [h]

/-- [proved-standard; formal-checked] `(1 − φ⁻¹)⁻¹ = φ²`. -/
theorem inv_one_sub_inv_goldenRatio : (1 - Real.goldenRatio⁻¹)⁻¹ = Real.goldenRatio ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [inv_goldenRatio_eq]
  have h := Real.goldenRatio_sq
  linear_combination (1 - Real.goldenRatio) * h

/-- [proved-derived; formal-checked] **The golden word is Wythoff's partition.** At rate `φ⁻¹` from
phase `0` the ones sit at `⌈k φ⌉ − 1` and the zeros at `⌊k φ²⌋`: the lower and upper Wythoff
sequences. -/
theorem carry_golden_iff (n : ℤ) :
    (carry Real.goldenRatio⁻¹ 0 n = 1 ↔ ∃ k : ℤ, beattySeq' Real.goldenRatio k = n) ∧
      (carry Real.goldenRatio⁻¹ 0 n = 0 ↔ ∃ k : ℤ, beattySeq (Real.goldenRatio ^ 2) k = n) := by
  have h0 : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have h1 : Real.goldenRatio⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  constructor
  · simpa using carry_eq_one_iff_beattySeq' h0 h1 n
  · rw [← inv_one_sub_inv_goldenRatio]
    exact carry_eq_zero_iff_beattySeq h0 h1 n

/-! ## Audit -/

section Audit

#print axioms helixReading_eq
#print axioms helixReading_add
#print axioms helixReading_succ
#print axioms carry_eq_windings_add_carry
#print axioms carry_mem
#print axioms carry_eq_jointCarry
#print axioms carry_mem_zero_one
#print axioms sum_carry
#print axioms sum_carry_eq_windings
#print axioms windings_advance_mem
#print axioms carry_balanced
#print axioms windings_add_of_isCycle
#print axioms carry_add_period_of_isCycle
#print axioms sum_carry_of_isCycle
#print axioms isCycle_of_eventually_periodic
#print axioms eventually_periodic_iff_isCycle
#print axioms carry_periodic_of_rational
#print axioms sum_carry_period_of_rational
#print axioms eventually_periodic_rational_iff
#print axioms not_eventually_periodic_of_irrational
#print axioms never_locks_iff_irrational
#print axioms period_ge_mediant_of_between
#print axioms period_ge_convergent_mediant
#print axioms carry_eq_one_iff_arrival
#print axioms succ_mem_carrySection_iff
#print axioms epochOf_carrySection
#print axioms epochOf_carrySection_eq_windings
#print axioms card_carrySection
#print axioms carrySection_epochs_attained
#print axioms windings_helixReading_inv
#print axioms carrySection_inv_eq_digitTicks
#print axioms odometer_counts_carrySection_epochs
#print axioms carry_rational_eq_phaseCarry
#print axioms carry_rational_eq_phaseCarry_of_lt
#print axioms mem_tube_iff
#print axioms existsUnique_mem_tube
#print axioms internal_mem_window_iff
#print axioms physicalProjection_injective
#print axioms physicalSite_succ_sub
#print axioms inv_goldenRatio_eq
#print axioms fib_succ_mul_inv_goldenRatio
#print axioms goldenRatio_inv_pow_mem
#print axioms windings_fib_succ_mul_inv_goldenRatio_of_even
#print axioms windings_fib_succ_mul_inv_goldenRatio_of_odd
#print axioms sum_carry_golden
#print axioms sum_carry_golden_of_even
#print axioms sum_carry_golden_of_odd
#print axioms sum_carry_golden_crystal
#print axioms carry_eq_one_iff_beattySeq'
#print axioms carry_eq_zero_iff_beattySeq
#print axioms inv_one_sub_inv_goldenRatio
#print axioms carry_golden_iff

end Audit

end Holonics.Aeon.Clock.CarryWord
