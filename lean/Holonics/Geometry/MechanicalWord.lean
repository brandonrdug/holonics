import Mathlib.NumberTheory.Rayleigh
import Holonics.Geometry.PhaseCarry
import Holonics.Geometry.PairResonance
import Holonics.Geometry.Turn

/-!
# The carry word of a helix: crystals lock, quasicrystals never close

[definition] A helix of real rate `α` and phase `ρ` is read against the integer section clock.
At the tick `n` it has crossed `⌊n α + ρ⌋` integer sections (its **winding**), and between the
ticks `n` and `n + 1` it crosses

`s_n = ⌊(n + 1) α + ρ⌋ − ⌊n α + ρ⌋`

sections: the **carry** of the tick. The word `(s_n)` is the classical mechanical word of slope
`α` and intercept `ρ`. This module owns it.

* **Helix = circle + carry.** The carries count the winding (`sum_carry`, a telescoping), and each
  carry is `⌊α⌋` or `⌊α⌋ + 1` (`carry_mem`); for `0 ≤ α < 1` it is a single turn or none, as for
  the integer odometer.
* **Pair = torus with a modular address.** The integer clock and the rate-`α` helix meet on a
  torus. A rational rate `p / q` is a lock: the word is periodic with period `q`
  (`carry_periodic_of_rational`), carries exactly `p` over one period, and restricted to rational
  phase it is the integer odometer's carry `PhaseCarry.carry` shifted by `⌊p / q⌋`
  (`carry_rational_eq_phaseCarry`). Conversely an eventually periodic word forces a rational rate
  (`rational_of_eventually_periodic`); an irrational rate never locks and its address never
  closes (`not_eventually_periodic_of_irrational`): a one-dimensional quasicrystal. A lock strictly
  between two neighbouring locks recurs no sooner than their mediant's period
  (`period_ge_mediant_of_between`, joined to `PairResonance`).
* **Faces and placement; the tube.** The lattice points `(n, m) ∈ ℤ²` inside the strip
  `n α + ρ − 1 < m ≤ n α + ρ` are exactly the graph `m = ⌊n α + ρ⌋` (`mem_tube_iff`); in the
  internal coordinate `n α − m` the strip is the window `[−ρ, 1 − ρ)` (`internal_mem_window_iff`).
  The strip alone projects onto all of `ℤ`; the quasicrystal needs the physical projection
  `n + β m`, whose consecutive selected sites are spaced `1 + β s_n`, two lengths ordered by the
  carry word (`physicalSite_succ_sub`). The lattice supplies the pathways and the window face
  selects them; which receiver hears the result (the regular-model-set diffraction of Hof 1995)
  is not proved here.
* **Balance.** Any two factors of equal length carry counts differing by at most one
  (`carry_balanced`).
* **The golden approximants** (joined to `Turn` §6). At rate `φ⁻¹` from phase `0`, the first
  `F_(n+1)` ticks carry `⌊F_(n+1) φ⁻¹⌋`, which is `F_n` for even `n` and `F_n − 1` for odd `n`;
  the crystal of rate `F_n / F_(n+1)` carries exactly `F_n` over the same span, and the phase
  error `F_(n+1) φ⁻¹ − F_n` is `Turn.goldenClockResidue (n + 1)`, which alternates in orientation.
  The Fibonacci fixed word of `0 ↦ 01, 1 ↦ 0` is the word of rate `φ⁻²` at intercept `φ⁻²`; the
  rate `φ⁻¹` from phase `0` used here is its complementary coding up to intercept and shift, so a
  statement about the Fibonacci word names its intercept.
* **Beatty positions** (joined to Mathlib `NumberTheory/Rayleigh`). For `0 < α < 1` and phase `0`
  the ones of the word sit at `⌈k / α⌉ − 1` and the zeros at `⌊k / (1 − α)⌋`; Rayleigh's
  complement theorem is the statement that the word is a partition of the ticks. At the golden
  rate these are the Wythoff pair `φ`, `φ²`.

The computational object is the helical pair interaction: two clocks (the integer section clock
and the rate-`α` helix) meeting on a torus. Of the six objects of the winding guide this module
touches the helix (circle + carry), the pair (torus with a modular address; a rational rate is a
lock), faces and placement (the window face) and the tube (the strip). Cell holonomy and the tower
thread stay attached and are not used here.

[open] Owed, not proved here: the three-distance theorem (Sós,
Świerczkowski, Surányi 1958: the points `{k α}`, `k < N`, cut the circle into gaps of at most three
lengths) and Sturmian factor complexity `n + 1` (Morse–Hedlund 1940). No `axiom`, no `sorry`, no
`native_decide`.
-/

namespace Holonics.Geometry.MechanicalWord

open scoped BigOperators

/-! ## 1. The winding and the carry of a helix at a real rate -/

/-- [definition] The winding of the helix of rate `α` and phase `ρ` at the tick `n`: the number of
integer sections it has crossed, `⌊n α + ρ⌋`. -/
noncomputable def winding (α ρ : ℝ) (n : ℤ) : ℤ := ⌊(n : ℝ) * α + ρ⌋

/-- [definition] The carry of the tick `n`: the integer sections crossed between the ticks `n`
and `n + 1`. The word `n ↦ carry α ρ n` is the mechanical word of slope `α` and intercept `ρ`. -/
noncomputable def carry (α ρ : ℝ) (n : ℤ) : ℤ := ⌊((n : ℝ) + 1) * α + ρ⌋ - ⌊(n : ℝ) * α + ρ⌋

/-- [proved-derived; formal-checked] The carry of a tick is the advance of the winding across it.
-/
theorem carry_eq_winding_sub (α ρ : ℝ) (n : ℤ) :
    carry α ρ n = winding α ρ (n + 1) - winding α ρ n := by
  unfold carry winding
  push_cast
  rfl

/-- [proved-standard; formal-checked] Adding `y` advances the floor of any `x` by `⌊y⌋` or by
`⌊y⌋ + 1`: the floor cocycle of `0 → ℤ → ℝ → S¹ → 0` takes the values `0` and `1`. -/
theorem floor_add_sub_floor_mem (x y : ℝ) :
    ⌊x + y⌋ - ⌊x⌋ = ⌊y⌋ ∨ ⌊x + y⌋ - ⌊x⌋ = ⌊y⌋ + 1 := by
  have h1 := Int.le_floor_add x y
  have h2 := Int.le_floor_add_floor x y
  omega

/-- [proved-derived; formal-checked] **Every carry is `⌊α⌋` or `⌊α⌋ + 1`.** The helix crosses the
whole turns of its rate, and the phase adds at most one more crossing. -/
theorem carry_mem (α ρ : ℝ) (n : ℤ) :
    carry α ρ n = ⌊α⌋ ∨ carry α ρ n = ⌊α⌋ + 1 := by
  unfold carry
  have h : ((n : ℝ) + 1) * α + ρ = ((n : ℝ) * α + ρ) + α := by ring
  rw [h]
  exact floor_add_sub_floor_mem _ _

/-- [proved-derived; formal-checked] Below one turn per tick the carry is a single turn or none:
the word is binary, as the integer odometer's carry is (`PhaseCarry.carry_le_one`). -/
theorem carry_mem_zero_one (α ρ : ℝ) (n : ℤ) (h0 : 0 ≤ α) (h1 : α < 1) :
    carry α ρ n = 0 ∨ carry α ρ n = 1 := by
  have hα : ⌊α⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  simpa [hα] using carry_mem α ρ n

/-! ## 2. The carries count the winding -/

/-- [proved-derived; formal-checked] **The carries of `k` consecutive ticks sum to the winding
advanced across them.** Helix = circle + carry: the winding is the sum of the carries. -/
theorem sum_carry_eq_winding_sub (α ρ : ℝ) (n : ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range k, carry α ρ (n + i) = winding α ρ (n + k) - winding α ρ n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, carry_eq_winding_sub]
    have h : n + ((k + 1 : ℕ) : ℤ) = n + k + 1 := by push_cast; ring
    rw [h]
    ring

/-- [proved-derived; formal-checked] **The carry sum telescopes**:
`Σ_{i<k} s_(n+i) = ⌊(n + k) α + ρ⌋ − ⌊n α + ρ⌋`. -/
theorem sum_carry (α ρ : ℝ) (n : ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range k, carry α ρ (n + i) =
      ⌊((n : ℝ) + k) * α + ρ⌋ - ⌊(n : ℝ) * α + ρ⌋ := by
  rw [sum_carry_eq_winding_sub]
  unfold winding
  push_cast
  rfl

/-! ## 3. Balance -/

/-- [proved-derived; formal-checked] Over `k` ticks the winding advances by `⌊k α⌋` or
`⌊k α⌋ + 1`, whatever the starting tick. -/
theorem winding_add_sub_mem (α ρ : ℝ) (n : ℤ) (k : ℕ) :
    winding α ρ (n + k) - winding α ρ n = ⌊(k : ℝ) * α⌋ ∨
      winding α ρ (n + k) - winding α ρ n = ⌊(k : ℝ) * α⌋ + 1 := by
  unfold winding
  have h : ((n + k : ℤ) : ℝ) * α + ρ = ((n : ℝ) * α + ρ) + (k : ℝ) * α := by push_cast; ring
  rw [h]
  exact floor_add_sub_floor_mem _ _

/-- [proved-derived; formal-checked] **The carry word is balanced.** Two factors of the same
length carry counts that differ by at most one. The helix spreads its crossings as evenly as the
integer sections allow. -/
theorem carry_balanced (α ρ : ℝ) (n m : ℤ) (k : ℕ) :
    |∑ i ∈ Finset.range k, carry α ρ (n + i) - ∑ i ∈ Finset.range k, carry α ρ (m + i)| ≤ 1 := by
  rw [sum_carry_eq_winding_sub, sum_carry_eq_winding_sub, abs_le]
  rcases winding_add_sub_mem α ρ n k with h | h <;>
    rcases winding_add_sub_mem α ρ m k with h' | h' <;>
    constructor <;> omega

/-! ## 4. A rational rate locks: the crystal -/

/-- [proved-derived; formal-checked] When `q` ticks carry the helix through exactly `c` whole
turns, the winding after `q` more ticks has advanced by exactly `c`. -/
theorem winding_add_period {α ρ : ℝ} {q c : ℤ} (h : (q : ℝ) * α = c) (n : ℤ) :
    winding α ρ (n + q) = winding α ρ n + c := by
  unfold winding
  have e : ((n + q : ℤ) : ℝ) * α + ρ = ((n : ℝ) * α + ρ) + (c : ℝ) := by
    push_cast
    rw [← h]
    ring
  rw [e, Int.floor_add_intCast]

/-- [proved-derived; formal-checked] **A commensurate period is a period of the word.** -/
theorem carry_add_period {α ρ : ℝ} {q c : ℤ} (h : (q : ℝ) * α = c) (n : ℤ) :
    carry α ρ (n + q) = carry α ρ n := by
  rw [carry_eq_winding_sub, carry_eq_winding_sub, show n + q + 1 = (n + 1) + q by ring,
    winding_add_period h, winding_add_period h]
  ring

/-- [proved-derived; formal-checked] **A rational rate is a lock.** At rate `p / q` the carry word
repeats with period `q`, whatever the phase: the crystal. -/
theorem carry_periodic_of_rational {α ρ : ℝ} {p : ℤ} {q : ℕ} (hq : 0 < q)
    (hα : α = (p : ℝ) / q) (n : ℤ) :
    carry α ρ (n + q) = carry α ρ n := by
  have hq' : (q : ℝ) ≠ 0 := by positivity
  refine carry_add_period (c := p) ?_ n
  rw [hα, Int.cast_natCast]
  field_simp

/-- [proved-derived; formal-checked] Over one period of the lock `p / q` the word carries exactly
`p`: the crystal's winding per period is its numerator. -/
theorem sum_carry_period_of_rational {α ρ : ℝ} {p : ℤ} {q : ℕ} (hq : 0 < q)
    (hα : α = (p : ℝ) / q) (n : ℤ) :
    ∑ i ∈ Finset.range q, carry α ρ (n + i) = p := by
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have h : ((q : ℤ) : ℝ) * α = p := by
    rw [hα, Int.cast_natCast]
    field_simp
  rw [sum_carry_eq_winding_sub, winding_add_period h]
  ring

/-- [proved-derived; formal-checked] **The real helix at a rational rate is the integer
odometer.** At rate `p / q` and phase `r / q` the carry of the tick `n` is the whole turns
`⌊p / q⌋` of the rate plus the odometer carry `PhaseCarry.carry q (n p + r) p` of adding the rate's
phase `p` to the helix's lattice position `n p + r` on the circle of `q` steps. The argument order
follows `PhaseCarry.carry n a b = (a % n + b % n) / n`: the circle, the position, the step. -/
theorem carry_rational_eq_phaseCarry (p q r n : ℕ) (hq : 0 < q) :
    carry ((p : ℝ) / q) ((r : ℝ) / q) n =
      ((p / q : ℕ) : ℤ) + (PhaseCarry.carry q (n * p + r) p : ℤ) := by
  unfold carry
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have e1 : (((n : ℤ) : ℝ) + 1) * ((p : ℝ) / q) + (r : ℝ) / q =
      ((n * p + r + p : ℕ) : ℝ) / (q : ℕ) := by
    push_cast
    field_simp
    ring
  have e2 : ((n : ℤ) : ℝ) * ((p : ℝ) / q) + (r : ℝ) / q = ((n * p + r : ℕ) : ℝ) / (q : ℕ) := by
    push_cast
    field_simp
  rw [e1, e2, Int.floor_div_natCast, Int.floor_div_natCast, Int.floor_natCast,
    Int.floor_natCast]
  have h := PhaseCarry.winding_add q (n * p + r) p hq
  simp only [PhaseCarry.winding] at h
  have h' : (((n * p + r + p) / q : ℕ) : ℤ) =
      (((n * p + r) / q : ℕ) : ℤ) + ((p / q : ℕ) : ℤ) +
        (PhaseCarry.carry q (n * p + r) p : ℤ) := by
    exact_mod_cast h
  push_cast at h'
  omega

/-- [proved-derived; formal-checked] Below one turn per tick (`p < q`) the real carry at a
rational rate is exactly the integer odometer's carry. -/
theorem carry_rational_eq_phaseCarry_of_lt (p q r n : ℕ) (hpq : p < q) :
    carry ((p : ℝ) / q) ((r : ℝ) / q) n = (PhaseCarry.carry q (n * p + r) p : ℤ) := by
  rw [carry_rational_eq_phaseCarry p q r n (by omega), Nat.div_eq_of_lt hpq]
  simp

/-! ## 5. An irrational rate never locks: the quasicrystal -/

/-- [proved-derived; formal-checked] **A lock forces a rational rate.** If the carry word repeats
with period `T` from some tick on, then `T` ticks carry the helix through a whole number of turns:
`T α ∈ ℤ`. The winding over each period is constant, so the phase error over `j` periods is
bounded by one crossing for every `j`, which only a zero error allows. -/
theorem rational_of_eventually_periodic {α ρ : ℝ} {T : ℕ} {N : ℤ}
    (hper : ∀ n ≥ N, carry α ρ (n + T) = carry α ρ n) :
    ∃ c : ℤ, (T : ℝ) * α = c := by
  -- The winding advanced over one period, read from the tick `n`.
  have hstep : ∀ n ≥ N, winding α ρ (n + 1 + T) - winding α ρ (n + 1) =
      winding α ρ (n + T) - winding α ρ n := by
    intro n hn
    have h := hper n hn
    rw [carry_eq_winding_sub, carry_eq_winding_sub] at h
    rw [show n + 1 + (T : ℤ) = n + T + 1 by ring]
    omega
  have hconst : ∀ j : ℕ, winding α ρ (N + j + T) - winding α ρ (N + j) =
      winding α ρ (N + T) - winding α ρ N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : N + ((j + 1 : ℕ) : ℤ) = N + j + 1 := by push_cast; ring
      rw [e, hstep _ (by omega), ih]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = winding α ρ (N + T) - winding α ρ N := ⟨_, rfl⟩
  have hlin : ∀ j : ℕ, winding α ρ (N + j * T) = winding α ρ N + j * c := by
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
  -- The phase error over `j` periods is less than one crossing.
  have hbound : ∀ j : ℕ, |(j : ℝ) * ((T : ℝ) * α - c)| < 1 := by
    intro j
    have hw : ⌊(N : ℝ) * α + ρ + j * (T * α)⌋ = ⌊(N : ℝ) * α + ρ⌋ + j * c := by
      have h := hlin j
      unfold winding at h
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

/-- [proved-derived; formal-checked] **An irrational rate never locks.** Its carry word is not
periodic from any tick on: the address never closes, and the helix is a one-dimensional
quasicrystal rather than a crystal. -/
theorem not_eventually_periodic_of_irrational {α : ℝ} (hα : Irrational α) (ρ : ℝ) {T : ℕ}
    (hT : 0 < T) (N : ℤ) :
    ¬ ∀ n ≥ N, carry α ρ (n + T) = carry α ρ n := by
  intro hper
  obtain ⟨c, hc⟩ := rational_of_eventually_periodic hper
  exact (hα.natCast_mul (Nat.pos_iff_ne_zero.mp hT)).ne_int c hc

/-- [proved-derived; formal-checked] **Lock ⇔ commensurate rate.** The carry word is eventually
periodic exactly when some positive number of ticks carries the helix through a whole number of
turns. -/
theorem eventually_periodic_iff (α ρ : ℝ) :
    (∃ T : ℕ, 0 < T ∧ ∃ N : ℤ, ∀ n ≥ N, carry α ρ (n + T) = carry α ρ n) ↔
      ∃ T : ℕ, 0 < T ∧ ∃ c : ℤ, (T : ℝ) * α = c := by
  constructor
  · rintro ⟨T, hT, N, hper⟩
    exact ⟨T, hT, rational_of_eventually_periodic hper⟩
  · rintro ⟨T, hT, c, hc⟩
    refine ⟨T, hT, 0, fun n _ => carry_add_period (q := (T : ℤ)) (c := c) ?_ n⟩
    rw [Int.cast_natCast]
    exact hc

/-- [proved-derived; formal-checked] **A lock strictly between two neighbouring locks recurs no
sooner than their mediant.** If the word locks with period `T` and its rate lies strictly between
the neighbouring locks `p / q` and `p' / q'` (`p' q − p q' = 1`), then `T ≥ q + q'`: the mediant is
the cheapest crystal in the gap (`PairResonance.between_neighbours_costs_at_least_the_mediant`). -/
theorem period_ge_mediant_of_between {α ρ : ℝ} {T : ℕ} {N : ℤ}
    (hper : ∀ n ≥ N, carry α ρ (n + T) = carry α ρ n) (hT : 0 < T)
    {p q p' q' : ℤ} (hq : 0 < q) (hq' : 0 < q') (hadj : p' * q - p * q' = 1)
    (hleft : (p : ℝ) / q < α) (hright : α < (p' : ℝ) / q') :
    q + q' ≤ T := by
  obtain ⟨c, hc⟩ := rational_of_eventually_periodic hper
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'r : (0 : ℝ) < q' := by exact_mod_cast hq'
  rw [div_lt_iff₀ hqr] at hleft
  rw [lt_div_iff₀ hq'r] at hright
  have h1 : (p : ℝ) * T < c * q := by
    have a := mul_lt_mul_of_pos_right hleft hTr
    have b : α * q * T = c * q := by rw [← hc]; ring
    linarith
  have h2 : (c : ℝ) * q' < p' * T := by
    have a := mul_lt_mul_of_pos_right hright hTr
    have b : α * q' * T = c * q' := by rw [← hc]; ring
    linarith
  have h1' : p * (T : ℤ) < c * q := by exact_mod_cast h1
  have h2' : c * q' < p' * (T : ℤ) := by exact_mod_cast h2
  exact PairResonance.between_neighbours_costs_at_least_the_mediant p q p' q' c T hq hq' hadj
    h1' h2'

/-! ## 6. Cut and project: the window face selects the pathways -/

/-- [proved-derived; formal-checked] **The lattice points in the tube are the carry's graph.** A
lattice point `(n, m)` lies in the strip `n α + ρ − 1 < m ≤ n α + ρ` exactly when `m` is the
winding `⌊n α + ρ⌋`. The lattice gives the pathways; the window face `(−1, 0]` selects them. -/
theorem mem_tube_iff (n : ℤ) (α ρ : ℝ) (m : ℤ) :
    ((n : ℝ) * α + ρ - 1 < m ∧ (m : ℝ) ≤ (n : ℝ) * α + ρ) ↔ m = winding α ρ n := by
  unfold winding
  rw [eq_comm, Int.floor_eq_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- [proved-derived; formal-checked] Each tick selects exactly one lattice point of the tube: the
window face has unit height, so the projected pathway is a graph. -/
theorem existsUnique_mem_tube (n : ℤ) (α ρ : ℝ) :
    ∃! m : ℤ, (n : ℝ) * α + ρ - 1 < m ∧ (m : ℝ) ≤ (n : ℝ) * α + ρ :=
  ⟨winding α ρ n, (mem_tube_iff n α ρ _).mpr rfl, fun m hm => (mem_tube_iff n α ρ m).mp hm⟩

/-- [proved-derived; formal-checked] **The strip is a window in the internal coordinate.** The
selected lattice point satisfies `n α − m ∈ [−ρ, 1 − ρ)`. -/
theorem internal_mem_window_iff (n : ℤ) (α ρ : ℝ) (m : ℤ) :
    (-ρ ≤ (n : ℝ) * α - m ∧ (n : ℝ) * α - m < 1 - ρ) ↔ m = winding α ρ n := by
  rw [← mem_tube_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- [definition] **The physical projection** of the selected lattice point at tick `n`:
`n + β ⌊n α + ρ⌋`. With `β` irrational the projection `(n, m) ↦ n + β m` is injective on `ℤ²`
(`physicalProjection_injective`). -/
noncomputable def physicalSite (β α ρ : ℝ) (n : ℤ) : ℝ := n + β * winding α ρ n

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
Consecutive sites differ by `1 + β s_n`: the lattice pathways chosen by the window face, read in
the physical line, form a point set with two spacings (`1` and `1 + β` when `0 ≤ α < 1`) in the
order of the mechanical word. -/
theorem physicalSite_succ_sub (β α ρ : ℝ) (n : ℤ) :
    physicalSite β α ρ (n + 1) - physicalSite β α ρ n = 1 + β * carry α ρ n := by
  unfold physicalSite
  rw [carry_eq_winding_sub]
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
      Nat.fib n + Turn.goldenClockResidue (n + 1) := by
  unfold Turn.goldenClockResidue
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

/-- [proved-derived; formal-checked] For even `n` the golden residue at `n + 1` is positive, so
`⌊F_(n+1) φ⁻¹⌋ = F_n`: the quasicrystal keeps pace with the crystal. -/
theorem floor_fib_succ_mul_inv_goldenRatio_of_even {n : ℕ} (hn : Even n) :
    ⌊(Nat.fib (n + 1) : ℝ) * Real.goldenRatio⁻¹⌋ = Nat.fib n := by
  rw [fib_succ_mul_inv_goldenRatio, Turn.goldenClock_oriented_residue, Int.floor_eq_iff]
  have hs : Even (n + 1 + 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k + 1, by omega⟩
  rw [hs.neg_one_pow]
  obtain ⟨h0, h1⟩ := goldenRatio_inv_pow_mem n
  push_cast
  constructor <;> linarith

/-- [proved-derived; formal-checked] For odd `n` the golden residue at `n + 1` is negative, so
`⌊F_(n+1) φ⁻¹⌋ = F_n − 1`: the quasicrystal lags the crystal by one crossing. -/
theorem floor_fib_succ_mul_inv_goldenRatio_of_odd {n : ℕ} (hn : Odd n) :
    ⌊(Nat.fib (n + 1) : ℝ) * Real.goldenRatio⁻¹⌋ = (Nat.fib n : ℤ) - 1 := by
  rw [fib_succ_mul_inv_goldenRatio, Turn.goldenClock_oriented_residue, Int.floor_eq_iff]
  have hs : Odd (n + 1 + 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k + 1, by omega⟩
  rw [hs.neg_one_pow]
  obtain ⟨h0, h1⟩ := goldenRatio_inv_pow_mem n
  push_cast
  constructor <;> linarith

/-- [proved-derived; formal-checked] The first `F_(n+1)` ticks of the golden helix from phase `0`
carry `⌊F_(n+1) φ⁻¹⌋`. -/
theorem sum_carry_golden (n : ℕ) :
    ∑ i ∈ Finset.range (Nat.fib (n + 1)), carry Real.goldenRatio⁻¹ 0 i =
      ⌊(Nat.fib (n + 1) : ℝ) * Real.goldenRatio⁻¹⌋ := by
  simpa using sum_carry Real.goldenRatio⁻¹ 0 0 (Nat.fib (n + 1))

/-- [proved-derived; formal-checked] **The golden quasicrystal at an even approximant.** Over the
first `F_(n+1)` ticks the golden word carries `F_n`, as its crystal approximant does. -/
theorem sum_carry_golden_of_even {n : ℕ} (hn : Even n) :
    ∑ i ∈ Finset.range (Nat.fib (n + 1)), carry Real.goldenRatio⁻¹ 0 i = Nat.fib n := by
  rw [sum_carry_golden, floor_fib_succ_mul_inv_goldenRatio_of_even hn]

/-- [proved-derived; formal-checked] **The golden quasicrystal at an odd approximant.** Over the
first `F_(n+1)` ticks the golden word carries `F_n − 1`, one crossing short of its crystal
approximant: the residue's orientation alternates with the parity. -/
theorem sum_carry_golden_of_odd {n : ℕ} (hn : Odd n) :
    ∑ i ∈ Finset.range (Nat.fib (n + 1)), carry Real.goldenRatio⁻¹ 0 i =
      (Nat.fib n : ℤ) - 1 := by
  rw [sum_carry_golden, floor_fib_succ_mul_inv_goldenRatio_of_odd hn]

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
`0 < α < 1` and phase `0`, the tick `n` carries a crossing exactly when `n = ⌈k / α⌉ − 1` for some
integer `k`: the `k`-th section is crossed during the tick `n`. -/
theorem carry_eq_one_iff_beattySeq' {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (n : ℤ) :
    carry α 0 n = 1 ↔ ∃ k : ℤ, beattySeq' α⁻¹ k = n := by
  constructor
  · intro h
    refine ⟨⌊((n : ℝ) + 1) * α⌋, ?_⟩
    unfold carry at h
    simp only [add_zero] at h
    have hk1 : ((⌊((n : ℝ) + 1) * α⌋ : ℤ) : ℝ) ≤ ((n : ℝ) + 1) * α := Int.floor_le _
    have hk2 : (n : ℝ) * α < ((⌊((n : ℝ) + 1) * α⌋ : ℤ) : ℝ) := by
      have e : ⌊(n : ℝ) * α⌋ < ⌊((n : ℝ) + 1) * α⌋ := by omega
      exact Int.floor_lt.mp e
    unfold beattySeq'
    rw [sub_eq_iff_eq_add, Int.ceil_eq_iff, ← div_eq_mul_inv]
    push_cast
    constructor
    · rw [lt_div_iff₀ h0]
      linarith
    · rw [div_le_iff₀ h0]
      linarith
  · rintro ⟨k, hk⟩
    unfold beattySeq' at hk
    have hc : ⌈(k : ℝ) * α⁻¹⌉ = n + 1 := by omega
    rw [Int.ceil_eq_iff, ← div_eq_mul_inv] at hc
    push_cast at hc
    obtain ⟨hc1, hc2⟩ := hc
    rw [lt_div_iff₀ h0] at hc1
    rw [div_le_iff₀ h0] at hc2
    have a1 : k ≤ ⌊((n : ℝ) + 1) * α⌋ := Int.le_floor.mpr hc2
    have a2 : ⌊(n : ℝ) * α⌋ < k := Int.floor_lt.mpr (by linarith)
    rcases carry_mem_zero_one α 0 n h0.le h1 with h | h
    · unfold carry at h
      simp only [add_zero] at h
      omega
    · exact h

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
  rcases carry_mem_zero_one α 0 n h0.le h1 with h | h <;> simp [h]

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

#print axioms carry_eq_winding_sub
#print axioms floor_add_sub_floor_mem
#print axioms carry_mem
#print axioms carry_mem_zero_one
#print axioms sum_carry_eq_winding_sub
#print axioms sum_carry
#print axioms winding_add_sub_mem
#print axioms carry_balanced
#print axioms winding_add_period
#print axioms carry_add_period
#print axioms carry_periodic_of_rational
#print axioms sum_carry_period_of_rational
#print axioms carry_rational_eq_phaseCarry
#print axioms carry_rational_eq_phaseCarry_of_lt
#print axioms rational_of_eventually_periodic
#print axioms not_eventually_periodic_of_irrational
#print axioms eventually_periodic_iff
#print axioms period_ge_mediant_of_between
#print axioms mem_tube_iff
#print axioms existsUnique_mem_tube
#print axioms internal_mem_window_iff
#print axioms physicalSite_succ_sub
#print axioms physicalProjection_injective
#print axioms inv_goldenRatio_eq
#print axioms fib_succ_mul_inv_goldenRatio
#print axioms goldenRatio_inv_pow_mem
#print axioms floor_fib_succ_mul_inv_goldenRatio_of_even
#print axioms floor_fib_succ_mul_inv_goldenRatio_of_odd
#print axioms sum_carry_golden
#print axioms sum_carry_golden_of_even
#print axioms sum_carry_golden_of_odd
#print axioms sum_carry_golden_crystal
#print axioms carry_eq_one_iff_beattySeq'
#print axioms carry_eq_zero_iff_beattySeq
#print axioms inv_one_sub_inv_goldenRatio
#print axioms carry_golden_iff

end Audit

end Holonics.Geometry.MechanicalWord
