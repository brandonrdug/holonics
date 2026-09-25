import Holonics.Aeon.Clock.Reading
import Holonics.Geometry.PhaseCarry
import Holonics.Objects.Parametron
import Holonics.Holon.Generator

/-!
# Windings and open phase: the lift of the clock torus, the quotient and the remainder

[definition] `docs/ELEMENTARY_OBJECTS.md` §9 and §12, the aeon record's
`t_R(γ) = ⟨ω_R | γ⟩ = n_R + r_R`. The navigators' joint phase lives on a torus; its lift
`clockLift ι` is the lattice `ℤ^ι` of micro-step potentials of the navigators `ι`, whose edges
advance one navigator by one micro-step and whose two-cells are the unit squares where two
navigators commute. An aeon of
the lift is a 1-chain of the joint motion that retains its winding; its projection to the torus
forgets it. A reading `t` splits into **whole windings** `windings t = ⌊t⌋` (the quotient, the
carry) and **open phase** `openPhase t = t − ⌊t⌋ ∈ [0, 1)` (the remainder).

[proved-derived; formal-checked] What is proved.

1. **The lift.** `clockLift` is well formed (`clockLift_wellFormed`: two navigators commute
   around every square); a navigator's micro-step clock is exact on the lift and reads the lift
   displacement (`reading_navigatorClock`). An aeon projects to a closed loop on the torus exactly
   when every navigator's reading is a whole multiple of its period (`torus_closes_iff`), and then
   the reading in turns is whole windings with zero open phase (`torus_cycle_reads_whole_windings`).
   The lift retains what the torus forgets (`lift_retains_winding`: three steps of a
   three-step ring and rest close at one torus point with readings `1` and `0` turns).
2. **Quotient and remainder.** `t = windings t + openPhase t` with `0 ≤ openPhase t < 1`, and the
   split is unique (`reading_split`, `split_unique`); a reading is a cycle reading exactly when
   its open phase is zero (`openPhase_eq_zero_iff`).
3. **The carry.** `windings (s + t) = windings s + windings t + carry s t` with `carry ∈ {0, 1}`,
   and the carry is a cocycle (`windings_add`, `carry_nonneg`, `carry_le_one`, `carry_cocycle`,
   `openPhase_add`). Along aeons: `aeon_windings_concat`.
4. **The split is the ratio's division with remainder.** For a reading presented as the ratio
   `m / d` (`m` micro-steps of a `d`-step ring), `windings = m / d` and `d · openPhase = m % d`
   (`ratio_split`); in the natural chart these are `PhaseCarry.winding` and `PhaseCarry.phase`
   (`windings_of_microsteps`, `openPhase_of_microsteps`), the reading's carry is the Odometer's
   carry `PhaseCarry.carry` (`carry_of_microsteps`), and the split is the rational clock passage's
   quotient–residue state (`split_eq_clockPassage_normalize`).
5. **Ticks are windings plus carry.** A ring passage starting at residue `r` crosses its section
   `winding d (n k) + carry d r (n k)` times (`targetTicks_eq_windings_add_carry`), which is the
   whole windings of the reading counted from the last crossing and, for `d ≥ 2`, the owner's
   crossing count (`ownerCrossings_eq_windings`). Each whole winding is one lossless jump of the
   navigator's lifted phase (`jump_iterate`, over `Holon/Generator.LiftedPhase.jump`), and the
   phase carrier `e^{2πi t}` reads only the open phase (`carrier_reads_only_open_phase`).

[definition] The torus itself is taken as the quotient of the lift (`torusPoint`); cycles on the
torus are the aeons of the lift whose displacement lies in the period lattice. `Objects/Ratio`
owns the log fibre of a ratio, not an integer division with remainder; the guide names
`Geometry/PhaseCarry` and the clock passage for that, and they are the owners joined here.

Scope: exact integer and rational arithmetic, and a generic ordered field with floor for the
split. Continuous phase flows are outside this module. No `axiom`, no `sorry`, no `native_decide`.
-/

set_option linter.dupNamespace false

namespace Holonics.Aeon.Clock.Winding

open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading
open Holonics.Geometry
open Holonics.Geometry.HolonicClockedPantographicSwing

/-! ## 1. The lift of the navigators' joint clock torus -/

section Lift

variable {ι : Type*} [DecidableEq ι]

/-- [definition] **The lift of the joint clock torus** of the navigators `ι`: occurrences are
lattice points of micro-step potentials `ℤ^ι`; the edge `(x, i)` advances navigator `i` by one
micro-step; the two-cell `(x, i, j)` is the unit square where navigators `i` and `j` commute. -/
def clockLift (ι : Type*) [DecidableEq ι] :
    ParametricComplex (ι → ℤ) ((ι → ℤ) × ι) ((ι → ℤ) × ι × ι) where
  src e := e.1
  tgt e := e.1 + Pi.single e.2 1
  base f := f.1
  boundary f :=
    [((f.1, f.2.1), true), ((f.1 + Pi.single f.2.1 1, f.2.2), true),
      ((f.1 + Pi.single f.2.2 1, f.2.1), false), ((f.1, f.2.2), false)]

/-- [proved-derived; formal-checked] Every square of the lift closes: two navigators commute. -/
theorem clockLift_wellFormed : (clockLift ι).WellFormed := by
  rintro ⟨x, i, j⟩
  simp [clockLift, ParametricComplex.start, ParametricComplex.finish, add_right_comm]

/-- [definition] Navigator `i`'s micro-step clock: the exact form of its lift coordinate. -/
def navigatorClock (i : ι) : Clock (clockLift ι) ℤ :=
  exactClock clockLift_wellFormed (fun x => x i)

/-- [proved-derived; formal-checked] **A navigator's clock reads the lift displacement** of its
coordinate, whatever route the aeon takes. -/
theorem reading_navigatorClock (i : ι) {x y : ι → ℤ} (γ : Aeon (clockLift ι) x y) :
    reading (navigatorClock i) γ = y i - x i :=
  reading_exactClock clockLift_wellFormed _ γ

/-- [definition] The torus point of a lift point, for navigator periods `d`. -/
def torusPoint (d : ι → ℕ) (x : ι → ℤ) : (i : ι) → ZMod (d i) := fun i => (x i : ZMod (d i))

/-- [proved-derived; formal-checked] **An aeon closes on the torus exactly when every navigator's
reading is a whole number of its periods.** -/
theorem torus_closes_iff (d : ι → ℕ) {x y : ι → ℤ} (γ : Aeon (clockLift ι) x y) :
    torusPoint d x = torusPoint d y ↔ ∀ i, (d i : ℤ) ∣ reading (navigatorClock i) γ := by
  constructor
  · intro h i
    rw [reading_navigatorClock]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun h i)
  · intro h
    funext i
    have := h i
    rw [reading_navigatorClock] at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr this

/-- [definition] A micro-step reading in turns of a `d`-step ring. -/
def turns (d : ℕ) (m : ℤ) : ℚ := m / d

end Lift

/-! ## 2. Quotient and remainder of a reading -/

section Split

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- [definition] **Whole windings** of a reading: the quotient. -/
def windings (t : R) : ℤ := ⌊t⌋

/-- [definition] **Open phase** of a reading: the remainder. -/
def openPhase (t : R) : R := Int.fract t

/-- [definition] **The carry** of two readings: the turn completed by adding their open phases. -/
def carry (s t : R) : ℤ := ⌊Int.fract s + Int.fract t⌋

/-- [proved-derived; formal-checked] **A reading is its whole windings plus its open phase**, with
the open phase inside one turn. -/
theorem reading_split (t : R) :
    (windings t : R) + openPhase t = t ∧ 0 ≤ openPhase t ∧ openPhase t < 1 :=
  ⟨Int.floor_add_fract t, Int.fract_nonneg t, Int.fract_lt_one t⟩

/-- [proved-derived; formal-checked] The split is unique. -/
theorem split_unique {t : R} (n : ℤ) (r : R) (h : (n : R) + r = t) (h0 : 0 ≤ r) (h1 : r < 1) :
    n = windings t ∧ r = openPhase t := by
  have hn : windings t = n := by
    rw [windings, Int.floor_eq_iff]
    constructor <;> linarith
  refine ⟨hn.symm, ?_⟩
  have := (reading_split t).1
  rw [hn] at this
  linarith

/-- [proved-derived; formal-checked] A reading has zero open phase exactly when it is a whole number
of turns: the reading of a cycle by an integral clock. -/
theorem openPhase_eq_zero_iff (t : R) : openPhase t = 0 ↔ ∃ n : ℤ, t = n := by
  constructor
  · intro h
    refine ⟨windings t, ?_⟩
    have := (reading_split t).1
    rw [h, add_zero] at this
    exact this.symm
  · rintro ⟨n, rfl⟩
    simp [openPhase]

theorem carry_nonneg (s t : R) : 0 ≤ carry s t :=
  Int.floor_nonneg.mpr (add_nonneg (Int.fract_nonneg s) (Int.fract_nonneg t))

/-- [proved-derived; formal-checked] The carry is a single turn or none. -/
theorem carry_le_one (s t : R) : carry s t ≤ 1 := by
  have h : Int.fract s + Int.fract t < ((2 : ℤ) : R) := by
    have := Int.fract_lt_one s
    have := Int.fract_lt_one t
    push_cast
    linarith
  have := Int.floor_lt.mpr h
  unfold carry
  omega

/-- [proved-derived; formal-checked] **Readings add with carry.** The whole windings of a sum are
the sum of the whole windings plus the carry of the open phases. -/
theorem windings_add (s t : R) : windings (s + t) = windings s + windings t + carry s t := by
  have hs := Int.floor_add_fract s
  have ht := Int.floor_add_fract t
  have : s + t = ((⌊s⌋ + ⌊t⌋ : ℤ) : R) + (Int.fract s + Int.fract t) := by
    push_cast
    linarith
  rw [windings, this, Int.floor_intCast_add]
  rfl

/-- [proved-derived; formal-checked] The open phase of a sum drops the carried turn. -/
theorem openPhase_add (s t : R) :
    openPhase (s + t) = openPhase s + openPhase t - carry s t := by
  have h1 := (reading_split (s + t)).1
  have h2 := (reading_split s).1
  have h3 := (reading_split t).1
  rw [windings_add] at h1
  push_cast at h1
  linarith

/-- [proved-derived; formal-checked] **The carry is a cocycle.** -/
theorem carry_cocycle (a b c : R) :
    carry a b + carry (a + b) c = carry b c + carry a (b + c) := by
  have h1 := windings_add (a + b) c
  have h2 := windings_add a b
  have h3 := windings_add a (b + c)
  have h4 := windings_add b c
  rw [add_assoc] at h1
  omega

end Split

/-! ## 3. Along aeons: additivity with carry -/

section Aeons

variable {V E F : Type*} {K : ParametricComplex V E F}

/-- [proved-derived; formal-checked] **The whole windings of a concatenated aeon** are the sum of
the whole windings plus the carry of the two open phases. -/
theorem aeon_windings_concat (c : Clock K ℚ) {u w v : V} (γ : Aeon K u w) (δ : Aeon K w v) :
    windings (reading c (γ.concat δ)) =
      windings (reading c γ) + windings (reading c δ) + carry (reading c γ) (reading c δ) := by
  rw [reading_concat, windings_add]

/-- [proved-derived; formal-checked] **A torus cycle reads whole windings.** When an aeon of the
lift closes on the torus, each navigator's reading in turns has zero open phase and its whole
windings are the lift displacement divided by the period. -/
theorem torus_cycle_reads_whole_windings {ι : Type*} [DecidableEq ι] (d : ι → ℕ) {x y : ι → ℤ}
    (γ : Aeon (clockLift ι) x y) (hd : ∀ i, 0 < d i) (hclose : torusPoint d x = torusPoint d y)
    (i : ι) :
    openPhase (turns (d i) (reading (navigatorClock i) γ)) = 0 ∧
      windings (turns (d i) (reading (navigatorClock i) γ)) = (y i - x i) / (d i : ℤ) := by
  obtain ⟨n, hn⟩ := (torus_closes_iff d γ).mp hclose i
  have hdq : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
  have ht : turns (d i) (reading (navigatorClock i) γ) = ((n : ℤ) : ℚ) := by
    rw [turns, hn]
    push_cast
    field_simp
  refine ⟨(openPhase_eq_zero_iff _).mpr ⟨n, ht⟩, ?_⟩
  rw [ht, windings, Int.floor_intCast, ← reading_navigatorClock i γ, hn,
    Int.mul_ediv_cancel_left _ (by exact_mod_cast (hd i).ne')]

/-- [counterexample; formal-checked] **The lift retains what the torus forgets.** On a single
three-step ring, three forward micro-steps from `0` and rest at `0` close at the same torus
point; their readings are `1` and `0` turns. -/
theorem lift_retains_winding :
    ∃ γ : Aeon (clockLift (Fin 1)) 0 (Pi.single 0 3),
      torusPoint (ι := Fin 1) (fun _ => 3) 0 = torusPoint (ι := Fin 1) (fun _ => 3) (Pi.single 0 3) ∧
        windings (turns 3 (reading (navigatorClock (ι := Fin 1) 0) γ)) = 1 ∧
        windings (turns 3 (reading (navigatorClock (ι := Fin 1) 0)
          (Aeon.rest (0 : Fin 1 → ℤ) : Aeon (clockLift (Fin 1)) 0 0))) = 0 := by
  refine ⟨⟨[((0, 0), true), ((Pi.single 0 1, 0), true), ((Pi.single 0 2, 0), true)], ?_⟩,
    ?_, ?_, ?_⟩
  · simp only [ParametricComplex.chained_cons, ParametricComplex.chained_nil, clockLift,
      ParametricComplex.start, ParametricComplex.finish, if_true]
    refine ⟨trivial, by simp, ?_, ?_⟩
    · rw [← Pi.single_add]; norm_num
    · rw [← Pi.single_add]; norm_num
  · funext i
    fin_cases i
    simp [torusPoint]
    decide
  · rw [reading_navigatorClock]
    simp [turns, windings]
  · rw [reading_rest]
    simp [turns, windings]

end Aeons

/-! ## 4. The split is the ratio's division with remainder -/

section Ratio

/-- [proved-derived; formal-checked] **The split of a ratio reading is its division with
remainder.** For `m` micro-steps of a `d`-step ring, the whole windings are the Euclidean quotient
`m / d`, `d` times the open phase is the remainder `m % d`, and `m = d · (m / d) + m % d` with
`0 ≤ m % d < d`. -/
theorem ratio_split (m : ℤ) (d : ℕ) (hd : 0 < d) :
    windings ((m : ℚ) / d) = m / (d : ℤ) ∧
      (d : ℚ) * openPhase ((m : ℚ) / d) = ((m % (d : ℤ) : ℤ) : ℚ) ∧
      m = (d : ℤ) * (m / (d : ℤ)) + m % (d : ℤ) ∧
      0 ≤ m % (d : ℤ) ∧ m % (d : ℤ) < d := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd
  refine ⟨Rat.floor_intCast_div_natCast m d, ?_, (Int.mul_ediv_add_emod m d).symm,
    Int.emod_nonneg _ hdz.ne', Int.emod_lt_of_pos _ hdz⟩
  rw [openPhase, Int.fract_div_intCast_eq_div_intCast_mod]
  field_simp

/-- [proved-derived; formal-checked] In the natural micro-step chart the whole windings are the
Odometer's winding `PhaseCarry.winding`. -/
theorem windings_of_microsteps (n x : ℕ) :
    windings ((x : ℚ) / n) = (PhaseCarry.winding n x : ℤ) := by
  rw [windings, Rat.floor_natCast_div_natCast, PhaseCarry.winding, Int.natCast_div]

/-- [proved-derived; formal-checked] In the natural micro-step chart the open phase is the phase
`PhaseCarry.phase` in turns. -/
theorem openPhase_of_microsteps (n x : ℕ) :
    openPhase ((x : ℚ) / n) = (PhaseCarry.phase n x : ℚ) / n := by
  rw [openPhase, Int.fract_div_natCast_eq_div_natCast_mod, PhaseCarry.phase]

/-- [proved-derived; formal-checked] **Concatenation carries exactly as the Odometer carries.** The
carry of two micro-step readings is `PhaseCarry.carry`. -/
theorem carry_of_microsteps (n a b : ℕ) :
    carry ((a : ℚ) / n) ((b : ℚ) / n) = (PhaseCarry.carry n a b : ℤ) := by
  rw [carry, Int.fract_div_natCast_eq_div_natCast_mod, Int.fract_div_natCast_eq_div_natCast_mod,
    ← add_div, ← Nat.cast_add, Rat.floor_natCast_div_natCast, PhaseCarry.carry, Int.natCast_div]

/-- [proved-derived; formal-checked] **The split is the rational clock passage's quotient–residue
state.** The whole windings and open phase of `potential / d` are the completed ticks and residue
of the owner's `normalize`. -/
theorem split_eq_clockPassage_normalize {ClockAddress : Type*}
    (passage : RationalClockPassage ClockAddress) (potential : ℕ) :
    windings ((potential : ℚ) / passage.denominator) =
        ((RationalClockPassage.normalize passage potential).completedTicks : ℤ) ∧
      openPhase ((potential : ℚ) / passage.denominator) =
        ((RationalClockPassage.normalize passage potential).residue : ℚ) /
          passage.denominator := by
  refine ⟨?_, ?_⟩
  · rw [windings_of_microsteps]
    rfl
  · rw [openPhase_of_microsteps]
    rfl

end Ratio

/-! ## 5. Ticks are whole windings plus carry -/

section Ticks

variable {ClockAddress : Type*}

/-- [proved-derived; formal-checked] **A ring passage's ticks are the windings of the advance plus
the carry of the starting residue.** -/
theorem targetTicks_eq_windings_add_carry (passage : RationalClockPassage ClockAddress)
    (r k : ℕ) (hr : r < passage.denominator) :
    passage.targetTicks r k =
      PhaseCarry.winding passage.denominator (passage.numerator * k) +
        PhaseCarry.carry passage.denominator r (passage.numerator * k) := by
  have h := PhaseCarry.winding_add passage.denominator r (passage.numerator * k)
    passage.denominator_pos
  have h0 : PhaseCarry.winding passage.denominator r = 0 := Nat.div_eq_of_lt hr
  rw [h0, zero_add] at h
  exact h

/-- [proved-derived; formal-checked] **The ticks crossed are the whole windings of the reading
counted from the last crossing**, and for `d ≥ 2` they are the owner's crossing records. -/
theorem ownerCrossings_eq_windings (passage : RationalClockPassage ClockAddress)
    (hd : 2 ≤ passage.denominator) (r k : ℕ) (hr : r < passage.denominator) :
    (Holonics.Objects.Parametron.ownerCrossings passage r (passage.numerator * k) : ℤ) =
      windings (((r + passage.numerator * k : ℕ) : ℚ) / passage.denominator) := by
  rw [(Holonics.Objects.Parametron.ownerCrossings_eq_targetTicks passage hd r k hr).1,
    windings_of_microsteps]
  rfl

open Holonics.HolonCore in
/-- [proved-derived; formal-checked] **Each whole winding is one lossless jump** of the navigator's
lifted phase: `m` jumps advance the lift by `m` turns and the counted winding by `m`, leaving the
chart phase, which is all any storage reads (`jump_lossless`). -/
theorem jump_iterate (p : LiftedPhase) (m : ℕ) :
    (LiftedPhase.jump^[m] p).θ = p.θ + 2 * Real.pi * m ∧
      (LiftedPhase.jump^[m] p).n = p.n + m ∧
      (LiftedPhase.jump^[m] p).chart = p.chart := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_, ?_⟩
    · simp only [LiftedPhase.jump, h1]
      push_cast
      ring
    · simp only [LiftedPhase.jump, h2]
      push_cast
      ring
    · rw [(jump_carries_winding _).2.1, h3]

open Holonics.HolonCore Holonics.Physics.HolonicParametron in
/-- [proved-derived; formal-checked] **The carrier reads only the open phase.** The phase carrier
`e^{2πi t}` of a reading equals that of its open phase: the whole windings are what the circle
forgets and the lift retains. -/
theorem carrier_reads_only_open_phase (t : ℝ) :
    phaseCarrier (2 * Real.pi * t) = phaseCarrier (2 * Real.pi * openPhase t) := by
  have h := (reading_split t).1
  conv_lhs => rw [← h]
  rw [show 2 * Real.pi * ((windings t : ℝ) + openPhase t) =
      2 * Real.pi * openPhase t + 2 * Real.pi * (windings t : ℝ) by ring]
  exact phaseCarrier_add_int_turns _ _

end Ticks

end Holonics.Aeon.Clock.Winding
