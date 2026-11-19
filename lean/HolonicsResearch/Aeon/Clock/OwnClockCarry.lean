import Holonics.HNN.Moment

/-!
# An Own ring keeps its own clock and leaves the carry chain as it was

Source: comment c6249536068 of #62, item 4 (`own_clock_leaves_the_carry_chain`), on the founding
of #398 (`hnn::field::Field::{selective_step, step_class}`, `hnn::receiving::LetterReader` and
`hnn::retention::aeon_readings` at `d5ed4adc1`; atlas `hnn.own-clock-leaves-the-carry-chain`). A
field's rings step one cell down a chain: a Lock ring advances by its cell's step before carry (its
lock's fit `[c ∈ N_g]`, or a located digit) plus the carry its predecessor passes, and passes on the
number of its sections the advance crossed, `⌊(τ + a)/d⌋ − ⌊τ/d⌋` (`HNN/Moment.SelectiveDecl.carryIn`).
A founded ring is declared `Own` (`Field::declare` sets every ring past the declaration's own to
`RingAdvance::Own`): `step_class` ticks it once on every cell, reads no carry and passes the carry it
met unchanged. The box: an Own ring ticks one a cell with carry zero in and out, so each Lock tick and
the final Lock carry are those of the field without its Own suffix.

## What is proved

* **An Own ring ticks once and passes the carry** (`chain_cons_own`, `own_tick_ignores_carry`): its
  tick is one whatever carry reaches it, and the next ring meets that carry unchanged, so its own
  carry in and carry out are zero.
* **An Own ring anywhere leaves the chain** (`chain_insert_own`): inserting it at any place inserts a
  tick of one at that place and changes no other tick and not the carry out.
* **`own_clock_leaves_the_carry_chain`.** With the Own rings as a suffix, the chain's ticks are the
  Lock chain's followed by ones, and its carry out is the Lock chain's
  (`chain_append_owns`, `own_clock_leaves_the_carry_chain`).
* **Over a passage.** One cell moves every lift by its tick (`tick`); over a passage `w` the Lock
  rings' lifts are those of the field without its Own suffix and each Own lift has advanced by
  `|w|` (`run_append_owns`), and the carry out at every cell, the word the joint clock's aeon closes
  on, is the Lock chain's (`carryWord_append_owns`).
* **The Lock chain is `HNN/Moment`'s selective step.** On the rings of a `SelectiveDecl`, the chain
  from ring `g` with the carry `carryIn x τ g` ticks `step_i x + carryIn x τ i` on ring `i` and
  passes `carryIn x τ (g + m)` (`chain_lockRings`), so a founded field's Lock ticks are the selective
  step's advances `advance x τ i − τ i` and its carry out is `carryIn x τ G`
  (`founded_chain_eq_selective`).

## Limits

* The chain is the lock route's (`step_class` with no located digits beyond the ring's own); the
  Rust refuses the located route on a field with an Own ring (`admit_lock_route`), and nothing here
  reads that route with an Own ring.
* `LetterReader` and `aeon_readings` read the lifts and the carry word this module states; their own
  letters and readings are not restated here.

The computational object is the helical pair interaction's carry: a ring is circle plus carry, and a
contact between consecutive rings passes the winding. Of the winding guide's six objects this touches
the helix (each ring's lift and its sections) and the tube (the chain of rings a cell steps, closing
its aeon at the joint clock's carry); the pair, faces and placement, cell holonomy and the tower
thread stay attached through `HNN/Moment`.

Consumers: `HNN/Moment.SelectiveDecl.{carryIn, advance, step}`, the founding's field
(`hnn::field::Field::{selective_step, step_class, declare}` at `d5ed4adc1`), and the atlas row
`hnn.own-clock-leaves-the-carry-chain`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Aeon.Clock.OwnClockCarry

open Holonics.HNN.Moment

/-- [definition] **How a ring advances** (`RingAdvance`): a Lock ring by its cell's step plus the
carry; an Own ring one tick a cell. -/
inductive Advance
  | lock
  | own
  deriving DecidableEq

/-- [definition] **A ring of the chain**: its advance law, its period, and each cell's step before
carry (the lock's fit, or a located digit). -/
structure ClockRing (Cell : Type*) where
  advance : Advance
  period : ℕ
  digit : Cell → ℕ

variable {Cell : Type*}

/-- [definition] **The carry a Lock ring passes**: the sections of period `d` that the advance `a`
from the lift `τ` crosses, `⌊(τ + a)/d⌋ − ⌊τ/d⌋`. -/
def ringCarry (r : ClockRing Cell) (τ a : ℕ) : ℕ := (τ + a) / r.period - τ / r.period

/-- [definition] **One cell's step down the chain** (`Field::step_class`): the rings with their
lifts, and the carry reaching the first; it returns each ring's tick and the carry out. An Own ring
ticks one and passes the carry unchanged; a Lock ring ticks its step plus the carry and passes its
own crossings. -/
def chain (x : Cell) : List (ClockRing Cell × ℕ) → ℕ → List ℕ × ℕ
  | [], c => ([], c)
  | (r, τ) :: rs, c =>
    match r.advance with
    | .own => (1 :: (chain x rs c).1, (chain x rs c).2)
    | .lock => ((r.digit x + c) :: (chain x rs (ringCarry r τ (r.digit x + c))).1,
        (chain x rs (ringCarry r τ (r.digit x + c))).2)

@[simp] theorem chain_nil (x : Cell) (c : ℕ) : chain x [] c = ([], c) := rfl

/-- [proved-derived; formal-checked] **An Own ring ticks once and passes the carry it met.** -/
theorem chain_cons_own (x : Cell) {r : ClockRing Cell} (h : r.advance = .own) (τ : ℕ)
    (rs : List (ClockRing Cell × ℕ)) (c : ℕ) :
    chain x ((r, τ) :: rs) c = (1 :: (chain x rs c).1, (chain x rs c).2) := by
  simp only [chain, h]

/-- [proved-derived; formal-checked] A Lock ring ticks its step plus the carry and passes its own
crossings. -/
theorem chain_cons_lock (x : Cell) {r : ClockRing Cell} (h : r.advance = .lock) (τ : ℕ)
    (rs : List (ClockRing Cell × ℕ)) (c : ℕ) :
    chain x ((r, τ) :: rs) c =
      ((r.digit x + c) :: (chain x rs (ringCarry r τ (r.digit x + c))).1,
        (chain x rs (ringCarry r τ (r.digit x + c))).2) := by
  simp only [chain, h]

/-- [proved-derived; formal-checked] **Carry zero in and out**: an Own ring's tick is one whatever
carry reaches it, and the rings after it meet the same chain as if it were absent. -/
theorem own_tick_ignores_carry (x : Cell) {r : ClockRing Cell} (h : r.advance = .own) (τ : ℕ)
    (rs : List (ClockRing Cell × ℕ)) (c c' : ℕ) :
    (chain x ((r, τ) :: rs) c).1.head? = some 1 ∧
      (chain x ((r, τ) :: rs) c').1.head? = some 1 ∧
      (chain x ((r, τ) :: rs) c).1.tail = (chain x rs c).1 ∧
      (chain x ((r, τ) :: rs) c).2 = (chain x rs c).2 := by
  simp [chain_cons_own x h]

/-- [proved-derived; formal-checked] Every ring ticks once on a cell. -/
theorem chain_length (x : Cell) : ∀ (rs : List (ClockRing Cell × ℕ)) (c : ℕ),
    (chain x rs c).1.length = rs.length
  | [], _ => rfl
  | (r, τ) :: rs, c => by
    cases h : r.advance
    · rw [chain_cons_lock x h, List.length_cons, List.length_cons, chain_length x rs]
    · rw [chain_cons_own x h, List.length_cons, List.length_cons, chain_length x rs]

/-- [proved-derived; formal-checked] **An Own ring anywhere leaves the chain**: inserted at any
place it inserts a tick of one there and changes no other tick and not the carry out. -/
theorem chain_insert_own (x : Cell) {r : ClockRing Cell} (h : r.advance = .own) (τ : ℕ) :
    ∀ (pre post : List (ClockRing Cell × ℕ)) (c : ℕ),
      chain x (pre ++ (r, τ) :: post) c =
        ((chain x (pre ++ post) c).1.insertIdx pre.length 1, (chain x (pre ++ post) c).2)
  | [], post, c => by
    rw [List.nil_append, List.nil_append, chain_cons_own x h, List.length_nil, List.insertIdx_zero]
  | (r', τ') :: pre, post, c => by
    cases h' : r'.advance
    · rw [List.cons_append, List.cons_append, chain_cons_lock x h', chain_cons_lock x h',
        chain_insert_own x h τ pre post, List.length_cons, List.insertIdx_succ_cons]
    · rw [List.cons_append, List.cons_append, chain_cons_own x h', chain_cons_own x h',
        chain_insert_own x h τ pre post, List.length_cons, List.insertIdx_succ_cons]

/-- [proved-derived; formal-checked] A chain of Own rings ticks one each and passes the carry. -/
theorem chain_owns (x : Cell) : ∀ (os : List (ClockRing Cell × ℕ)), (∀ p ∈ os, p.1.advance = .own) →
    ∀ c, chain x os c = (List.replicate os.length 1, c)
  | [], _, _ => rfl
  | (r, τ) :: os, hos, c => by
    rw [chain_cons_own x (hos (r, τ) List.mem_cons_self),
      chain_owns x os (fun p hp => hos p (List.mem_cons_of_mem _ hp)), List.length_cons,
      List.replicate_succ]

/-- [proved-derived; formal-checked] **An Own suffix appends ones and keeps the carry out.** -/
theorem chain_append_owns (x : Cell) {os : List (ClockRing Cell × ℕ)}
    (hos : ∀ p ∈ os, p.1.advance = .own) :
    ∀ (ls : List (ClockRing Cell × ℕ)) (c : ℕ),
      chain x (ls ++ os) c = ((chain x ls c).1 ++ List.replicate os.length 1, (chain x ls c).2)
  | [], c => by rw [List.nil_append, chain_owns x os hos, chain_nil, List.nil_append]
  | (r, τ) :: ls, c => by
    cases h : r.advance
    · rw [List.cons_append, chain_cons_lock x h, chain_cons_lock x h, chain_append_owns x hos ls,
        List.cons_append]
    · rw [List.cons_append, chain_cons_own x h, chain_cons_own x h, chain_append_owns x hos ls,
        List.cons_append]

/-- [proved-derived; formal-checked] **`own_clock_leaves_the_carry_chain`.** On a field whose Own
rings form the founded suffix, each Lock tick and the final Lock carry are those of the field
without its Own suffix, and each Own ring ticks one. -/
theorem own_clock_leaves_the_carry_chain (x : Cell) (ls : List (ClockRing Cell × ℕ))
    {os : List (ClockRing Cell × ℕ)} (hos : ∀ p ∈ os, p.1.advance = .own) (c : ℕ) :
    (chain x (ls ++ os) c).1.take ls.length = (chain x ls c).1 ∧
      (chain x (ls ++ os) c).1.drop ls.length = List.replicate os.length 1 ∧
      (chain x (ls ++ os) c).2 = (chain x ls c).2 := by
  rw [chain_append_owns x hos]
  exact ⟨List.take_left' (chain_length x ls c), List.drop_left' (chain_length x ls c), rfl⟩

/-! ## Over a passage -/

/-- [definition] **One cell moves every lift by its tick**, the chain read from carry zero. -/
def tick (x : Cell) (rs : List (ClockRing Cell × ℕ)) : List (ClockRing Cell × ℕ) :=
  List.zipWith (fun p t => (p.1, p.2 + t)) rs (chain x rs 0).1

/-- [definition] **The lifts after a passage.** -/
def run : List Cell → List (ClockRing Cell × ℕ) → List (ClockRing Cell × ℕ)
  | [], rs => rs
  | x :: w, rs => run w (tick x rs)

/-- [definition] **The carry word**: the carry out of the chain at each cell of the passage, the
joint clock's carry at which its aeon closes. -/
def carryWord : List Cell → List (ClockRing Cell × ℕ) → List ℕ
  | [], _ => []
  | x :: w, rs => (chain x rs 0).2 :: carryWord w (tick x rs)

theorem zipWith_replicate_one (os : List (ClockRing Cell × ℕ)) :
    List.zipWith (fun p t => (p.1, p.2 + t)) os (List.replicate os.length 1) =
      os.map fun p => (p.1, p.2 + 1) := by
  induction os with
  | nil => rfl
  | cons p os ih => rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, ih,
      List.map_cons]

/-- [proved-derived; formal-checked] A cell moves the Lock lifts as the field without its Own suffix
and each Own lift by one. -/
theorem tick_append_owns (x : Cell) (ls : List (ClockRing Cell × ℕ)) {os : List (ClockRing Cell × ℕ)}
    (hos : ∀ p ∈ os, p.1.advance = .own) :
    tick x (ls ++ os) = tick x ls ++ os.map fun p => (p.1, p.2 + 1) := by
  rw [tick, chain_append_owns x hos, List.zipWith_append (chain_length x ls 0).symm,
    zipWith_replicate_one, tick]

/-- [proved-derived; formal-checked] **Over a passage `w`**, the Lock rings' lifts are those of the
field without its Own suffix, and each Own lift has advanced by `|w|`. -/
theorem run_append_owns : ∀ (w : List Cell) (ls : List (ClockRing Cell × ℕ))
    {os : List (ClockRing Cell × ℕ)}, (∀ p ∈ os, p.1.advance = .own) →
    run w (ls ++ os) = run w ls ++ os.map fun p => (p.1, p.2 + w.length)
  | [], ls, os, _ => by simp [run]
  | x :: w, ls, os, hos => by
    have hos' : ∀ p ∈ os.map (fun p => (p.1, p.2 + 1)), p.1.advance = .own := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hos q hq
    rw [run, tick_append_owns x ls hos, run_append_owns w (tick x ls) hos', run, List.map_map,
      List.length_cons]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp, Prod.mk.injEq, true_and]
    omega

/-- [proved-derived; formal-checked] **The carry word is the Lock chain's**: at every cell of a
passage the carry out is that of the field without its Own suffix, so the aeon closes at the same
cell. -/
theorem carryWord_append_owns : ∀ (w : List Cell) (ls : List (ClockRing Cell × ℕ))
    {os : List (ClockRing Cell × ℕ)}, (∀ p ∈ os, p.1.advance = .own) →
    carryWord w (ls ++ os) = carryWord w ls
  | [], _, _, _ => rfl
  | x :: w, ls, os, hos => by
    have hos' : ∀ p ∈ os.map (fun p => (p.1, p.2 + 1)), p.1.advance = .own := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hos q hq
    rw [carryWord, carryWord, (chain_append_owns x hos ls 0), tick_append_owns x ls hos,
      carryWord_append_owns w (tick x ls) hos']

/-! ## The Lock chain is the selective step of `HNN/Moment` -/

section Selective

variable (D : SelectiveDecl Cell)

/-- [definition] **The Lock rings `g, …, g + m − 1` of a selective declaration** with their lifts. -/
def lockRings (τ : ℕ → ℕ) (g m : ℕ) : List (ClockRing Cell × ℕ) :=
  (List.range' g m).map fun i => (⟨.lock, D.period i, D.step i⟩, τ i)

/-- [proved-derived; formal-checked] **The Lock chain is the selective step.** From ring `g` with
the carry `carryIn x τ g`, ring `i` ticks `step_i x + carryIn x τ i` and the chain passes
`carryIn x τ (g + m)`. -/
theorem chain_lockRings (x : Cell) (τ : ℕ → ℕ) : ∀ (m g : ℕ),
    chain x (lockRings D τ g m) (D.carryIn x τ g) =
      ((List.range' g m).map fun i => D.step i x + D.carryIn x τ i, D.carryIn x τ (g + m))
  | 0, g => by simp [lockRings]
  | m + 1, g => by
    have hcarry : ringCarry (⟨.lock, D.period g, D.step g⟩ : ClockRing Cell) (τ g)
        (D.step g x + D.carryIn x τ g) = D.carryIn x τ (g + 1) := by
      simp only [ringCarry, SelectiveDecl.carryIn, add_assoc]
    have h := chain_lockRings x τ m (g + 1)
    simp only [lockRings, List.range'_succ, List.map_cons] at h ⊢
    rw [chain_cons_lock x rfl, hcarry, h, show g + 1 + m = g + (m + 1) by omega]

/-- [proved-derived; formal-checked] **A founded field's step is the selective step with ones
appended.** On `G` Lock rings of a selective declaration followed by Own rings, from carry zero, the
Lock ticks are the selective advances `advance x τ i − τ i`, each Own ring ticks one, and the carry
out is `carryIn x τ G`. -/
theorem founded_chain_eq_selective (x : Cell) (τ : ℕ → ℕ) (G : ℕ) {os : List (ClockRing Cell × ℕ)}
    (hos : ∀ p ∈ os, p.1.advance = .own) :
    chain x (lockRings D τ 0 G ++ os) 0 =
      ((List.range G).map (fun i => D.advance x τ i - τ i) ++ List.replicate os.length 1,
        D.carryIn x τ G) := by
  have h0 : D.carryIn x τ 0 = 0 := rfl
  have h := chain_lockRings D x τ G 0
  rw [h0, zero_add] at h
  rw [chain_append_owns x hos, h, List.range_eq_range']
  congr 2
  refine List.map_congr_left fun i _ => ?_
  simp only [SelectiveDecl.advance]
  omega

end Selective

end Holonics.Aeon.Clock.OwnClockCarry
