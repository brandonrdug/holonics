import Holonics.Aeon.Production.FirstLaw
import Mathlib.Tactic

/-!
# Receiving precision: publication is a deposition-class step without an arrival, the partition telescopes, and it
# survives the same-moment ingest, a refusal, a close and a cold restore

Issue #62's comment of October 18 (owed by #393, merged at `5cc91c7b`) and the records of October 16 and 17
(`research/records/2026-10-16_RECEIVING_PRECISION_PUBLISHES_THE_ARRIVED_FIRST_LAW_ENDPOINT.md`,
`research/records/2026-10-17_OBSERVED_RECEIVING_PRECISION_CONTINUES_THE_SAME_MOMENT.md`, sections "Lean owed") list six
statements on receiving precision. This module models the Rust owners at `5cc91c7b` (unchanged at `d5ed4adc1` but
for the ledger's `found`, one more exchange step) and proves each.

**The model and its Rust.**
- `Encl` is `ExactInterval`, with `plus` and `minus` its exact Minkowski sum and difference and `width` its width
  (`aeon/first_law.rs`, `plus`, `minus`, `width`).
- `Balance` is `EnclosedBalance` field for field, and `Balance.opened` its `opened`. `step`, `arrive`, `deposit`,
  `publish`, `release` and `close` are `EnclosedLedger::{step, arrive, deposit, publish, release, close}`: a step reads
  the occurrence reached (refused, as `AeonError::NoOccurrence`, before any reading), adds that occurrence's width to
  the widening after the first step, adds the move `next − at` to its kind's subtotals and count, and makes `next` the
  occurrence reached. A refusal is `none`, and a refused step leaves the balance as it was.
- `Resident` keeps the parts of `hnn::reference::Resident` that receiving precision reads or writes: the constitution,
  the pending and staged handle counts, the arrived operand, the ledger, the charts and tally (`aux`), the open moment
  and its cells, and the aeon's `awaiting`. `publishPrecision` is `Resident::publish_receiving_precision`
  (`hnn/reference.rs`): the event's material check, the refusal while a pending or staged handle stands, the
  `PrecisionOccurrence` refusal when the ledger's occurrence and the arrived operand disagree, the receiving-only
  rebase, and, where an operand arrived, its reread at the successor published as one ledger step, all committed
  together.
- `ingestCell` is the ingest's effect on these parts (`Reference::ingest`): it refuses past the population or while the
  aeon awaits its close, advances the open moment by one cell, and writes neither the ledger nor the arrived operand.
  `closeAeon` is `close_aeon`'s ledger part: an optional release step, then `EnclosedLedger::close`.
- `Crib` is `ObservedCrib` (`hnn/reference/observed.rs`): its positions, `push` keeping the positions at least
  `next − window` (the Rust's `partition_point` and `drain` on its ascending positions), and `reopen`.
- `observeCell` is `observe_cell_continuing` from the deposited successor on: the precision event (when the staged
  features select one), the read-only post-deposit view, the shared ingest, the crib's push and, at carry-out, the
  close and the crib's reopening, on clones; `observeCellPublic` commits the clones only on success.
- `Saved` and `restore` are the passage's `write_balance` and `read_balance` (`hnn/reference/passage.rs`, version 4):
  the counts and the widening, the enclosures, and the refusal of a saved balance whose deposited and published
  subtotals do not add to its inclusive deposition. The text form of a rational is taken to read back as written.

**What is proved.**
1. **Inclusive deposition is deposited plus published, and the partition telescopes.** `Inv` holds on an opened
   ledger and is kept by every step, arrival and close (`inv_opened`, `inv_step`, `inv_arrive`, `inv_close`,
   `inv_run`): the inclusive deposition is the sum of the deposited and published subtotals
   (`deposition_eq_deposited_plus_published`), and once a step is taken, exchange plus deposited plus published is the
   change `closing − opening` widened by the interior widths on each side (`partition_telescopes`). On exact code
   lengths the three kinds' sums telescope to `C N − C 0`, with the deposition-class sum of `FirstLaw` split into its
   deposited and published parts (`exact_deposition_partition`, `exact_partition_telescopes`, through
   `Aeon/Production/FirstLaw.ledger_telescopes`).
2. **Publication is a deposition-class step without a new arrival** (`publish_spec`, `publish_deposition_class`): it
   moves the inclusive deposition, the total, the occurrence reached and the widening exactly as a deposit would,
   enters the published subtotal and count in place of the deposited ones, and leaves the arrivals, the cells and the
   sealed arrival score alone; only `arrive` changes them (`arrivals_step`).
3. **The arrived reread preserves the sealed arrival score and sample count** (`publishPrecision_seals`,
   `publishPrecision_reread`): a publication keeps the arrived operand, the ledger's arrivals, cells and arrived score,
   and the moment; where an operand arrived, the occurrence reached is its reread at the successor. Without an arrived
   operand the ledger is untouched (`publishPrecision_no_arrival`), and a disagreement is refused
   (`publishPrecision_occurrence_refused`).
4. **Publication composes with the same-moment ingest** (`ingest_after_publish`, `close_after_publish`): the ingest
   after a publication keeps the published ledger and the arrived operand and advances the same moment by one cell;
   at carry-out the closed aeon's balance keeps the published subtotal, the count of publications and the arrivals,
   and the next aeon opens at the occurrence reached.
5. **A refused later ingest or close preserves the resident, the bounded crib and the exterior view**
   (`observeCellPublic_ingest_refused`, `observeCellPublic_close_refused`): the public step returns the resident and
   the crib it was given and releases no view. The crib is bounded: a pushed crib holds at most `window` cells, its
   positions increasing and below `next` (`Crib.Bounded`, `Crib.bounded_push`, `Crib.length_le`), and so is every crib
   the public step returns (`observeCellPublic_bounded`).
6. **The partition and its telescoping survive a close and a cold restore** (`inv_close`, `restore_save`,
   `inv_restore_save`, `restore_partitioned`): a saved balance that satisfies `Inv` restores to itself, and every
   restored balance satisfies the partition. The version-4 reader checks the partition and not the telescoping:
   `restore_accepts_untelescoped` restores a balance with no step and a nonzero exchange.

The computational object is the helical pair interaction's ledger read at a receiver: a reception's arrived operand and
its code length read through a moving constitution, the steps of the first law on enclosures. Of the winding guide's
six general objects this touches faces and placement (the receiver's enclosed code lengths) and the tube (the aeon
and its close); the helix, the pair, the cell holonomy and the tower thread stay attached.

What stands beside it: the receiving precision event itself (which staged features select an event, its tolerance,
the rebase's lattice), the card's publication with its checkpoint and rollback (`holonics-cuda/src/hnn/port.rs`),
`forget_kept_reads`, the collapse and key location at close, and the text parsing of rationals.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ReceivingPrecision

open Finset

/-! ## 1. Enclosures and the ledger -/

/-- An enclosure `[lower, upper]` (`ExactInterval`). -/
@[ext] structure Encl where
  lower : ℚ
  upper : ℚ
deriving DecidableEq

namespace Encl

/-- The exact Minkowski sum. -/
def plus (a b : Encl) : Encl := ⟨a.lower + b.lower, a.upper + b.upper⟩

/-- The exact Minkowski difference. -/
def minus (a b : Encl) : Encl := ⟨a.lower - b.upper, a.upper - b.lower⟩

def width (a : Encl) : ℚ := a.upper - a.lower

def zero : Encl := ⟨0, 0⟩

@[simp] theorem plus_lower (a b : Encl) : (a.plus b).lower = a.lower + b.lower := rfl
@[simp] theorem plus_upper (a b : Encl) : (a.plus b).upper = a.upper + b.upper := rfl
@[simp] theorem minus_lower (a b : Encl) : (a.minus b).lower = a.lower - b.upper := rfl
@[simp] theorem minus_upper (a b : Encl) : (a.minus b).upper = a.upper - b.lower := rfl
@[simp] theorem zero_lower : zero.lower = 0 := rfl
@[simp] theorem zero_upper : zero.upper = 0 := rfl

end Encl

/-- The three kinds of step: an exchange (an arrival after the first reading, a release, a founding), a deposit, and
a publication. Deposits and publications are the deposition class. -/
inductive Kind
  | exchange
  | deposit
  | publication
deriving DecidableEq

/-- One aeon's first law read on enclosed code lengths (`EnclosedBalance`). -/
structure Balance where
  exchange : Encl
  /-- The inclusive deposition-class total. -/
  deposition : Encl
  deposited : Encl
  published : Encl
  opening : Option Encl
  closing : Option Encl
  widening : ℚ
  exchanges : ℕ
  depositions : ℕ
  publications : ℕ
  arrivals : ℕ
  cells : ℕ
  /-- The sealed arrival score: the summed code length of every arrival at the constitution it arrived through. -/
  arrived : Encl

namespace Balance

/-- A balance opened at an occurrence (`EnclosedBalance::opened`). -/
def opened (at_ : Option Encl) : Balance where
  exchange := Encl.zero
  deposition := Encl.zero
  deposited := Encl.zero
  published := Encl.zero
  opening := at_
  closing := at_
  widening := 0
  exchanges := 0
  depositions := 0
  publications := 0
  arrivals := 0
  cells := 0
  arrived := Encl.zero

/-- The steps taken. -/
def steps (b : Balance) : ℕ := b.exchanges + b.depositions + b.publications

/-- `exchange + deposition`. -/
def total (b : Balance) : Encl := b.exchange.plus b.deposition

/-- The step from the occurrence `at_` reached to `next`, of kind `k`. -/
def stepAt (b : Balance) (next : Encl) (k : Kind) (at_ : Encl) : Balance :=
  { b with
    widening := if 0 < b.steps then b.widening + at_.width else b.widening
    closing := some next
    exchange := if k = .exchange then b.exchange.plus (next.minus at_) else b.exchange
    deposition := if k = .exchange then b.deposition else b.deposition.plus (next.minus at_)
    deposited := if k = .deposit then b.deposited.plus (next.minus at_) else b.deposited
    published := if k = .publication then b.published.plus (next.minus at_) else b.published
    exchanges := if k = .exchange then b.exchanges + 1 else b.exchanges
    depositions := if k = .deposit then b.depositions + 1 else b.depositions
    publications := if k = .publication then b.publications + 1 else b.publications }

/-- `EnclosedLedger::step`: refused before any reading. -/
def step (b : Balance) (next : Encl) (k : Kind) : Option Balance := b.closing.map (b.stepAt next k)

/-- The arrival's own counts: its code length added to the arrival score, one arrival and its cells. -/
def counted (b : Balance) (code : Encl) (n : ℕ) : Balance :=
  { b with arrived := b.arrived.plus code, arrivals := b.arrivals + 1, cells := b.cells + n }

/-- `EnclosedLedger::arrive`: new targets read at `code` over `n` cells; an exchange step, or the opening. -/
def arrive (b : Balance) (code : Encl) (n : ℕ) : Balance :=
  match (b.counted code n).step code .exchange with
  | some b' => b'
  | none => { b.counted code n with opening := some code, closing := some code }

def deposit (b : Balance) (reread : Encl) : Option Balance := b.step reread .deposit
def publish (b : Balance) (reread : Encl) : Option Balance := b.step reread .publication
def release (b : Balance) (reread : Encl) : Option Balance := b.step reread .exchange

/-- `EnclosedLedger::close`: the aeon's balance, and the next aeon opened at the occurrence reached. -/
def close (b : Balance) : Balance × Balance := (b, opened b.closing)

/-- **The partition**: the inclusive deposition is the deposited subtotal plus the published one. -/
def Partitioned (b : Balance) : Prop := b.deposition = b.deposited.plus b.published

/-- **The telescoping**: before any step every sum is zero and the aeon opens where it stands; after one, the total is
the change `closing − opening` widened by the interior widths on each side. -/
def Telescopes (b : Balance) : Prop :=
  (b.steps = 0 → b.exchange = Encl.zero ∧ b.deposited = Encl.zero ∧ b.published = Encl.zero ∧ b.widening = 0 ∧
      b.opening = b.closing) ∧
    (0 < b.steps → ∃ o c, b.opening = some o ∧ b.closing = some c ∧
      b.total.lower = c.lower - o.upper - b.widening ∧ b.total.upper = c.upper - o.lower + b.widening)

/-- The ledger's invariant: the partition, the telescoping, and no step before an occurrence. -/
def Inv (b : Balance) : Prop := b.Partitioned ∧ b.Telescopes ∧ (b.closing = none → b.steps = 0)

end Balance

open Balance

theorem step_eq_some {b b' : Balance} {r : Encl} {k : Kind} :
    b.step r k = some b' ↔ ∃ at_, b.closing = some at_ ∧ b' = b.stepAt r k at_ := by
  unfold Balance.step
  cases h : b.closing with
  | none => simp
  | some a => simp [eq_comm]

/-! ## 2. The partition telescopes (box 1) -/

theorem inv_opened (x : Option Encl) : (opened x).Inv := by
  refine ⟨?_, ⟨fun _ => ?_, fun h => ?_⟩, fun _ => rfl⟩
  · ext <;> simp [opened]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp [steps, opened] at h

theorem steps_stepAt (b : Balance) (r : Encl) (k : Kind) (a : Encl) : (b.stepAt r k a).steps = b.steps + 1 := by
  cases k <;> simp [stepAt, steps] <;> omega

theorem total_stepAt (b : Balance) (r : Encl) (k : Kind) (a : Encl) :
    (b.stepAt r k a).total = b.total.plus (r.minus a) := by
  cases k <;> ext <;> simp [stepAt, total] <;> ring

theorem inv_stepAt {b : Balance} (hb : b.Inv) {r a : Encl} (ha : b.closing = some a) (k : Kind) :
    (b.stepAt r k a).Inv := by
  obtain ⟨hp, ⟨h0, hpos⟩, -⟩ := hb
  have hp' : b.deposition = b.deposited.plus b.published := hp
  refine ⟨?_, ⟨fun h => ?_, fun _ => ?_⟩, fun h => ?_⟩
  · unfold Partitioned at hp ⊢
    cases k <;> simp only [stepAt] <;> simp [hp] <;> ext <;> simp <;> ring
  · rw [steps_stepAt] at h; omega
  · rw [total_stepAt]
    rcases Nat.eq_zero_or_pos b.steps with hs | hs
    · obtain ⟨hex, hdd, hpb, hw, ho⟩ := h0 hs
      refine ⟨a, r, ?_, rfl, ?_, ?_⟩
      · simp only [stepAt]; rw [ho, ha]
      · simp [stepAt, hs, total, hp', hex, hdd, hpb, hw]
      · simp [stepAt, hs, total, hp', hex, hdd, hpb, hw]
    · obtain ⟨o, c, ho, hc, hl, hu⟩ := hpos hs
      rw [ha] at hc
      cases hc
      refine ⟨o, r, ?_, rfl, ?_, ?_⟩
      · simpa [stepAt] using ho
      · simp only [Encl.plus_lower, Encl.minus_lower, stepAt, hs, if_true, Encl.width]; rw [hl]; ring
      · simp only [Encl.plus_upper, Encl.minus_upper, stepAt, hs, if_true, Encl.width]; rw [hu]; ring
  · simp [stepAt] at h

/-- **Every step keeps the ledger's invariant.** -/
theorem inv_step {b b' : Balance} (hb : b.Inv) {r : Encl} {k : Kind} (h : b.step r k = some b') : b'.Inv := by
  obtain ⟨a, ha, rfl⟩ := step_eq_some.mp h
  exact inv_stepAt hb ha k

/-- **An arrival keeps the ledger's invariant.** -/
theorem inv_arrive {b : Balance} (hb : b.Inv) (code : Encl) (n : ℕ) : (b.arrive code n).Inv := by
  have hb₀ : (b.counted code n).Inv := hb
  unfold Balance.arrive
  split
  · rename_i b' h
    exact inv_step hb₀ h
  · rename_i h
    have hcl : (b.counted code n).closing = none := by
      unfold Balance.step at h; cases hc : (b.counted code n).closing <;> simp_all
    obtain ⟨hp, ⟨h0, -⟩, hns⟩ := hb₀
    have hs := hns hcl
    obtain ⟨hex, hdd, hpb, hw, -⟩ := h0 hs
    refine ⟨hp, ⟨fun _ => ⟨hex, hdd, hpb, hw, rfl⟩, fun h' => ?_⟩, fun h' => ?_⟩
    · exact absurd h' (by simpa [steps] using hs.le)
    · simp at h'

/-- **The close keeps the invariant on both aeons.** -/
theorem inv_close {b : Balance} (hb : b.Inv) : b.close.1.Inv ∧ b.close.2.Inv := ⟨hb, inv_opened _⟩

/-- **Inclusive deposition is deposited plus published.** -/
theorem deposition_eq_deposited_plus_published {b : Balance} (hb : b.Inv) :
    b.deposition = b.deposited.plus b.published := hb.1

/-- **The partition telescopes**: once a step is taken, exchange plus deposited plus published is the change
`closing − opening` widened by the interior widths on each side. -/
theorem partition_telescopes {b : Balance} (hb : b.Inv) (hs : 0 < b.steps) :
    ∃ o c, b.opening = some o ∧ b.closing = some c ∧
      (b.exchange.plus (b.deposited.plus b.published)).lower = c.lower - o.upper - b.widening ∧
      (b.exchange.plus (b.deposited.plus b.published)).upper = c.upper - o.lower + b.widening := by
  rw [← hb.1]
  exact hb.2.1.2 hs

/-- The ledger's operations, as the resident calls them. -/
inductive Op
  | arrive (code : Encl) (n : ℕ)
  | deposit (reread : Encl)
  | publish (reread : Encl)
  | release (reread : Encl)

def Op.apply (b : Balance) : Op → Option Balance
  | .arrive code n => some (b.arrive code n)
  | .deposit r => b.deposit r
  | .publish r => b.publish r
  | .release r => b.release r

/-- A run of operations, refused at its first refused step. -/
def run (b : Balance) : List Op → Option Balance
  | [] => some b
  | op :: ops => (op.apply b).bind fun b' => run b' ops

/-- **Along any run the partition and its telescoping hold.** -/
theorem inv_run : ∀ (ops : List Op) {b b' : Balance}, b.Inv → run b ops = some b' → b'.Inv
  | [], b, b', hb, h => by simp [run] at h; exact h ▸ hb
  | op :: ops, b, b', hb, h => by
      simp only [run, Option.bind_eq_some_iff] at h
      obtain ⟨b₁, h₁, h₂⟩ := h
      refine inv_run ops ?_ h₂
      cases op with
      | arrive code n => simp [Op.apply] at h₁; exact h₁ ▸ inv_arrive hb code n
      | deposit r => exact inv_step hb h₁
      | publish r => exact inv_step hb h₁
      | release r => exact inv_step hb h₁

/-- The exact sum of the steps of kind `k₀` along code lengths `C`. -/
noncomputable def exactPart (C : ℕ → ℝ) (κ : ℕ → Kind) (k₀ : Kind) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, if κ k = k₀ then C (k + 1) - C k else 0

/-- A deposition-class step. -/
def depClass (k : Kind) : Bool := decide (k ≠ .exchange)

/-- **On exact code lengths the deposition class is deposited plus published**: `FirstLaw`'s deposition sum, read
with deposits and publications as its moving steps, splits into the two subtotals. -/
theorem exact_deposition_partition (C : ℕ → ℝ) (κ : ℕ → Kind) (N : ℕ) :
    Aeon.Production.FirstLaw.ledgerDeposition C (fun k => depClass (κ k)) N =
      exactPart C κ .deposit N + exactPart C κ .publication N := by
  unfold Aeon.Production.FirstLaw.ledgerDeposition exactPart
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  cases h : κ k <;> simp [h, depClass]

/-- **The three kinds telescope** to the change of code length, through `FirstLaw.ledger_telescopes`. -/
theorem exact_partition_telescopes (C : ℕ → ℝ) (κ : ℕ → Kind) (N : ℕ) :
    exactPart C κ .exchange N + exactPart C κ .deposit N + exactPart C κ .publication N = C N - C 0 := by
  rw [add_assoc, ← exact_deposition_partition, ← Aeon.Production.FirstLaw.ledger_telescopes C
    (fun k => depClass (κ k)) N]
  congr 1
  unfold Aeon.Production.FirstLaw.ledgerExchange exactPart
  refine sum_congr rfl fun k _ => ?_
  cases h : κ k <;> simp [h, depClass]

/-! ## 3. Publication is a deposition-class step without a new arrival (box 2) -/

/-- **Publication**: one published step, no arrival, no cell, the sealed arrival score untouched. -/
theorem publish_spec {b b' : Balance} {r : Encl} (h : b.publish r = some b') :
    ∃ a, b.closing = some a ∧ b'.closing = some r ∧ b'.published = b.published.plus (r.minus a) ∧
      b'.deposition = b.deposition.plus (r.minus a) ∧ b'.deposited = b.deposited ∧ b'.exchange = b.exchange ∧
      b'.publications = b.publications + 1 ∧ b'.depositions = b.depositions ∧ b'.exchanges = b.exchanges ∧
      b'.arrivals = b.arrivals ∧ b'.cells = b.cells ∧ b'.arrived = b.arrived ∧ b'.opening = b.opening := by
  obtain ⟨a, ha, rfl⟩ := step_eq_some.mp h
  exact ⟨a, ha, by simp [stepAt]⟩

/-- **Publication is of the deposition class**: it moves the inclusive deposition, the exchange, the total, the
occurrence reached and the widening exactly as a deposit does. -/
theorem publish_deposition_class (b : Balance) (r : Encl) :
    (b.publish r).map (fun b' => (b'.deposition, b'.exchange, b'.total, b'.closing, b'.widening, b'.steps)) =
      (b.deposit r).map (fun b' => (b'.deposition, b'.exchange, b'.total, b'.closing, b'.widening, b'.steps)) := by
  unfold Balance.publish Balance.deposit Balance.step
  cases b.closing with
  | none => rfl
  | some a => simp [stepAt, total, steps]; omega

/-- **Only an arrival changes the arrivals, the cells and the arrival score**: no step of any kind does. -/
theorem arrivals_step {b b' : Balance} {r : Encl} {k : Kind} (h : b.step r k = some b') :
    b'.arrivals = b.arrivals ∧ b'.cells = b.cells ∧ b'.arrived = b.arrived := by
  obtain ⟨a, -, rfl⟩ := step_eq_some.mp h
  exact ⟨rfl, rfl, rfl⟩

/-! ## 4. The resident's publication (box 3) -/

/-- The laws the resident's publication reads: the event's material check, the receiving-only rebase, and the
arrived operand's code length at a constitution, which writes the charts and tally. -/
structure Laws (Θ A X : Type*) where
  admits : Θ → Bool
  rebase : Θ → Option Θ
  read : A → Θ → X → Option (Encl × X)

/-- The parts of a resident that receiving precision reads or writes. -/
structure Resident (Θ A X M : Type*) where
  constitution : Θ
  pending : ℕ
  staged : ℕ
  arrived : Option A
  ledger : Balance
  aux : X
  moment : Option M
  momentCells : ℕ
  awaiting : Bool

variable {Θ A X M : Type*}

/-- `Resident::publish_receiving_precision`. -/
def publishPrecision (L : Laws Θ A X) (r : Resident Θ A X M) : Option (Resident Θ A X M) :=
  if L.admits r.constitution = false then none
  else if r.pending ≠ 0 ∨ r.staged ≠ 0 then none
  else if r.ledger.closing.isSome ≠ r.arrived.isSome then none
  else
    match L.rebase r.constitution with
    | none => none
    | some next =>
        match r.arrived with
        | none => some { r with constitution := next }
        | some a =>
            match L.read a next r.aux with
            | none => none
            | some (e, aux') =>
                (r.ledger.publish e).map fun l => { r with constitution := next, ledger := l, aux := aux' }

theorem publishPrecision_cases {L : Laws Θ A X} {r r' : Resident Θ A X M} (h : publishPrecision L r = some r') :
    r.pending = 0 ∧ r.staged = 0 ∧ ∃ next, L.rebase r.constitution = some next ∧ r'.constitution = next ∧
      ((r.arrived = none ∧ r'.ledger = r.ledger ∧ r'.aux = r.aux) ∨
        ∃ a e, r.arrived = some a ∧ L.read a next r.aux = some (e, r'.aux) ∧ r.ledger.publish e = some r'.ledger) ∧
      r'.arrived = r.arrived ∧ r'.moment = r.moment ∧ r'.momentCells = r.momentCells ∧ r'.pending = r.pending ∧
      r'.staged = r.staged ∧ r'.awaiting = r.awaiting := by
  unfold publishPrecision at h
  split_ifs at h with h1 h2 h3
  simp only [not_or, ne_eq, not_not] at h2
  obtain ⟨hp, hs⟩ := h2
  cases hn : L.rebase r.constitution with
  | none => simp [hn] at h
  | some next =>
      simp only [hn] at h
      cases ha : r.arrived with
      | none =>
          simp only [ha, Option.some.injEq] at h
          subst h
          exact ⟨hp, hs, next, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩, ha.symm ▸ rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some a =>
          simp only [ha] at h
          cases hr : L.read a next r.aux with
          | none => simp [hr] at h
          | some p =>
              obtain ⟨e, aux'⟩ := p
              simp only [hr, Option.map_eq_some_iff] at h
              obtain ⟨l, hl, rfl⟩ := h
              exact ⟨hp, hs, next, rfl, rfl, Or.inr ⟨a, e, rfl, hr, hl⟩, ha.symm ▸ rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The arrived reread preserves the sealed arrival score and sample count**: a publication keeps the arrived
operand, the ledger's arrivals, cells and arrival score, and the open moment with its cells. -/
theorem publishPrecision_seals {L : Laws Θ A X} {r r' : Resident Θ A X M} (h : publishPrecision L r = some r') :
    r'.arrived = r.arrived ∧ r'.ledger.arrivals = r.ledger.arrivals ∧ r'.ledger.cells = r.ledger.cells ∧
      r'.ledger.arrived = r.ledger.arrived ∧ r'.moment = r.moment ∧ r'.momentCells = r.momentCells := by
  obtain ⟨-, -, next, -, -, hcase, harr, hm, hmc, -⟩ := publishPrecision_cases h
  refine ⟨harr, ?_, ?_, ?_, hm, hmc⟩ <;> rcases hcase with ⟨-, hl, -⟩ | ⟨a, e, -, -, hp⟩ <;>
    first | rw [hl] | exact (arrivals_step hp).1 | exact (arrivals_step hp).2.1 | exact (arrivals_step hp).2.2

/-- **The reread at the successor is the occurrence reached**: where an operand arrived, the publication is one
published step to its code length at the rebased constitution. -/
theorem publishPrecision_reread {L : Laws Θ A X} {r r' : Resident Θ A X M} {a : A} (ha : r.arrived = some a)
    (h : publishPrecision L r = some r') :
    ∃ e, L.read a r'.constitution r.aux = some (e, r'.aux) ∧ r'.ledger.closing = some e ∧
      r'.ledger.publications = r.ledger.publications + 1 ∧ r'.ledger.depositions = r.ledger.depositions ∧
      r'.ledger.deposited = r.ledger.deposited := by
  obtain ⟨-, -, next, -, hc, hcase, -⟩ := publishPrecision_cases h
  rcases hcase with ⟨hn, -⟩ | ⟨a', e, ha', hr, hp⟩
  · rw [ha] at hn; cases hn
  · rw [ha] at ha'; cases ha'
    obtain ⟨-, -, hcl, -, -, hdd, -, hpub, hdep, -⟩ := publish_spec hp
    exact ⟨e, hc ▸ hr, hcl, hpub, hdep, hdd⟩

/-- Without an arrived operand a publication rebases the constitution and leaves the ledger. -/
theorem publishPrecision_no_arrival {L : Laws Θ A X} {r r' : Resident Θ A X M} (ha : r.arrived = none)
    (h : publishPrecision L r = some r') : r'.ledger = r.ledger := by
  obtain ⟨-, -, next, -, -, hcase, -⟩ := publishPrecision_cases h
  rcases hcase with ⟨-, hl, -⟩ | ⟨a, e, ha', -⟩
  · exact hl
  · rw [ha] at ha'; cases ha'

/-- **`PrecisionOccurrence`**: an occurrence without an arrived operand, or the reverse, is refused. -/
theorem publishPrecision_occurrence_refused (L : Laws Θ A X) (r : Resident Θ A X M)
    (h : r.ledger.closing.isSome ≠ r.arrived.isSome) : publishPrecision L r = none := by
  unfold publishPrecision
  split_ifs <;> rfl

/-- A publication keeps the ledger's invariant. -/
theorem publishPrecision_inv {L : Laws Θ A X} {r r' : Resident Θ A X M} (hb : r.ledger.Inv)
    (h : publishPrecision L r = some r') : r'.ledger.Inv := by
  obtain ⟨-, -, next, -, -, hcase, -⟩ := publishPrecision_cases h
  rcases hcase with ⟨-, hl, -⟩ | ⟨a, e, -, -, hp⟩
  · exact hl ▸ hb
  · exact inv_step hb hp

/-! ## 5. The same-moment ingest and the close (box 4) -/

/-- The ingest's effect on these parts: refused past the population or while the aeon awaits its close; one cell of
the same moment; neither the ledger nor the arrived operand is written. -/
def ingestCell (population : ℕ) (r : Resident Θ A X M) : Option (Resident Θ A X M) :=
  if r.awaiting = true ∨ population ≤ r.momentCells then none else some { r with momentCells := r.momentCells + 1 }

/-- The close's ledger part: an optional release step, then the ledger's close; the closed balance is returned. -/
def closeAeon (release : Option Encl) (r : Resident Θ A X M) : Option (Resident Θ A X M × Balance) :=
  match release with
  | none => some ({ r with ledger := r.ledger.close.2, awaiting := false }, r.ledger.close.1)
  | some e => (r.ledger.release e).map fun l => ({ r with ledger := l.close.2, awaiting := false }, l.close.1)

/-- **The ingest after a publication keeps the published ledger** and the arrived operand, and advances the same
moment by one cell: no arrival is added by either. -/
theorem ingest_after_publish {L : Laws Θ A X} {r r₁ r₂ : Resident Θ A X M} {population : ℕ}
    (h₁ : publishPrecision L r = some r₁) (h₂ : ingestCell population r₁ = some r₂) :
    r₂.ledger = r₁.ledger ∧ r₂.arrived = r.arrived ∧ r₂.moment = r.moment ∧ r₂.momentCells = r.momentCells + 1 ∧
      r₂.ledger.arrivals = r.ledger.arrivals ∧ r₂.ledger.arrived = r.ledger.arrived := by
  obtain ⟨harr, hn, -, hsc, hm, hmc⟩ := publishPrecision_seals h₁
  unfold ingestCell at h₂
  split_ifs at h₂
  cases h₂
  exact ⟨rfl, harr, hm, by simp [hmc], hn, hsc⟩

/-- **At carry-out the closed aeon keeps the publication**: its published subtotal and count of publications, its
arrivals and arrival score are the published ledger's, the partition and telescoping hold on it, and the next aeon
opens at the occurrence reached with the invariant. -/
theorem close_after_publish {r₂ r₃ : Resident Θ A X M} {closed : Balance} {release : Option Encl}
    (hb : r₂.ledger.Inv) (h : closeAeon release r₂ = some (r₃, closed)) :
    closed.published = r₂.ledger.published ∧ closed.publications = r₂.ledger.publications ∧
      closed.arrivals = r₂.ledger.arrivals ∧ closed.arrived = r₂.ledger.arrived ∧ closed.Inv ∧
      r₃.ledger = opened closed.closing ∧ r₃.ledger.Inv ∧ r₃.arrived = r₂.arrived ∧ r₃.moment = r₂.moment := by
  unfold closeAeon at h
  cases release with
  | none =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, rfl, hb, rfl, inv_opened _, rfl, rfl⟩
  | some e =>
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨l, hl, rfl, rfl⟩ := h
      obtain ⟨a, ha, rfl⟩ := step_eq_some.mp hl
      exact ⟨by simp [stepAt, close], by simp [stepAt, close], rfl, rfl, inv_stepAt hb ha _, rfl, inv_opened _, rfl,
        rfl⟩

/-! ## 6. The bounded crib and the transaction (box 5) -/

/-- The observed crib: its opening, the next position, and its cells with their positions. -/
structure Crib (α : Type*) where
  opening : ℕ
  next : ℕ
  entries : List (ℕ × α)

namespace Crib

variable {α : Type*}

/-- `ObservedCrib::push`: the cell at `next`, keeping the positions at least `next + 1 − window`. -/
def push (window : ℕ) (c : Crib α) (x : α) : Crib α where
  opening := c.opening
  next := c.next + 1
  entries := (c.entries ++ [(c.next, x)]).filter fun e => c.next + 1 - window ≤ e.1

/-- `ObservedCrib::reopen`. -/
def reopen (c : Crib α) : Crib α := ⟨c.next, c.next, []⟩

/-- **A bounded crib**: increasing positions, each in `[next − window, next)`. -/
def Bounded (window : ℕ) (c : Crib α) : Prop :=
  (c.entries.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ c.entries, c.next - window ≤ e.1 ∧ e.1 < c.next

theorem bounded_push {window : ℕ} {c : Crib α} (hc : c.Bounded window) (x : α) : (c.push window x).Bounded window := by
  obtain ⟨hpw, hbd⟩ := hc
  have hpair : ((c.entries ++ [(c.next, x)]).map Prod.fst).Pairwise (· < ·) := by
    rw [List.map_append, List.pairwise_append]
    refine ⟨hpw, by simp, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp ha
    rw [hb]; exact (hbd e' he').2
  refine ⟨List.Pairwise.sublist (List.Sublist.map Prod.fst List.filter_sublist) hpair, fun e he => ?_⟩
  show c.next + 1 - window ≤ e.1 ∧ e.1 < c.next + 1
  simp only [push, List.mem_filter, List.mem_append, List.mem_singleton, decide_eq_true_eq] at he
  obtain ⟨he | he, hk⟩ := he
  · exact ⟨hk, by have := (hbd e he).2; omega⟩
  · subst he; exact ⟨hk, by simp⟩

theorem bounded_reopen (window : ℕ) (c : Crib α) : c.reopen.Bounded window := by
  simp [Bounded, reopen]

/-- **A bounded crib holds at most `window` cells.** -/
theorem length_le {window : ℕ} {c : Crib α} (hc : c.Bounded window) : c.entries.length ≤ window := by
  obtain ⟨hpw, hbd⟩ := hc
  have hnd : (c.entries.map Prod.fst).Nodup := hpw.imp (fun h => ne_of_lt h)
  have hsub : (c.entries.map Prod.fst).toFinset ⊆ Finset.Ico (c.next - window) c.next := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact Finset.mem_Ico.mpr (hbd e he)
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map, Nat.card_Ico] at this
  omega

end Crib

variable {V α : Type*}

/-- `observe_cell_continuing` from the deposited successor on, on clones: the precision event (`event`), the
read-only view, the shared ingest, the crib's push and, at carry-out, the close and the crib's reopening. -/
def observeCell (L : Laws Θ A X) (population window : ℕ) (event : Bool) (carryOut : Option (Option Encl))
    (view : Resident Θ A X M → V) (x : α) (r : Resident Θ A X M) (c : Crib α) :
    Option (Resident Θ A X M × Crib α × V) :=
  (if event then publishPrecision L r else some r).bind fun r₁ =>
    (ingestCell population r₁).bind fun r₂ =>
      match carryOut with
      | none => some (r₂, c.push window x, view r₁)
      | some release => (closeAeon release r₂).map fun p => (p.1, (c.push window x).reopen, view r₁)

/-- The public step: the clones are committed only on success, and the view is released only inside a success. -/
def observeCellPublic (L : Laws Θ A X) (population window : ℕ) (event : Bool) (carryOut : Option (Option Encl))
    (view : Resident Θ A X M → V) (x : α) (r : Resident Θ A X M) (c : Crib α) :
    Resident Θ A X M × Crib α × Option V :=
  match observeCell L population window event carryOut view x r c with
  | some (r', c', v) => (r', c', some v)
  | none => (r, c, none)

/-- **A refused later ingest preserves the resident, the crib and the view.** -/
theorem observeCellPublic_ingest_refused {L : Laws Θ A X} {population window : ℕ} {event : Bool}
    {carryOut : Option (Option Encl)} {view : Resident Θ A X M → V} {x : α} {r r₁ : Resident Θ A X M} {c : Crib α}
    (h₁ : (if event then publishPrecision L r else some r) = some r₁) (h : ingestCell population r₁ = none) :
    observeCellPublic L population window event carryOut view x r c = (r, c, none) := by
  unfold observeCellPublic observeCell
  rw [h₁]
  simp [h]

/-- **A refused close preserves the resident, the crib and the view.** -/
theorem observeCellPublic_close_refused {L : Laws Θ A X} {population window : ℕ} {event : Bool}
    {release : Option Encl} {view : Resident Θ A X M → V} {x : α} {r r₁ r₂ : Resident Θ A X M} {c : Crib α}
    (h₁ : (if event then publishPrecision L r else some r) = some r₁) (h₂ : ingestCell population r₁ = some r₂)
    (h : closeAeon release r₂ = none) :
    observeCellPublic L population window event (some release) view x r c = (r, c, none) := by
  unfold observeCellPublic observeCell
  rw [h₁]
  simp [h₂, h]

/-- **Every crib the public step returns is bounded**, when the crib it was given is. -/
theorem observeCellPublic_bounded {L : Laws Θ A X} {population window : ℕ} {event : Bool}
    {carryOut : Option (Option Encl)} {view : Resident Θ A X M → V} {x : α} {r : Resident Θ A X M} {c : Crib α}
    (hc : c.Bounded window) :
    (observeCellPublic L population window event carryOut view x r c).2.1.Bounded window := by
  unfold observeCellPublic
  cases h : observeCell L population window event carryOut view x r c with
  | none => exact hc
  | some p =>
      obtain ⟨r', c', v⟩ := p
      simp only
      unfold observeCell at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨r₁, -, r₂, -, h⟩ := h
      cases carryOut with
      | none => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]; exact Crib.bounded_push hc x
      | some release =>
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨p, -, -, hc', -⟩ := h
          rw [← hc']; exact Crib.bounded_reopen _ _

/-! ## 7. The partition survives a cold restore (box 6) -/

/-- The saved balance (`write_balance`): the counts and the widening, then the enclosures, each possibly absent. -/
structure Saved where
  exchanges : ℕ
  depositions : ℕ
  publications : ℕ
  arrivals : ℕ
  cells : ℕ
  widening : ℚ
  exchange : Option Encl
  deposition : Option Encl
  deposited : Option Encl
  published : Option Encl
  opening : Option Encl
  closing : Option Encl
  arrived : Option Encl

def save (b : Balance) : Saved :=
  ⟨b.exchanges, b.depositions, b.publications, b.arrivals, b.cells, b.widening, some b.exchange, some b.deposition,
    some b.deposited, some b.published, b.opening, b.closing, some b.arrived⟩

/-- `read_balance`: each subtotal must be present, and the deposited and published subtotals must add to the
inclusive deposition. -/
def restore (s : Saved) : Option Balance :=
  match s.exchange, s.deposition, s.deposited, s.published, s.arrived with
  | some ex, some dep, some dd, some pb, some ar =>
      if dd.plus pb = dep then
        some ⟨ex, dep, dd, pb, s.opening, s.closing, s.widening, s.exchanges, s.depositions, s.publications,
          s.arrivals, s.cells, ar⟩
      else none
  | _, _, _, _, _ => none

/-- **Every restored balance is partitioned.** -/
theorem restore_partitioned {s : Saved} {b : Balance} (h : restore s = some b) : b.Partitioned := by
  unfold restore at h
  split at h
  · split_ifs at h with hp
    cases h
    exact hp.symm
  · cases h

/-- **A partitioned balance restores to itself.** -/
theorem restore_save {b : Balance} (hb : b.Partitioned) : restore (save b) = some b := by
  simp [restore, save, hb.symm]

/-- **The partition and its telescoping survive a close and a cold restore**: both aeons of a close, saved, restore
to themselves with the invariant. -/
theorem inv_restore_save {b : Balance} (hb : b.Inv) :
    restore (save b.close.1) = some b.close.1 ∧ restore (save b.close.2) = some b.close.2 ∧
      b.close.1.Inv ∧ b.close.2.Inv :=
  ⟨restore_save (inv_close hb).1.1, restore_save (inv_close hb).2.1, inv_close hb⟩

/-- **The reader checks the partition and not the telescoping**: a saved balance with no step and a nonzero exchange
is restored. -/
theorem restore_accepts_untelescoped :
    ∃ s b, restore s = some b ∧ b.Partitioned ∧ ¬ b.Telescopes := by
  have hz : Encl.zero.plus Encl.zero = Encl.zero := by ext <;> simp
  refine ⟨⟨0, 0, 0, 0, 0, 0, some ⟨1, 1⟩, some Encl.zero, some Encl.zero, some Encl.zero, none, none,
    some Encl.zero⟩, ⟨⟨1, 1⟩, Encl.zero, Encl.zero, Encl.zero, none, none, 0, 0, 0, 0, 0, 0, Encl.zero⟩, ?_, ?_, ?_⟩
  · simp only [restore, hz, if_true]
  · show Encl.zero = Encl.zero.plus Encl.zero
    rw [hz]
  · rintro ⟨h0, -⟩
    have h1 := congrArg Encl.lower (h0 (by simp [steps])).1
    simp at h1

end Holonics.HNN.ReceivingPrecision
