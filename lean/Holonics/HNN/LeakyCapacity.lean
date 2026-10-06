import Holonics.HNN.IndexedOpen
import Holonics.HNN.RangedMoment
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Size

/-!
# The retained leaky coordinates have a count-dependent finite box

This joins `IndexedOpen.nearest` and `IndexedOpen.carried`, the actual retained
recurrence, to a cardinality read. It changes neither that recurrence nor the source
clock. Fixed opening metadata, declared slots and `n` injected data are the operands.
Every coordinate starts at zero, a tick cannot increase a nonnegative integer at
`0 ≤ ρ ≤ 1`, and each injected datum contributes at most `U = 2^unit`. Thus every
coordinate lies in `[0,n*U]`. The factor for `S` slots is `(n*U+1)^S`.

This is a bound at each count, not an amplitude bound uniform over all counts. A
zero-tick source with repeated drives has arbitrarily large coordinates even at a
strictly dissipative modulus. Opening metadata is fixed in this conditional count;
varying learned constitutions are not counted by it. Formal checking is pending.
-/

noncomputable section

namespace Holonics.HNN.LeakyCapacity

open IndexedOpen

/-- Nearest rounding preserves a nonnegative integer upper bound. -/
theorem nearest_bounds {y : ℚ} {U : ℤ} (h0 : 0 ≤ y) (hU : y ≤ (U : ℚ)) :
    0 ≤ nearest y ∧ nearest y ≤ U := by
  unfold nearest
  constructor
  · apply Int.floor_nonneg.mpr
    linarith
  · apply Int.floor_le_iff.mpr
    linarith

/-- The actual rounded transport cannot increase a nonnegative integer coordinate. -/
theorem tick_nonexpansive {ρ : ℚ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {v : ℤ} (hv : 0 ≤ v) :
    0 ≤ nearest (ρ * v) ∧ nearest (ρ * v) ≤ v := by
  have hvq : (0 : ℚ) ≤ v := by exact_mod_cast hv
  exact nearest_bounds (mul_nonneg h0 hvq) (by nlinarith)

/-- A datum adds at most one opened lattice unit, including a rounded section entry. -/
def admittedDrive (U : ℕ) : LeakyStep → Prop
  | .tick => True
  | .unit z => 0 ≤ z ∧ z ≤ (U : ℤ)
  | .entry y => 0 ≤ y ∧ y ≤ (U : ℚ)

/-- Number of injected data, independent of the number of transport ticks. -/
def injections : List LeakyStep → ℕ
  | [] => 0
  | .tick :: l => injections l
  | _ :: l => injections l + 1

/-- Reuses the retained recurrence; no source list is part of the retained carrier. -/
theorem carried_bound (U : ℕ) {ρ : ℚ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (l : List LeakyStep) :
    (∀ st ∈ l, admittedDrive U st) → ∀ (v : ℤ), 0 ≤ v →
      0 ≤ carried ρ v l ∧ carried ρ v l ≤ v + (injections l : ℤ) * U := by
  induction l with
  | nil => intro _ v hv; simpa [carried, injections] using hv
  | cons st l ih =>
    intro had v hv
    have hh := had st (by simp)
    have ht : ∀ st ∈ l, admittedDrive U st := fun st hs => had st (by simp [hs])
    cases st with
    | tick =>
      have hn := tick_nonexpansive h0 h1 hv
      have hi := ih ht (nearest (ρ * v)) hn.1
      simp only [carried, injections]
      exact ⟨hi.1, hi.2.trans (add_le_add hn.2 le_rfl)⟩
    | unit z =>
      change 0 ≤ z ∧ z ≤ (U : ℤ) at hh
      have hi := ih ht (v + z) (by omega)
      simp only [carried, injections]
      refine ⟨hi.1, ?_⟩
      calc carried ρ (v + z) l ≤ v + z + (injections l : ℤ) * U := hi.2
        _ ≤ v + U + (injections l : ℤ) * U := by omega
        _ = v + ((injections l + 1 : ℕ) : ℤ) * U := by push_cast; ring
    | entry y =>
      change 0 ≤ y ∧ y ≤ (U : ℚ) at hh
      have hn := nearest_bounds (U := (U : ℤ)) hh.1 (by
        simpa only [Int.cast_natCast] using hh.2)
      have hi := ih ht (v + nearest y) (by omega)
      simp only [carried, injections]
      refine ⟨hi.1, ?_⟩
      calc carried ρ (v + nearest y) l ≤ v + nearest y + (injections l : ℤ) * U := hi.2
        _ ≤ v + U + (injections l : ℤ) * U := by omega
        _ = v + ((injections l + 1 : ℕ) : ℤ) * U := by push_cast; ring

theorem empty_carried_bound (U : ℕ) {ρ : ℚ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (l : List LeakyStep) (had : ∀ st ∈ l, admittedDrive U st) :
    0 ≤ carried ρ 0 l ∧ carried ρ 0 l ≤ (injections l : ℤ) * U := by
  simpa using carried_bound U h0 h1 l had 0 (by rfl)

/-- With no tick, drives add exactly; a passive transport does not bound this source. -/
theorem carried_replicate_unit (ρ : ℚ) (U v : ℤ) (n : ℕ) :
    carried ρ v (List.replicate n (.unit U)) = v + (n : ℤ) * U := by
  induction n generalizing v with
  | zero => simp [carried]
  | succ n ih =>
      simp only [List.replicate_succ, carried, ih]
      push_cast
      ring

/-- A finite bound uniform over the admitted counts needs a drive/clock condition. -/
theorem no_uniform_bound_without_ticks (ρ : ℚ) (U : ℕ) (hU : 0 < U) :
    ¬ ∃ B : ℤ, ∀ n : ℕ, carried ρ 0 (List.replicate n (.unit U)) ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have := hB n
  rw [carried_replicate_unit] at this
  simp only [zero_add] at this
  have hU' : (1 : ℤ) ≤ U := by exact_mod_cast (show 1 ≤ U from hU)
  have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
  nlinarith

section Box

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Canonical sparse maps inject into this full declared coordinate box; absent means zero. -/
def coordinateBox (U : ι → ℕ) (n : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc 0 ((n * U i : ℕ) : ℤ)

theorem coordinate_mem_box (U : ι → ℕ) (n : ℕ) (v : ι → ℤ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ ((n * U i : ℕ) : ℤ)) :
    v ∈ coordinateBox U n := by
  exact Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr (hv i)

/-- The exact product count at fixed lattice metadata and injected count. -/
theorem card_coordinateBox (U : ι → ℕ) (n : ℕ) :
    (coordinateBox U n).card = ∏ i : ι, (n * U i + 1) := by
  simp only [coordinateBox, Fintype.card_piFinset, Int.card_Icc, sub_zero]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show ((n * U i : ℕ) : ℤ) + 1 = ((n * U i + 1 : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_natCast]

/-- The ring factor, with `S = d*A + |offsets|*d*A^2`. -/
theorem card_ring_box (S U n : ℕ) :
    (coordinateBox (fun _ : Fin S => U) n).card = (n * U + 1) ^ S := by
  simp [card_coordinateBox]

/-- Histogram capacity and the retained-coordinate capacity are separate factors. -/
theorem joint_card_bound {X : Type*} (C : Finset X) {N : ℕ} (hC : C.card ≤ N)
    (U : ι → ℕ) (n : ℕ) :
    (C ×ˢ coordinateBox U n).card ≤ N * ∏ i : ι, (n * U i + 1) := by
  rw [Finset.card_product, card_coordinateBox]
  exact Nat.mul_le_mul_right _ hC

/-- The additional factor preserves the existing persistent-crossover argument. -/
theorem coordinate_factor_logConcave (n₀ : ℕ) (U : ι → ℕ) :
    Moment.LogConcaveFrom n₀ fun n => ∏ i : ι, (n * U i + 1) := by
  classical
  have h := Moment.LogConcaveFrom.prod (Finset.univ : Finset ι)
    (fun i n => U i * n + 1) (fun i _ => Moment.logConcave_linear n₀ (U i) 1)
  simpa [Nat.mul_comm] using h

theorem coordinate_factor_pos (U : ι → ℕ) (n : ℕ) :
    0 < ∏ i : ι, (n * U i + 1) := by
  exact Finset.prod_pos fun i _ => by omega

/-- The reader's word-sized bit-length formula, without constructing `n*2^u`. -/
def coordinateBitWidth (n u : ℕ) : ℕ := if n = 0 then 0 else n.size + u

/-- The runtime integer bit reading bounds each coordinate factor, including the empty opening. -/
theorem coordinate_factor_le_pow_bits (n u : ℕ) :
    n * 2 ^ u + 1 ≤ 2 ^ coordinateBitWidth n u := by
  by_cases hn : n = 0
  · simp [hn, coordinateBitWidth]
  · rw [coordinateBitWidth, if_neg hn, pow_add]
    have h := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self n) (by positivity : 0 < 2 ^ u)
    omega

theorem product_le_pow_bits (s : Finset ι) (u : ι → ℕ) (n : ℕ) :
    (∏ i ∈ s, (n * 2 ^ u i + 1)) ≤ 2 ^ (∑ i ∈ s, coordinateBitWidth n (u i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
    exact Nat.mul_le_mul (coordinate_factor_le_pow_bits n (u i)) ih

/-- `(N-1).size` is the source reader's exact ceiling-log wire for a positive count. -/
theorem cardinal_le_pow_ceiling_size (N : ℕ) : N ≤ 2 ^ (N - 1).size := by
  cases N with
  | zero => simp
  | succ N => simpa using Nat.succ_le_of_lt (Nat.lt_size_self N)

/-- The complete retained carrier is bounded by the actual `state_bits_upper` reading. -/
theorem joint_card_bit_bound {X : Type*} (C : Finset X) {N : ℕ} (hC : C.card ≤ N)
    (u : ι → ℕ) (n : ℕ) :
    (C ×ˢ coordinateBox (fun i => 2 ^ u i) n).card ≤
      2 ^ ((N - 1).size + ∑ i : ι, coordinateBitWidth n (u i)) := by
  rw [Finset.card_product, card_coordinateBox, pow_add]
  exact Nat.mul_le_mul (hC.trans (cardinal_le_pow_ceiling_size N))
    (product_le_pow_bits Finset.univ u n)

end Box

section Audit
#print axioms tick_nonexpansive
#print axioms empty_carried_bound
#print axioms no_uniform_bound_without_ticks
#print axioms card_coordinateBox
#print axioms joint_card_bound
#print axioms coordinate_factor_logConcave
#print axioms coordinate_factor_le_pow_bits
#print axioms joint_card_bit_bound
end Audit

end Holonics.HNN.LeakyCapacity
