import Mathlib.Data.Multiset.Lattice
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic

/-!
# A join reads which things arrived, and a sum with a carry reads how many

Atlas: `key.join-reads-support-a-carry-counts`. Record:
`research/records/2026-11-20_HODGE_ASKS_THAT_EACH_VARIETYS_FAILURE_GROUP_BE_FINITE_…` (§6.1).

Three readings of a collection of arrivals, each coarser than the one before. A word over moves that do not commute
reads their order (`Compression/FaithfulModes.commutator_and`). A word over moves that commute reads their counts
alone (`Compression/FaithfulModes.abelian_word_counts`). This module adds the third: a reading that joins, where
`a ⊔ a = a`, reads only which things arrived.

1. **A join reads the support** (`join_reads_support`): two collections of arrivals with the same set of things have
   the same join, whatever their counts. Any number of arrivals of one thing reads as one
   (`join_blind_to_repeat`).
2. **A sum reads the count** (`sum_reads_count`), and on a ring of period `m` it reads the count modulo `m`
   (`ring_sum_reads_count_mod`); the ring is back at rest just at the multiples of its period (`ring_sum_zero_iff`).
3. **A count is its carries and its residue** (`count_is_carries_and_residue`), and a second ring of period `r`
   that takes the first ring's carries holds the count modulo `m * r` (`two_rings_hold_the_product`).
4. **One arrival against two** (`join_cannot_count_sum_can`): the join reads them alike and the sum does not.

Limits. This is the algebra under a sentence, and no theorem of constraint satisfaction is stated: that local
consistency decides a finite constraint language just when it expresses no linear equations over a finite abelian
group (Barto and Kozik 2014), and that the general algorithm interleaves consistency with linear equations over
prime fields (Zhuk 2017), are named in the record from training. A detector that integrates and fires, the time
encoding of a band-limited signal by its spike times, and the generalized sampling expansion are not stated.
-/

namespace Holonics.Compression.JoinReadsSupport

/-! ## 1. A join reads the support -/

section Join

variable {α : Type*} [SemilatticeSup α] [OrderBot α]

/-- [proved-standard; formal-checked] **A join reads which things arrived**: two collections of arrivals with the
same set of things have the same join. -/
theorem join_reads_support [DecidableEq α] {s t : Multiset α} (h : s.toFinset = t.toFinset) :
    s.sup = t.sup := by
  have hd : s.dedup = t.dedup := by
    rw [← Multiset.toFinset_val, ← Multiset.toFinset_val, h]
  rw [← Multiset.sup_dedup s, ← Multiset.sup_dedup t, hd]

/-- [proved-standard; formal-checked] Any number of arrivals of one thing reads as one. -/
theorem join_blind_to_repeat (a : α) (n : ℕ) : (Multiset.replicate (n + 1) a).sup = a := by
  induction n with
  | zero => simp
  | succ k ih => rw [Multiset.replicate_succ, Multiset.sup_cons, ih, sup_idem]

end Join

/-! ## 2. A sum reads the count -/

/-- [proved-standard; formal-checked] A sum of unit arrivals is their count. -/
theorem sum_reads_count (n : ℕ) : (Multiset.replicate n (1 : ℕ)).sum = n := by
  rw [Multiset.sum_replicate, smul_eq_mul, mul_one]

/-- [proved-standard; formal-checked] **On a ring of period `m` a sum reads the count modulo `m`**: two counts of
unit arrivals read alike just when they are congruent. -/
theorem ring_sum_reads_count_mod (m n k : ℕ) :
    (Multiset.replicate n (1 : ZMod m)).sum = (Multiset.replicate k (1 : ZMod m)).sum ↔
      n ≡ k [MOD m] := by
  rw [Multiset.sum_replicate, Multiset.sum_replicate, nsmul_one, nsmul_one,
    ZMod.natCast_eq_natCast_iff]

/-- [proved-standard; formal-checked] The ring is back at rest just at the multiples of its period, where it
carries. -/
theorem ring_sum_zero_iff (m n : ℕ) : (Multiset.replicate n (1 : ZMod m)).sum = 0 ↔ m ∣ n := by
  rw [Multiset.sum_replicate, nsmul_one, ZMod.natCast_eq_zero_iff]

/-! ## 3. Carries and residue -/

/-- [proved-standard; formal-checked] **A count is its carries and its residue.** -/
theorem count_is_carries_and_residue (m n : ℕ) : m * (n / m) + n % m = n :=
  Nat.div_add_mod n m

/-- [proved-standard; formal-checked] **A slower ring that takes the carries extends the count**: the residue on a
ring of period `m` and the residue of its carries on a ring of period `r` hold the count modulo `m * r`. -/
theorem two_rings_hold_the_product (m r n : ℕ) : n % (m * r) = n % m + m * (n / m % r) :=
  Nat.mod_mul

/-! ## 4. One arrival against two -/

/-- [counterexample; formal-checked] **A join cannot count and a sum can**: one arrival and two arrivals of one
thing have the same join and different sums. -/
theorem join_cannot_count_sum_can {α : Type*} [SemilatticeSup α] [OrderBot α] (a : α) :
    (Multiset.replicate 2 a).sup = (Multiset.replicate 1 a).sup ∧
      (Multiset.replicate 2 (1 : ℕ)).sum ≠ (Multiset.replicate 1 (1 : ℕ)).sum := by
  refine ⟨?_, ?_⟩
  · rw [join_blind_to_repeat a 1, join_blind_to_repeat a 0]
  · rw [sum_reads_count, sum_reads_count]
    decide

end Holonics.Compression.JoinReadsSupport
