import Holonics.Aeon.Clock.Epoch
import Holonics.Computation.HolonicRecurrentEcology
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
# The sieve of Eratosthenes is a first-arrival epoch tower

[definition] Rebuild step 3 (#145), the null-cone record §5: the sieve is an epoch tower whose
survivors are first arrivals. It is stated over two existing owners.

- **The clocks** (`Aeon/Clock/Epoch`). The digit clock of base `p` ticks at the multiples of `p`
  inside an aeon of `N` micro-steps (`digitTicks p N`). At grain `k` the sieve's section is the
  union of the digit clocks of every prime `p ≤ k` (`sieveTicks`): the multiples of `p` are merged
  into `p`'s orbit, whose first tick is `p` itself (`prime_is_first_tick`).
- **The first arrival** (`Computation/HolonicRecurrentEcology.FirstArrival`). The multiplicative
  recurrence `peel m = m / minFac m` removes the least prime factor. Its first-arrival population
  at the unit receiver `{1}` at epoch `n` is exactly the occurrences with `n` prime factors counted
  with multiplicity, `Ω m = n` (`firstArrival_eq_cardFactors`). The primes are the first arrivals
  at epoch one (`firstArrival_one_iff_prime`).

[proved-derived; formal-checked] What is proved.

1. **The section is the union of the prime digit clocks** (`sieveTicks`, a definition): a
   micro-state is ticked at grain `k` exactly when a prime `p ≤ k` divides it (`mem_sieveTicks`).
2. **The tower is nested.** Raising the grain adds ticks (`sieveTicks_mono`) and removes survivors
   (`survivors_antitone`). The coarse grain's epochs are a function of the fine grain's epochs
   (`sieve_epoch_coarsens`, from `Epoch.epochOf_coarse`), and coarsening composes along three grains
   (`sieve_tower`, from `Epoch.coarsen_tower`).
3. **Eratosthenes.** The survivors in `[2, N]` after sieving by every prime `p ≤ √N` are exactly the
   primes in `(√N, N]` (`survivors_sqrt`). The proof reads the least prime factor: a composite `m`
   has `minFac m² ≤ m` (`Nat.minFac_sq_le_self`).
4. **The survivors are first arrivals.** They are exactly the epoch-one first arrivals of the
   multiplicative recurrence in `(√N, N]` (`survivors_sqrt_eq_firstArrivals`), and the primes up to
   `N` are the roots `p ≤ √N` (each the first tick of its own clock) together with the survivors
   (`primes_eq_roots_union_survivors`).

[counterexample; formal-checked] **The grain `√N` is load-bearing.** Sieving `[2, 25]` only by the
primes up to `4` leaves `25 = 5²`, which is not prime (`grain_below_sqrt_leaves_a_square`). A
control: at `N = 30`, `√30 = 5` and the survivors are `{7, 11, 13, 17, 19, 23, 29}`
(`survivors_thirty`).

[interpretation] The mean gap near `x` is `log x` (Kac's form of a density). That reading is
heuristic in Cramér's sense and is not a theorem here.

No `axiom`, no `sorry`.
-/

namespace Holonics.Landmarks.Sieve

open Finset
open Holonics.Aeon.Clock.Epoch
open Holonics.Computation.HolonicRecurrentEcology

/-! ## 1. The sieve's section at grain `k` -/

/-- [definition] The primes up to the grain `k`. -/
def primesUpTo (k : ℕ) : Finset ℕ := (range (k + 1)).filter Nat.Prime

theorem mem_primesUpTo {k p : ℕ} : p ∈ primesUpTo k ↔ p.Prime ∧ p ≤ k := by
  simp [primesUpTo, and_comm]

/-- [definition] **The sieve's section at grain `k`** over an aeon of `N` micro-steps: the ticks of
the digit clocks of every prime up to `k`. -/
def sieveTicks (k N : ℕ) : Finset ℕ := (primesUpTo k).biUnion fun p => digitTicks p N

/-- [proved-derived; formal-checked] A micro-state is ticked at grain `k` exactly when a prime up to
`k` divides it. -/
theorem mem_sieveTicks {k N m : ℕ} :
    m ∈ sieveTicks k N ↔ 0 < m ∧ m < N ∧ ∃ p, p.Prime ∧ p ≤ k ∧ p ∣ m := by
  simp only [sieveTicks, mem_biUnion, mem_primesUpTo, digitTicks, mem_filter, mem_Ioo]
  constructor
  · rintro ⟨p, ⟨hp, hpk⟩, ⟨h0, hN⟩, hd⟩
    exact ⟨h0, hN, p, hp, hpk, hd⟩
  · rintro ⟨h0, hN, p, hp, hpk, hd⟩
    exact ⟨p, ⟨hp, hpk⟩, ⟨h0, hN⟩, hd⟩

/-- [proved-derived; formal-checked] **A prime is the first tick of its own digit clock**: `p` is a
tick of `digitTicks p N` and every tick is at least `p`. -/
theorem prime_is_first_tick {p N : ℕ} (hp : p.Prime) (hpN : p < N) :
    p ∈ digitTicks p N ∧ ∀ m ∈ digitTicks p N, p ≤ m := by
  refine ⟨?_, ?_⟩
  · simp only [digitTicks, mem_filter, mem_Ioo]
    exact ⟨⟨hp.pos, hpN⟩, dvd_rfl⟩
  · intro m hm
    simp only [digitTicks, mem_filter, mem_Ioo] at hm
    exact Nat.le_of_dvd hm.1.1 hm.2

/-! ## 2. The tower is nested -/

/-- [proved-derived; formal-checked] **Raising the grain adds ticks**: the coarse section is a
sub-section of the fine one. -/
theorem sieveTicks_mono {k k' N : ℕ} (h : k ≤ k') : sieveTicks k N ⊆ sieveTicks k' N := by
  intro m hm
  rw [mem_sieveTicks] at hm ⊢
  obtain ⟨h0, hN, p, hp, hpk, hd⟩ := hm
  exact ⟨h0, hN, p, hp, hpk.trans h, hd⟩

/-- [proved-derived; formal-checked] **The coarse grain's epoch is a function of the fine grain's
epoch** (`Epoch.epochOf_coarse`). -/
theorem sieve_epoch_coarsens {k k' N : ℕ} (h : k ≤ k') (j : ℕ) :
    epochOf (sieveTicks k N) j =
      coarsen (sieveTicks k' N) (sieveTicks k N) (epochOf (sieveTicks k' N) j) :=
  epochOf_coarse (sieveTicks_mono h) j

/-- [proved-derived; formal-checked] **Coarsening composes along the tower** of three grains
(`Epoch.coarsen_tower`). -/
theorem sieve_tower {k k' k'' N : ℕ} (h₁ : k' ≤ k'') (h₂ : k ≤ k') (j : ℕ) :
    coarsen (sieveTicks k' N) (sieveTicks k N)
        (coarsen (sieveTicks k'' N) (sieveTicks k' N) (epochOf (sieveTicks k'' N) j)) =
      coarsen (sieveTicks k'' N) (sieveTicks k N) (epochOf (sieveTicks k'' N) j) :=
  coarsen_tower (sieveTicks_mono h₁) (sieveTicks_mono h₂) j

/-- [definition] **The survivors at grain `k`**: the micro-states of `[2, N)` that no prime digit
clock up to `k` ticks. -/
def survivors (k N : ℕ) : Finset ℕ := Ioo 1 N \ sieveTicks k N

theorem mem_survivors {k N m : ℕ} :
    m ∈ survivors k N ↔ 1 < m ∧ m < N ∧ ∀ p, p.Prime → p ≤ k → ¬ p ∣ m := by
  simp only [survivors, mem_sdiff, mem_Ioo, mem_sieveTicks]
  constructor
  · rintro ⟨⟨h1, hN⟩, hnot⟩
    refine ⟨h1, hN, fun p hp hpk hd => hnot ⟨by omega, hN, p, hp, hpk, hd⟩⟩
  · rintro ⟨h1, hN, hall⟩
    refine ⟨⟨h1, hN⟩, ?_⟩
    rintro ⟨-, -, p, hp, hpk, hd⟩
    exact hall p hp hpk hd

/-- [proved-derived; formal-checked] **The survivors shrink along the tower.** -/
theorem survivors_antitone {k k' N : ℕ} (h : k ≤ k') : survivors k' N ⊆ survivors k N :=
  sdiff_subset_sdiff subset_rfl (sieveTicks_mono h)

/-! ## 3. Eratosthenes: the survivors at grain `√N` are the primes above `√N` -/

/-- [proved-derived; formal-checked] **Eratosthenes.** The survivors in `[2, N]` after sieving by
every prime `p ≤ √N` are exactly the primes in `(√N, N]`. -/
theorem survivors_sqrt (N : ℕ) :
    survivors (Nat.sqrt N) (N + 1) = (Ioc (Nat.sqrt N) N).filter Nat.Prime := by
  ext m
  rw [mem_survivors, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨h1, hN, hall⟩
    have hmN : m ≤ N := by omega
    have hmin : Nat.sqrt N < m.minFac := by
      by_contra hle
      exact hall m.minFac (Nat.minFac_prime (by omega)) (not_lt.mp hle) (Nat.minFac_dvd m)
    have hprime : m.Prime := by
      by_contra hnp
      have hsq := Nat.minFac_sq_le_self (by omega : 0 < m) hnp
      have : m.minFac ≤ Nat.sqrt N := Nat.le_sqrt'.mpr (hsq.trans hmN)
      omega
    exact ⟨⟨lt_of_lt_of_le hmin (Nat.minFac_le (by omega)), hmN⟩, hprime⟩
  · rintro ⟨⟨hs, hmN⟩, hprime⟩
    refine ⟨hprime.one_lt, by omega, fun p hp hpk hd => ?_⟩
    rcases hprime.eq_one_or_self_of_dvd p hd with h | h
    · exact hp.one_lt.ne' h
    · omega

/-! ## 4. The survivors are first arrivals -/

/-- [definition] **The multiplicative recurrence**: remove the least prime factor. -/
def peel (m : ℕ) : ℕ := m / m.minFac

/-- [proved-derived; formal-checked] **The first-arrival epoch at the unit receiver is `Ω`.** An
occurrence first reaches `{1}` under `peel` at epoch `n` exactly when it is nonzero with `n` prime
factors counted with multiplicity. -/
theorem firstArrival_eq_cardFactors (n m : ℕ) :
    m ∈ FirstArrival.population peel {1} n ↔ m ≠ 0 ∧ ArithmeticFunction.cardFactors m = n := by
  rw [ArithmeticFunction.cardFactors_apply]
  induction n generalizing m with
  | zero =>
    simp only [FirstArrival.population, Set.mem_singleton_iff, List.length_eq_zero_iff,
      Nat.primeFactorsList_eq_nil]
    omega
  | succ n ih =>
    simp only [FirstArrival.population, Set.mem_sdiff, Set.mem_preimage, Set.mem_singleton_iff,
      ih]
    rcases m with _ | _ | k
    · simp [peel]
    · simp
    · have hpos : 0 < (k + 2).minFac := Nat.minFac_pos _
      have hle : (k + 2).minFac ≤ k + 2 := Nat.minFac_le (by omega)
      have hq : (k + 2) / (k + 2).minFac ≠ 0 := (Nat.div_pos hle hpos).ne'
      rw [Nat.primeFactorsList_add_two, List.length_cons]
      simp only [peel]
      generalize (k + 2) / (k + 2).minFac = q at hq ⊢
      constructor
      · rintro ⟨⟨-, hlen⟩, -⟩
        exact ⟨by omega, by omega⟩
      · rintro ⟨-, hlen⟩
        exact ⟨⟨hq, by omega⟩, by omega⟩

/-- [proved-derived; formal-checked] **The primes are the first arrivals at epoch one.** -/
theorem firstArrival_one_iff_prime (m : ℕ) :
    m ∈ FirstArrival.population peel {1} 1 ↔ m.Prime := by
  rw [firstArrival_eq_cardFactors, ArithmeticFunction.cardFactors_eq_one_iff_prime]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h.ne_zero, h⟩

/-- [proved-derived; formal-checked] **The survivors are first arrivals**: the survivors at grain
`√N` are exactly the epoch-one first arrivals of the multiplicative recurrence in `(√N, N]`. -/
theorem survivors_sqrt_eq_firstArrivals (N m : ℕ) :
    m ∈ survivors (Nat.sqrt N) (N + 1) ↔
      m ∈ Ioc (Nat.sqrt N) N ∧ m ∈ FirstArrival.population peel {1} 1 := by
  rw [survivors_sqrt, mem_filter, firstArrival_one_iff_prime]

/-- [proved-derived; formal-checked] **The primes up to `N` are the roots and the survivors**: the
primes `p ≤ √N` (each the first tick of its own clock) together with the survivors at grain
`√N`. -/
theorem primes_eq_roots_union_survivors (N : ℕ) :
    (Ioc 0 N).filter Nat.Prime = primesUpTo (Nat.sqrt N) ∪ survivors (Nat.sqrt N) (N + 1) := by
  rw [survivors_sqrt]
  ext m
  simp only [mem_filter, mem_Ioc, mem_union, mem_primesUpTo]
  constructor
  · rintro ⟨⟨h0, hmN⟩, hp⟩
    by_cases hs : m ≤ Nat.sqrt N
    · exact Or.inl ⟨hp, hs⟩
    · exact Or.inr ⟨⟨by omega, hmN⟩, hp⟩
  · rintro (⟨hp, hs⟩ | ⟨⟨hs, hmN⟩, hp⟩)
    · exact ⟨⟨hp.pos, hs.trans (Nat.sqrt_le_self N)⟩, hp⟩
    · exact ⟨⟨by omega, hmN⟩, hp⟩

/-! ## 5. The grain `√N` is load-bearing -/

/-- [counterexample; formal-checked] **Sieving below `√N` leaves a square.** In `[2, 25]`, the
primes up to `4` do not tick `25 = 5²`, which is not prime. -/
theorem grain_below_sqrt_leaves_a_square :
    25 ∈ survivors 4 26 ∧ ¬ (25 : ℕ).Prime ∧ Nat.sqrt 25 = 5 := by
  refine ⟨?_, by norm_num, by norm_num [Nat.sqrt_eq']⟩
  rw [mem_survivors]
  refine ⟨by norm_num, by norm_num, fun p hp hpk hd => ?_⟩
  interval_cases p <;> revert hp hd <;> decide

/-- [proved-derived; formal-checked] **A control**: at `N = 30`, `√30 = 5` and the survivors are the
primes `{7, 11, 13, 17, 19, 23, 29}`. -/
theorem survivors_thirty : survivors 5 31 = {7, 11, 13, 17, 19, 23, 29} := by
  have h5 : Nat.sqrt 30 = 5 := by
    exact (Nat.eq_sqrt.mpr (by norm_num)).symm
  rw [← h5, survivors_sqrt, h5]
  decide

section Audit
#print axioms mem_sieveTicks
#print axioms prime_is_first_tick
#print axioms sieve_epoch_coarsens
#print axioms sieve_tower
#print axioms survivors_antitone
#print axioms survivors_sqrt
#print axioms firstArrival_eq_cardFactors
#print axioms firstArrival_one_iff_prime
#print axioms survivors_sqrt_eq_firstArrivals
#print axioms primes_eq_roots_union_survivors
#print axioms grain_below_sqrt_leaves_a_square
#print axioms survivors_thirty
end Audit

end Holonics.Landmarks.Sieve
