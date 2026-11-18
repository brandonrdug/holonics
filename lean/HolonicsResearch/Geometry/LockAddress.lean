import HolonicsResearch.Compression.SternBrocotCode
import Mathlib

/-!
# The lock address: a run word is a product of convergents, its node the mediant of two of them

#410 (box "The lock address"): the retired Rust `LockAddress` (held at `d5ed4adc1`,
`crates/holonics/src/navigator/address.rs`) stored the Stern–Brocot path of a pair's rate ratio
`p/q` run-length, the runs `R^(a₀) L^(a₁) R^(a₂) …` being the partial quotients, read its ratio as
the mediant of the two columns of the word's matrix, priced the lock by its denominator `q` (the
turns before the pair returns to its joint phase), and placed a lock between neighbours to a
declared tolerance. `Geometry/Farey` proved the continued-fraction product `cfProd` carries the
convergents; `Compression/SternBrocotCode` proved a word's matrix carries `(1, 1)` to its node. This
file joins the two on the run word and states the cost, the tolerance and the lock's kernel.

[proved-standard; formal-checked] What is proved.

1. **A run is a power of one generator** (`rPow`, `lPow`, `wordMatrix_replicate_true`,
   `wordMatrix_replicate_false`, `wordMatrix_append`, `rPow_eq_sbRPower`): `k` letters `R` are
   `!![1, k; 0, 1]` and `k` letters `L` are `!![1, 0; k, 1]`, and words multiply as they
   concatenate.
2. **The run word is the continued-fraction product, up to the exchange** (`runLetters`,
   `runWord`, `runWord_succ`, `det_runWord`, `exchange_rPow_exchange`, `cfMatrix_eq`,
   `cfProd_eq_runWord`): with `X` the exchange, `cfMatrix t = Rᵗ X` and `X Rᵏ X = Lᵏ`, so the
   product of the first `n + 1` steps is the run word times `X` after an odd count of runs and the
   run word itself after an even count; the run word has determinant one.
3. **Its columns are consecutive convergents** (`runWord_convergents`): `h_n/k_n` and
   `h_(n+1)/k_(n+1)` of `[a₀; a₁, …, a_(n+1)]`, in the order the parity of the last run gives.
4. **Its node is their mediant** (`runWord_node`, `node_runLetters`, `hh_bump`, `kk_bump`):
   the word carries `(1, 1)` to `(h_(n+1) + h_n, k_(n+1) + k_n)`, which is the last convergent of
   `[a₀; a₁, …, a_(n+1) + 1]`: the Rust's rule that the last quotient is one longer than its run.
5. **The denominators grow on the positive chart** (`kk_pos`): with every quotient after the first
   at least one, every `k_n` is positive.
6. **The tolerance** (`mediant_gaps`, `lock_tolerance`, `abs_sub_convs_le_of_real`): a lock that
   is the mediant of two unimodular neighbours `h/k`, `h′/k′` stands at `1/(k(k + k′))` and
   `1/(k′(k + k′))` from them, and they stand `1/(kk′)` apart; for a real rate Mathlib's
   `|v − A_n/B_n| ≤ 1/(B_n B_(n+1))` is the same bound on its own convergents.
7. **The denominator is the horizon** (`lock_horizon`, `lock_horizon_least`): for `p/q` in lowest
   terms, `q ∣ t·p` exactly when `q ∣ t`, so the pair first returns to its joint phase after `q`
   turns.
8. **The lock's kernel, stationary and signed** (`lock_kernel`, `lock_kernel_stationary`,
   `lock_kernel_signed`): the pair with rates `u`, `v ≠ 0` locks at `(p, q)` (`q·u = p·v`, the
   zero-power direction of the Rust's `pair_lock`) exactly on the integer multiples of the
   primitive `(u/g, v/g)`, `g = gcd(u, v)`; a stationary first clock (`u = 0`) locks only at
   `p = 0`; rates of opposite sign lock only at ratios of opposite sign.

[agent-inferred] **Limits.** The Euclidean descent that builds the runs from `p/q` (the Rust's
`from_ratio`) is `Compression/SternBrocotCode.path`, read letter by letter; its run-length form is
not stated here. The cheapest lock strictly between neighbours is
`Geometry/PairResonance.between_neighbours_costs_at_least_the_mediant`. The box's "signed kernel"
is read as the lock relation `q·u = p·v` over signed rates; if it meant a kernel of a signed chart of
the tree (words in `SL(2, ℤ)` with negative entries), that is not stated.

The computational object is the helical pair interaction: a lock is the pair's commensurate turn,
its address the word of shears Euclid's division writes for the rate ratio, and its cost the
turns before the joint phase closes. Of the winding guide's six general objects this touches the
pair (the ratio of two rates and its lock), the helix (the turns before closure) and faces and
placement (a lock placed between neighbours to a tolerance); the cell holonomy, tube and tower
thread stay attached.

Consumers: the atlas rows of the lock address and of `Geometry/Farey`; `Aeon`'s near-return grains,
which read a rate's convergents.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.LockAddress

open Matrix Holonics.Geometry.Farey Holonics.Mathematics.Towers
open Holonics.Compression.SternBrocotCode

/-! ## 1. Runs are powers of one generator -/

/-- [definition] `k` turns `R`: `!![1, k; 0, 1]`. -/
def rPow (k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (k : ℤ); 0, 1]

/-- [definition] `k` turns `L`: `!![1, 0; k, 1]`. -/
def lPow (k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; (k : ℤ), 1]

/-- [proved-standard; formal-checked] `rPow` is `Farey.sbRPower`. -/
theorem rPow_eq_sbRPower (k : ℕ) : rPow k = sbRPower k := (sbRPower_eq k).symm

/-- [proved-standard; formal-checked] Words multiply as they concatenate. -/
theorem wordMatrix_append (w v : List Bool) : wordMatrix (w ++ v) = wordMatrix w * wordMatrix v := by
  induction w with
  | nil => simp [wordMatrix]
  | cons l w ih => rw [List.cons_append, wordMatrix, wordMatrix, ih, Matrix.mul_assoc]

/-- [proved-standard; formal-checked] A run of `R` is `rPow`. -/
theorem wordMatrix_replicate_true (k : ℕ) : wordMatrix (List.replicate k true) = rPow k := by
  induction k with
  | zero =>
    ext i j; fin_cases i <;> fin_cases j <;> simp [wordMatrix, rPow]
  | succ k ih =>
    rw [List.replicate_succ, wordMatrix, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [letter, rPow, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] A run of `L` is `lPow`. -/
theorem wordMatrix_replicate_false (k : ℕ) : wordMatrix (List.replicate k false) = lPow k := by
  induction k with
  | zero =>
    ext i j; fin_cases i <;> fin_cases j <;> simp [wordMatrix, lPow]
  | succ k ih =>
    rw [List.replicate_succ, wordMatrix, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [letter, lPow, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-! ## 2. The run word -/

/-- [definition] The turn of run `i`: `R` on the even runs, `L` on the odd. -/
def runTurn (i : ℕ) : Bool := i % 2 == 0

/-- [definition] **The letters of the first `n + 1` runs** `R^(a₀) L^(a₁) R^(a₂) …`. -/
def runLetters (a : ℕ → ℕ) : ℕ → List Bool
  | 0 => List.replicate (a 0) true
  | n + 1 => runLetters a n ++ List.replicate (a (n + 1)) (runTurn (n + 1))

/-- [definition] **The run word's matrix.** -/
def runWord (a : ℕ → ℕ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := wordMatrix (runLetters a n)

/-- [definition] One run's matrix. -/
def runPow (i k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := if i % 2 = 0 then rPow k else lPow k

variable (a : ℕ → ℕ)

/-- [proved-standard; formal-checked] One more run multiplies by its power, one product a run. -/
theorem runWord_succ (n : ℕ) : runWord a (n + 1) = runWord a n * runPow (n + 1) (a (n + 1)) := by
  rw [runWord, runLetters, wordMatrix_append, ← runWord, runPow, runTurn]
  by_cases h : (n + 1) % 2 = 0
  · simp only [h, beq_self_eq_true, if_true, wordMatrix_replicate_true]
  · have : ((n + 1) % 2 == 0) = false := by simpa using h
    simp only [this, h, if_false, wordMatrix_replicate_false]

/-- [proved-standard; formal-checked] The run word is unimodular. -/
theorem det_runWord (n : ℕ) : (runWord a n).det = 1 := det_wordMatrix _

/-- [proved-standard; formal-checked] **The exchange turns `R` into `L`**: `X Rᵏ X = Lᵏ`. -/
theorem exchange_rPow_exchange (k : ℕ) : sbExchange * rPow k * sbExchange = lPow k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sbExchange, rPow, lPow, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] `cfMatrix t = Rᵗ X`. -/
theorem cfMatrix_eq (k : ℕ) : cfMatrix (k : ℤ) = rPow k * sbExchange := by
  rw [theNaturalStepIsAPowerTimesTheExchange, rPow_eq_sbRPower]

/-- [proved-standard; formal-checked] The exchange is its own inverse. -/
theorem exchange_sq : sbExchange * sbExchange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sbExchange, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **The run word is the continued-fraction product, up to the
exchange**: `cfProd n = runWord n · X` after an odd count of runs, `runWord n` after an even one. -/
theorem cfProd_eq_runWord (n : ℕ) :
    cfProd (fun i => (a i : ℤ)) n = runWord a n * (if n % 2 = 0 then sbExchange else 1) := by
  induction n with
  | zero =>
    simp only [cfProd, Nat.zero_mod, if_true, runWord, runLetters, wordMatrix_replicate_true]
    exact cfMatrix_eq (a 0)
  | succ n ih =>
    change cfProd (fun i => (a i : ℤ)) n * cfMatrix (a (n + 1) : ℤ) = _
    rw [ih, cfMatrix_eq, runWord_succ, runPow]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h1 : (n + 1) % 2 = 1 := by omega
      simp only [h, h1, if_true, one_ne_zero, if_false, Matrix.mul_one]
      rw [← exchange_rPow_exchange, Matrix.mul_assoc, Matrix.mul_assoc]
    · have h1 : (n + 1) % 2 = 0 := by omega
      simp only [h, h1, if_true, one_ne_zero, if_false, Matrix.mul_one]
      rw [Matrix.mul_assoc]

/-- [proved-standard; formal-checked] **The run word's columns are consecutive convergents**:
after an even count of runs they are `(h_(n+1), k_(n+1))` then `(h_n, k_n)`, after an odd count
the other way round. -/
theorem runWord_convergents (n : ℕ) :
    runWord a (n + 1) =
      if (n + 1) % 2 = 0 then
        !![hh (fun i => (a i : ℤ)) n, hh (fun i => (a i : ℤ)) (n + 1);
          kk (fun i => (a i : ℤ)) n, kk (fun i => (a i : ℤ)) (n + 1)]
      else
        !![hh (fun i => (a i : ℤ)) (n + 1), hh (fun i => (a i : ℤ)) n;
          kk (fun i => (a i : ℤ)) (n + 1), kk (fun i => (a i : ℤ)) n] := by
  have hc := theProductCarriesTheConvergents (fun i => (a i : ℤ)) n
  rw [cfProd_eq_runWord] at hc
  by_cases h : (n + 1) % 2 = 0
  · rw [if_pos h] at hc ⊢
    have : runWord a (n + 1) = runWord a (n + 1) * sbExchange * sbExchange := by
      rw [Matrix.mul_assoc, exchange_sq, Matrix.mul_one]
    rw [this, hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sbExchange, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [if_neg h, Matrix.mul_one] at hc
    rw [if_neg h, hc]

/-- [proved-standard; formal-checked] **The run word carries `(1, 1)` to the mediant of its two
convergents.** -/
theorem runWord_node (n : ℕ) :
    runWord a (n + 1) *ᵥ ![1, 1] =
      ![hh (fun i => (a i : ℤ)) (n + 1) + hh (fun i => (a i : ℤ)) n,
        kk (fun i => (a i : ℤ)) (n + 1) + kk (fun i => (a i : ℤ)) n] := by
  rw [runWord_convergents]
  split_ifs <;>
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- [proved-standard; formal-checked] **The node of the run letters is that mediant**
(`Compression/SternBrocotCode.wordMatrix_mulVec`). -/
theorem node_runLetters (n : ℕ) :
    ((node (runLetters a (n + 1))).1 : ℤ) =
        hh (fun i => (a i : ℤ)) (n + 1) + hh (fun i => (a i : ℤ)) n ∧
      ((node (runLetters a (n + 1))).2 : ℤ) =
        kk (fun i => (a i : ℤ)) (n + 1) + kk (fun i => (a i : ℤ)) n := by
  have h1 := wordMatrix_mulVec (runLetters a (n + 1))
  have h2 := runWord_node a n
  rw [runWord] at h2
  rw [h1] at h2
  exact ⟨by simpa using congrFun h2 0, by simpa using congrFun h2 1⟩

/-! ## 3. The last quotient is one longer than its run -/

section Bump

variable (b : ℕ → ℤ)

/-- [proved-standard; formal-checked] The convergents read only the quotients up to their index. -/
theorem hh_congr {c : ℕ → ℤ} (n : ℕ) (hbc : ∀ i ≤ n, b i = c i) :
    hh b n = hh c n ∧ kk b n = kk c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih, hbc with
    | 0, _, hbc => simp [hh, kk, hbc 0 le_rfl]
    | 1, _, hbc => simp [hh, kk, hbc 0 (by norm_num), hbc 1 le_rfl]
    | m + 2, ih, hbc =>
      have h1 := ih (m + 1) (by omega) fun i hi => hbc i (by omega)
      have h0 := ih m (by omega) fun i hi => hbc i (by omega)
      simp only [hh, kk, hbc (m + 2) le_rfl, h1.1, h1.2, h0.1, h0.2, and_self]

/-- [definition] The quotients with the last one, at `n + 1`, made one longer. -/
def bump (n : ℕ) : ℕ → ℤ := Function.update b (n + 1) (b (n + 1) + 1)

/-- [proved-standard; formal-checked] **The node is the last convergent of the bumped
quotients**: `h′_(n+1) = h_(n+1) + h_n`. -/
theorem hh_bump (n : ℕ) : hh (bump b n) (n + 1) = hh b (n + 1) + hh b n := by
  have hlow := hh_congr (bump b n) (c := b) n fun i hi => by
    simp [bump, Function.update, show i ≠ n + 1 by omega]
  cases n with
  | zero => simp [hh, bump, Function.update]; ring
  | succ m =>
    change bump b (m + 1) (m + 2) * hh (bump b (m + 1)) (m + 1) + hh (bump b (m + 1)) m = _
    have hm := hh_congr (bump b (m + 1)) (c := b) m fun i hi => by
      simp [bump, Function.update, show i ≠ m + 2 by omega]
    rw [hlow.1, hm.1]
    change _ = (b (m + 2) * hh b (m + 1) + hh b m) + hh b (m + 1)
    simp [bump, Function.update]
    ring

/-- [proved-standard; formal-checked] And `k′_(n+1) = k_(n+1) + k_n`. -/
theorem kk_bump (n : ℕ) : kk (bump b n) (n + 1) = kk b (n + 1) + kk b n := by
  have hlow := hh_congr (bump b n) (c := b) n fun i hi => by
    simp [bump, Function.update, show i ≠ n + 1 by omega]
  cases n with
  | zero => simp [kk, bump, Function.update]
  | succ m =>
    change bump b (m + 1) (m + 2) * kk (bump b (m + 1)) (m + 1) + kk (bump b (m + 1)) m = _
    have hm := hh_congr (bump b (m + 1)) (c := b) m fun i hi => by
      simp [bump, Function.update, show i ≠ m + 2 by omega]
    rw [hlow.2, hm.2]
    change _ = (b (m + 2) * kk b (m + 1) + kk b m) + kk b (m + 1)
    simp [bump, Function.update]
    ring

/-- [proved-standard; formal-checked] **On the positive chart the denominators are positive**:
with every quotient after the first at least one, `0 < k_n`. -/
theorem kk_pos (hb : ∀ i, 1 ≤ i → 1 ≤ b i) (n : ℕ) : 0 < kk b n ∧ 0 < kk b (n + 1) := by
  induction n with
  | zero => exact ⟨by simp [kk], by simpa [kk] using (by linarith [hb 1 le_rfl] : (0 : ℤ) < b 1)⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    change 0 < b (n + 2) * kk b (n + 1) + kk b n
    have := hb (n + 2) (by omega)
    nlinarith [ih.1, ih.2]

end Bump

/-! ## 4. The tolerance -/

/-- [proved-standard; formal-checked] **A mediant of unimodular neighbours stands at
`1/(k(k + k′))` and `1/(k′(k + k′))` from them, and they stand `1/(kk′)` apart.** -/
theorem mediant_gaps {h k h' k' : ℤ} (hk : 0 < k) (hk' : 0 < k')
    (hdet : h * k' - h' * k = 1 ∨ h * k' - h' * k = -1) :
    |((h + h' : ℤ) : ℚ) / ((k + k' : ℤ) : ℚ) - (h : ℚ) / k| = 1 / ((k : ℚ) * (k + k')) ∧
      |((h + h' : ℤ) : ℚ) / ((k + k' : ℤ) : ℚ) - (h' : ℚ) / k'| = 1 / ((k' : ℚ) * (k + k')) ∧
      |(h : ℚ) / k - (h' : ℚ) / k'| = 1 / ((k : ℚ) * k') := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hkq' : (0 : ℚ) < k' := by exact_mod_cast hk'
  have hs : (0 : ℚ) < k + k' := by linarith
  have hD : ((h * k' - h' * k : ℤ) : ℚ) = 1 ∨ ((h * k' - h' * k : ℤ) : ℚ) = -1 := by
    rcases hdet with h1 | h1 <;> [left; right] <;> exact_mod_cast h1
  push_cast at hD ⊢
  have n1 := hkq.ne'
  have n2 := hkq'.ne'
  have n3 := hs.ne'
  have e1 : ((h : ℚ) + h') / ((k : ℚ) + k') - (h : ℚ) / k =
      -((h : ℚ) * k' - h' * k) / ((k : ℚ) * (k + k')) := by
    field_simp; ring
  have e2 : ((h : ℚ) + h') / ((k : ℚ) + k') - (h' : ℚ) / k' =
      ((h : ℚ) * k' - h' * k) / ((k' : ℚ) * (k + k')) := by
    field_simp; ring
  have e3 : (h : ℚ) / k - (h' : ℚ) / k' = ((h : ℚ) * k' - h' * k) / ((k : ℚ) * k') := by
    field_simp
  rw [e1, e2, e3]
  have p1 : (0 : ℚ) < k * (k + k') := by positivity
  have p2 : (0 : ℚ) < k' * (k + k') := by positivity
  have p3 : (0 : ℚ) < k * k' := by positivity
  rcases hD with hD | hD <;> rw [hD] <;>
    simp [abs_div, abs_of_pos p1, abs_of_pos p2, abs_of_pos p3, abs_of_pos hkq, abs_of_pos hkq',
      abs_of_pos hs]

/-- [proved-standard; formal-checked] **The lock placed by a run word stands at
`1/(k_(n+1)(k_(n+1) + k_n))` from its last convergent** on the positive chart. -/
theorem lock_tolerance (ha : ∀ i, 1 ≤ i → 1 ≤ a i) (n : ℕ) :
    |(((hh (fun i => (a i : ℤ)) (n + 1) + hh (fun i => (a i : ℤ)) n : ℤ) : ℚ) /
        ((kk (fun i => (a i : ℤ)) (n + 1) + kk (fun i => (a i : ℤ)) n : ℤ) : ℚ)) -
      (hh (fun i => (a i : ℤ)) (n + 1) : ℚ) / (kk (fun i => (a i : ℤ)) (n + 1) : ℚ)| =
      1 / ((kk (fun i => (a i : ℤ)) (n + 1) : ℚ) *
        (kk (fun i => (a i : ℤ)) (n + 1) + kk (fun i => (a i : ℤ)) n)) := by
  have hpos := kk_pos (fun i => (a i : ℤ)) (fun i hi => by exact_mod_cast ha i hi) n
  have hdet := theConvergentDeterminantAlternates (fun i => (a i : ℤ)) n
  have hd : hh (fun i => (a i : ℤ)) (n + 1) * kk (fun i => (a i : ℤ)) n -
        hh (fun i => (a i : ℤ)) n * kk (fun i => (a i : ℤ)) (n + 1) = 1 ∨
      hh (fun i => (a i : ℤ)) (n + 1) * kk (fun i => (a i : ℤ)) n -
        hh (fun i => (a i : ℤ)) n * kk (fun i => (a i : ℤ)) (n + 1) = -1 := by
    rw [hdet]
    rcases neg_one_pow_eq_or ℤ n with h | h <;> simp [h]
  exact (mediant_gaps hpos.2 hpos.1 hd).1

/-- [proved-standard; formal-checked] **For a real rate the convergents carry the same bound**
(Mathlib's `GenContFract.abs_sub_convs_le`). -/
theorem abs_sub_convs_le_of_real (v : ℝ) (n : ℕ)
    (hn : ¬(GenContFract.of v).TerminatedAt n) :
    |v - (GenContFract.of v).convs n| ≤
      1 / ((GenContFract.of v).dens n * (GenContFract.of v).dens (n + 1)) :=
  GenContFract.abs_sub_convs_le hn

/-! ## 5. The horizon and the kernel -/

/-- [proved-standard; formal-checked] **The denominator is the horizon**: for `p/q` in lowest
terms, `q ∣ t·p` exactly when `q ∣ t`. -/
theorem lock_horizon {p q : ℤ} (hpq : IsCoprime p q) (t : ℤ) : q ∣ t * p ↔ q ∣ t :=
  ⟨fun h => hpq.symm.dvd_of_dvd_mul_right h, fun h => dvd_mul_of_dvd_left h p⟩

/-- [proved-standard; formal-checked] **No earlier return**: a positive number of turns that closes
the joint phase is at least `q`. -/
theorem lock_horizon_least {p q : ℤ} (hpq : IsCoprime p q) {t : ℤ} (ht : 0 < t)
    (h : q ∣ t * p) : q ≤ t :=
  Int.le_of_dvd ht ((lock_horizon hpq t).mp h)

/-- [proved-standard; formal-checked] **The lock's kernel**: rates `u`, `v ≠ 0` lock at `(p, q)`,
`q·u = p·v`, exactly on the integer multiples of the primitive `(u/g, v/g)`, `g = gcd(u, v)`. -/
theorem lock_kernel {u v : ℤ} (hv : v ≠ 0) (p q : ℤ) :
    q * u = p * v ↔
      ∃ t : ℤ, p = t * (u / (Int.gcd u v : ℤ)) ∧ q = t * (v / (Int.gcd u v : ℤ)) := by
  set g : ℤ := (Int.gcd u v : ℤ) with hg
  have hgpos : 0 < Int.gcd u v := Int.gcd_pos_of_ne_zero_right u hv
  have hg0 : g ≠ 0 := by rw [hg]; exact_mod_cast hgpos.ne'
  obtain ⟨u', hu'⟩ : g ∣ u := by rw [hg]; exact Int.gcd_dvd_left u v
  obtain ⟨v', hv'⟩ : g ∣ v := by rw [hg]; exact Int.gcd_dvd_right u v
  have hu'' : u / g = u' := by rw [hu', Int.mul_ediv_cancel_left _ hg0]
  have hv'' : v / g = v' := by rw [hv', Int.mul_ediv_cancel_left _ hg0]
  have hcop : Int.gcd u' v' = 1 := by
    have := Int.gcd_div_gcd_div_gcd hgpos
    rwa [← hg, hu'', hv''] at this
  have hv'0 : v' ≠ 0 := by rintro rfl; simp at hv'; exact hv hv'
  rw [hu'', hv'']
  constructor
  · intro h
    have h' : q * u' = p * v' := by
      have : g * (q * u') = g * (p * v') := by rw [hu', hv'] at h; linear_combination h
      exact mul_left_cancel₀ hg0 this
    have hdvd : v' ∣ q * u' := ⟨p, by rw [h']; ring⟩
    have hcop' : IsCoprime v' u' := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hcop
    obtain ⟨t, ht⟩ := hcop'.dvd_of_dvd_mul_right hdvd
    refine ⟨t, ?_, by rw [ht]; ring⟩
    have : v' * p = v' * (t * u') := by rw [ht] at h'; linear_combination -h'
    exact mul_left_cancel₀ hv'0 this
  · rintro ⟨t, rfl, rfl⟩
    rw [hu', hv']
    ring

/-- [proved-standard; formal-checked] **A stationary first clock locks only at `p = 0`.** -/
theorem lock_kernel_stationary {v : ℤ} (hv : v ≠ 0) (p q : ℤ) : q * 0 = p * v ↔ p = 0 := by
  constructor
  · intro h
    rw [mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hv
  · rintro rfl; simp

/-- [proved-standard; formal-checked] **Rates of opposite sign lock only at ratios of opposite
sign**: `q·u = p·v`, `q ≠ 0`, `uv < 0` give `pq < 0`. -/
theorem lock_kernel_signed {u v p q : ℤ} (h : q * u = p * v) (hq : q ≠ 0) (huv : u * v < 0) :
    p * q < 0 := by
  have hv : v ≠ 0 := by rintro rfl; simp at huv
  have key : p * q * v ^ 2 = q ^ 2 * (u * v) := by linear_combination q * v * h.symm
  have hq2 : 0 < q ^ 2 := by positivity
  have hv2 : 0 < v ^ 2 := by positivity
  have : p * q * v ^ 2 < 0 := by rw [key]; exact mul_neg_of_pos_of_neg hq2 huv
  by_contra hc
  push Not at hc
  nlinarith

end Holonics.Geometry.LockAddress
