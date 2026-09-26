import Holonics.Mathematics.RatioSeriesTransport
import Holonics.Mathematics.RadixWindowReceiver
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Constraint identities are navigators: π and `e` through their partial navigators

[definition] π and `e` are **constraint identities**: the identity is the navigator and carries no
error. A digit window is a receiver face (`Mathematics/RadixWindowReceiver`), and error enters only
in how that face is attained. The **partial navigator** of a ratio series is the compiled block of
its ratio word (`Mathematics/RatioSeriesTransport`): a block `(n, α, β)` acts on the carried pair
(current term, partial sum), and its **convergents** are the partial sums it returns. The landmark
is the limit of those convergents.

[proved-derived; formal-checked] What is proved.

1. **Blocks compose associatively** (`compose_assoc`) with the empty block as unit (`unit_compose`,
   `compose_unit`), and compilation turns concatenation of ratio words into composition
   (`compile_append`, with `execute_append`): any bracketing of a word, in particular binary
   splitting, compiles to the same partial navigator.
2. **A partial navigator returns the convergent.** For terms with `t_(i+1) = r_i t_i`, the block of
   the first `n` ratios carries `(t_0, t_0)` to `(t_n, Σ_(i≤n) t_i)` (`partial_navigator_act`).
3. **`e`.** Ratios `1/(i+1)`, terms `1/i!` (`eTerm_succ`). Its convergents enclose `e` exactly:
   `s_n + 1/(n+1)! ≤ e ≤ s_n + (n+2)/((n+1)!(n+1))` (`e_enclosure`); they converge to `e`
   (`e_convergents_tendsto`); and the enclosure alone proves `e` irrational
   (`exp_one_irrational`: `n!(e − s_n)` would be an integer strictly between `0` and `1`).
4. **π through Machin's arms.** `π = 16 arctan(1/5) − 4 arctan(1/239)`
   (`Real.four_mul_arctan_inv_5_sub_arctan_inv_239`). Each arm is the partial navigator of the
   existing ratio `arctanRatio x i = −x²(2i+1)/(2i+3)` from `(x, x)` (`armSum_eq`), and consecutive
   partial sums bracket it, `S_(2N+1) ≤ arctan x ≤ S_(2N)` (`arm_enclosure`, from Mathlib's
   `Real.hasSum_arctan` and the alternating-series bounds). So `piLower N ≤ π ≤ piUpper N`
   (`pi_enclosure`), the width tends to zero (`pi_width_tendsto`), and the convergents converge to
   π (`pi_convergents_tendsto`). The arm `1/5` gains `log₁₀ 25` digits per ratio, where Leibniz's
   series at `x = 1` needs about `bᵏ⁺ˡ` terms for a window at offset `k`.
5. **A window is certified by the floors of both enclosure ends.** If `L ≤ x ≤ U` and
   `⌊bᵏ⁺ˡ L⌋ = ⌊bᵏ⁺ˡ U⌋`, the window of `l` digits at offset `k` is that floor's residue
   (`Mathematics/RadixWindowReceiver.window_eq_of_endpoint_floors_eq`). For `e` and π the
   certificate is an equality of two rational floors of one finite block
   (`e_window_certified`, `pi_window_certified`), and for every radix, offset and length some
   finite block carries it (`e_window_certificate_exists`, `pi_window_certificate_exists`), because
   `bᵏ⁺ˡx` is off the integer grid for irrational `x` (`off_grid_of_irrational`) and the enclosure
   widths fall to zero (`window_of_enclosure`).

[counterexample; formal-checked]
- **The certificate is load-bearing.** The block of `0` ratios returns `1`, whose floor reads the
  digit `0`, while the first digit of `e` after the point is `7` (`uncertified_block_misreads`):
  a convergent without the certificate does not read the window.
- **Off-grid is load-bearing for the search.** The one-sided enclosures `1 − 1/(N+1) ≤ 1 ≤ 1`
  converge, yet at radix ten no finite `N` certifies the first digit window of `1`:
  `⌊10 L_N⌋ ≠ ⌊10 U_N⌋` for every `N` (`on_grid_never_certifies`). An exact enclosure `L = U = x`
  certifies at once; the one-sided enclosures never do.

[open] The cost of a window (`Kt = |p| + log t`; the Bailey–Borwein–Plouffe jump `Uⁿ` by repeated
squaring, about `2 log₂ k` for offset `k`) is recorded in ELEMENTARY_OBJECTS ("Emanation and
resonance") and is not formalized here.

No `axiom`, no `sorry`.
-/

namespace Holonics.Compression.Landmark.ConstraintIdentity

open Filter Topology Finset
open Holonics.Mathematics.RatioSeriesTransport
open Holonics.Mathematics.RadixWindowReceiver

/-! ## 1. Partial navigators compose associatively -/

/-- [definition] The empty block: no ratio, unit multiplier, no sum. -/
def unitBlock : Block := ⟨0, 1, 0⟩

theorem compile_nil : compile [] = unitBlock := rfl

/-- [proved-derived; formal-checked] **Block composition is associative.** -/
theorem compose_assoc (a b c : Block) :
    (a.compose b).compose c = a.compose (b.compose c) := by
  simp only [Block.compose, Block.mk.injEq]
  refine ⟨by omega, by ring, by ring⟩

theorem unit_compose (b : Block) : unitBlock.compose b = b := by
  cases b
  simp only [unitBlock, Block.compose, Block.mk.injEq]
  refine ⟨by omega, by ring, by ring⟩

theorem compose_unit (b : Block) : b.compose unitBlock = b := by
  cases b
  simp only [unitBlock, Block.compose, Block.mk.injEq]
  refine ⟨by omega, by ring, by ring⟩

/-- [proved-derived; formal-checked] Executing a concatenated word executes its parts in order. -/
theorem execute_append (u v : List ℚ) (s : State) :
    execute (u ++ v) s = execute v (execute u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons r u ih => exact ih (step r s)

/-- [proved-derived; formal-checked] **Compilation turns concatenation into composition**, so any
bracketing of a ratio word (binary splitting in particular) compiles to one block. -/
theorem compile_append (u v : List ℚ) : compile (u ++ v) = (compile u).compose (compile v) := by
  induction u with
  | nil => rw [List.nil_append, compile_nil, unit_compose]
  | cons r u ih =>
    rw [List.cons_append, compile, compile, ih, compose_assoc]

/-! ## 2. A partial navigator returns the convergent -/

/-- [definition] The ratio word of the first `n` ratios. -/
def ratioWord (r : ℕ → ℚ) (n : ℕ) : List ℚ := (List.range n).map r

/-- [proved-derived; formal-checked] **The partial navigator returns the convergent.** For terms with
`t (i+1) = r i · t i`, executing the first `n` ratios from `(t 0, t 0)` returns
`(t n, Σ_(i<n+1) t i)`. -/
theorem execute_ratioWord (r t : ℕ → ℚ) (ht : ∀ i, t (i + 1) = r i * t i) (n : ℕ) :
    execute (ratioWord r n) (t 0, t 0) = (t n, ∑ i ∈ range (n + 1), t i) := by
  induction n with
  | zero => simp [ratioWord, execute]
  | succ n ih =>
    rw [ratioWord, List.range_succ, List.map_append, execute_append, ← ratioWord, ih]
    simp only [List.map_cons, List.map_nil, execute, step]
    rw [ht n, sum_range_succ _ (n + 1), ht n]

/-- [proved-derived; formal-checked] The same through the compiled block. -/
theorem partial_navigator_act (r t : ℕ → ℚ) (ht : ∀ i, t (i + 1) = r i * t i) (n : ℕ) :
    (compile (ratioWord r n)).act (t 0, t 0) = (t n, ∑ i ∈ range (n + 1), t i) := by
  rw [compile_act, execute_ratioWord r t ht]

/-! ## 3. A window is determined by a finite block -/

/-- [proved-derived; formal-checked] **A window is read from a finite enclosure.** If `bᵏ⁺ˡ x` is
off the integer grid and the enclosures `L N ≤ x ≤ U N` have width tending to zero, then some
finite `N` has equal floors at both ends, and the window of `l` digits at offset `k` is the
residue of that floor. -/
theorem window_of_enclosure {x : ℝ} {b : ℕ} (hb : 0 < b) (k l : ℕ)
    (hgrid : ∀ z : ℤ, (b : ℝ) ^ (k + l) * x ≠ z)
    (L U : ℕ → ℝ) (hL : ∀ N, L N ≤ x) (hU : ∀ N, x ≤ U N)
    (hwidth : Tendsto (fun N => U N - L N) atTop (𝓝 0)) :
    ∃ N, ⌊(b : ℝ) ^ (k + l) * L N⌋ = ⌊(b : ℝ) ^ (k + l) * U N⌋ ∧
      window b k l x = ⌊(b : ℝ) ^ (k + l) * L N⌋ % (b ^ l : ℤ) := by
  set s : ℝ := (b : ℝ) ^ (k + l) with hs
  have hspos : 0 < s := by positivity
  set y := s * x with hy
  set K := ⌊y⌋ with hK
  have hfl : (K : ℝ) ≤ y := Int.floor_le y
  have hlt : y < K + 1 := Int.lt_floor_add_one y
  have hne : (K : ℝ) ≠ y := fun h => hgrid K h.symm
  have hgap1 : 0 < y - K := by
    rcases lt_or_eq_of_le hfl with h | h
    · linarith
    · exact absurd h hne
  have hgap2 : 0 < (K : ℝ) + 1 - y := by linarith
  set δ := min (y - K) ((K : ℝ) + 1 - y) with hδ
  have hδpos : 0 < δ := lt_min hgap1 hgap2
  have hev : ∀ᶠ N in atTop, U N - L N < δ / s :=
    (tendsto_order.1 hwidth).2 _ (div_pos hδpos hspos)
  obtain ⟨N, hN⟩ := hev.exists
  have hLN := hL N
  have hUN := hU N
  have hwid : s * (U N - L N) < δ := by
    have := mul_lt_mul_of_pos_left hN hspos
    rwa [mul_div_cancel₀ _ hspos.ne'] at this
  have hδ1 : δ ≤ y - K := min_le_left _ _
  have hδ2 : δ ≤ (K : ℝ) + 1 - y := min_le_right _ _
  have hfloorL : ⌊s * L N⌋ = K := by
    rw [Int.floor_eq_iff]
    constructor
    · nlinarith
    · nlinarith
  have hfloorU : ⌊s * U N⌋ = K := by
    rw [Int.floor_eq_iff]
    constructor
    · nlinarith
    · nlinarith
  refine ⟨N, by rw [hfloorL, hfloorU], ?_⟩
  rw [hfloorL]
  exact window_eq_of_endpoint_floors_eq (K := K) hb hLN hUN hfloorL hfloorU

/-- [proved-derived; formal-checked] An irrational value is off every radix grid. -/
theorem off_grid_of_irrational {x : ℝ} (hx : Irrational x) {b : ℕ} (hb : 0 < b) (k l : ℕ) :
    ∀ z : ℤ, (b : ℝ) ^ (k + l) * x ≠ z := by
  intro z hz
  apply hx
  refine ⟨(z : ℚ) / (b : ℚ) ^ (k + l), ?_⟩
  have hs : (b : ℝ) ^ (k + l) ≠ 0 := by positivity
  push_cast
  rw [← hz]
  field_simp

/-- [counterexample; formal-checked] **Off-grid is load-bearing for the search.** The one-sided
enclosures `1 − 1/(N+1) ≤ 1 ≤ 1` have width tending to zero, yet at radix ten no `N` has equal
floors. -/
theorem on_grid_never_certifies :
    (∀ N : ℕ, (1 : ℝ) - 1 / (N + 1) ≤ 1) ∧
      Tendsto (fun N : ℕ => (1 : ℝ) - (1 - 1 / ((N : ℝ) + 1))) atTop (𝓝 0) ∧
      ∀ N : ℕ, ⌊(10 : ℝ) ^ (0 + 1) * (1 - 1 / ((N : ℝ) + 1))⌋ ≠ ⌊(10 : ℝ) ^ (0 + 1) * 1⌋ := by
  refine ⟨fun N => by have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
                      linarith, ?_, ?_⟩
  · simp only [sub_sub_cancel]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro N h
    have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    have h2 : ⌊(10 : ℝ) ^ (0 + 1) * (1 - 1 / ((N : ℝ) + 1))⌋ ≤ 9 := by
      rw [Int.floor_le_iff]
      push_cast
      nlinarith
    have h3 : ⌊(10 : ℝ) ^ (0 + 1) * 1⌋ = 10 := by norm_num
    rw [h, h3] at h2
    omega

/-! ## 4. `e` -/

/-- [definition] The ratio of `e`'s series: `t_(i+1) = t_i/(i+1)`. -/
def eRatio (i : ℕ) : ℚ := 1 / (i + 1)

/-- [definition] The terms of `e`'s series: `1/i!`. -/
def eTerm (i : ℕ) : ℚ := 1 / (i.factorial : ℚ)

theorem eTerm_succ (i : ℕ) : eTerm (i + 1) = eRatio i * eTerm i := by
  simp only [eTerm, eRatio, Nat.factorial_succ]
  push_cast
  field_simp

/-- [definition] The convergent of `e` returned by the partial navigator of `n` ratios. -/
def eConvergent (n : ℕ) : ℚ := ((compile (ratioWord eRatio n)).act (1, 1)).2

theorem eConvergent_eq (n : ℕ) : eConvergent n = ∑ i ∈ range (n + 1), eTerm i := by
  have h := partial_navigator_act eRatio eTerm eTerm_succ n
  have h0 : eTerm 0 = 1 := by simp [eTerm]
  rw [h0] at h
  rw [eConvergent, h]

theorem eConvergent_cast (n : ℕ) :
    (eConvergent n : ℝ) = ∑ i ∈ range (n + 1), (1 : ℝ) ^ i / (i.factorial : ℝ) := by
  rw [eConvergent_eq]
  push_cast
  simp [eTerm]

/-- [proved-derived; formal-checked] **`e`'s partial navigator encloses it exactly:**
`s_n + 1/(n+1)! ≤ e ≤ s_n + (n+2)/((n+1)!(n+1))`. -/
theorem e_enclosure (n : ℕ) :
    (eConvergent n : ℝ) + 1 / ((n + 1).factorial : ℝ) ≤ Real.exp 1 ∧
      Real.exp 1 ≤ (eConvergent n : ℝ) + (n + 2) / (((n + 1).factorial : ℝ) * (n + 1)) := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 1) zero_le_one (n + 2)
    rw [sum_range_succ, ← eConvergent_cast] at h
    simpa using h
  · have h := Real.exp_bound' (x := 1) zero_le_one le_rfl (n := n + 1) (Nat.succ_pos n)
    rw [← eConvergent_cast] at h
    push_cast at h
    simp only [one_pow, one_mul] at h
    convert h using 2
    ring

/-- [proved-derived; formal-checked] The width of `e`'s enclosure tends to zero. -/
theorem e_width_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) / (((n + 1).factorial : ℝ) * (n + 1))) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) (g := fun n : ℕ => 2 / ((n : ℝ) + 1))
  · intro n
    have hf : ((n : ℝ) + 1) ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.self_le_factorial (n + 1)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
    rw [mul_zero] at this
    exact this.congr fun n => by ring

/-- [proved-derived; formal-checked] **The landmark `e` is the limit of its partial navigator's
convergents.** -/
theorem e_convergents_tendsto : Tendsto (fun n => (eConvergent n : ℝ)) atTop (𝓝 (Real.exp 1)) := by
  have hw := e_width_tendsto
  have hlow : Tendsto (fun n : ℕ => Real.exp 1 - ((n : ℝ) + 2) / (((n + 1).factorial : ℝ) * (n + 1)))
      atTop (𝓝 (Real.exp 1)) := by
    simpa using tendsto_const_nhds.sub hw
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro n
    have := (e_enclosure n).2
    simp only
    linarith
  · intro n
    have := (e_enclosure n).1
    have : (0 : ℝ) ≤ 1 / ((n + 1).factorial : ℝ) := by positivity
    simp only
    linarith

/-- [proved-derived; formal-checked] **`e` is irrational, from its own enclosure.** If `e = p/q`,
then at `n = q` the scaled remainder `n!(e − s_n)` is an integer in `(0, 1)`. -/
theorem exp_one_irrational : Irrational (Real.exp 1) := by
  rintro ⟨r, hr⟩
  set n := r.den with hn
  have hnpos : 0 < n := r.den_pos
  obtain ⟨hlow, hup⟩ := e_enclosure n
  -- `n! · e` is an integer
  obtain ⟨m, hm⟩ : r.den ∣ n.factorial := Nat.dvd_factorial hnpos le_rfl
  have hie : (n.factorial : ℝ) * Real.exp 1 = ((m * r.num : ℤ) : ℝ) := by
    rw [← hr, Rat.cast_def]
    have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
    rw [hm]
    push_cast
    field_simp
  -- `n! · s_n` is an integer
  set S : ℕ := ∑ i ∈ range (n + 1), n.factorial / i.factorial with hS
  have his : (n.factorial : ℝ) * (eConvergent n : ℝ) = (S : ℝ) := by
    rw [eConvergent_cast, mul_sum, hS, Nat.cast_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [Nat.cast_div (Nat.factorial_dvd_factorial hi') (by positivity)]
    ring
  set z : ℤ := m * r.num - (S : ℤ) with hz
  have hzr : (z : ℝ) = (n.factorial : ℝ) * (Real.exp 1 - eConvergent n) := by
    rw [hz, Int.cast_sub, Int.cast_natCast, mul_sub, hie, his]
  have hfpos : (0 : ℝ) < n.factorial := by positivity
  have hsucc : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hz0 : (0 : ℝ) < z := by
    rw [hzr]
    have h1 : 0 < 1 / ((n + 1).factorial : ℝ) := by positivity
    have : 0 < Real.exp 1 - eConvergent n := by linarith
    positivity
  have hz1 : (z : ℝ) < 1 := by
    rw [hzr]
    have hb : Real.exp 1 - eConvergent n ≤ (n + 2) / (((n + 1).factorial : ℝ) * (n + 1)) := by
      linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    calc (n.factorial : ℝ) * (Real.exp 1 - eConvergent n)
        ≤ n.factorial * ((n + 2) / (((n + 1).factorial : ℝ) * (n + 1))) :=
          mul_le_mul_of_nonneg_left hb hfpos.le
      _ = (n + 2) / ((n + 1) * (n + 1)) := by
          rw [hsucc]; field_simp
      _ < 1 := by
          rw [div_lt_one (by positivity)]
          nlinarith
  have h0 : (0 : ℤ) < z := by exact_mod_cast hz0
  have h1 : z < 1 := by exact_mod_cast hz1
  omega

/-- [definition] The upper end of `e`'s enclosure after `N` ratios. -/
def eUpper (N : ℕ) : ℚ := eConvergent N + (N + 2) / ((N + 1).factorial * (N + 1))

theorem e_mem_enclosure (N : ℕ) :
    (eConvergent N : ℝ) ≤ Real.exp 1 ∧ Real.exp 1 ≤ (eUpper N : ℝ) := by
  obtain ⟨h1, h2⟩ := e_enclosure N
  refine ⟨by have : (0 : ℝ) ≤ 1 / ((N + 1).factorial : ℝ) := by positivity
             linarith, ?_⟩
  rw [eUpper]
  push_cast
  exact h2

/-- [proved-derived; formal-checked] **A certified window of `e`.** When the floors of both ends
of `e`'s enclosure agree at the scale `bᵏ⁺ˡ`, a checkable equality of two rational floors, the
window of `l` digits at offset `k` is the residue of that floor. -/
theorem e_window_certified {b : ℕ} (hb : 0 < b) (k l N : ℕ)
    (h : ⌊(b : ℚ) ^ (k + l) * eConvergent N⌋ = ⌊(b : ℚ) ^ (k + l) * eUpper N⌋) :
    window b k l (Real.exp 1) = ⌊(b : ℚ) ^ (k + l) * eConvergent N⌋ % (b ^ l : ℤ) := by
  obtain ⟨hL, hU⟩ := e_mem_enclosure N
  apply window_eq_of_endpoint_floors_eq hb hL hU
  · rw [← Rat.floor_cast (α := ℝ)]; push_cast; rfl
  · rw [h, ← Rat.floor_cast (α := ℝ)]; push_cast; rfl

/-- [proved-derived; formal-checked] **Every window of `e` is certified by a finite block**: in
every radix `b > 0`, some `N` makes the floors of both enclosure ends agree. -/
theorem e_window_certificate_exists {b : ℕ} (hb : 0 < b) (k l : ℕ) :
    ∃ N, ⌊(b : ℚ) ^ (k + l) * eConvergent N⌋ = ⌊(b : ℚ) ^ (k + l) * eUpper N⌋ := by
  obtain ⟨N, hN, -⟩ := window_of_enclosure hb k l
    (off_grid_of_irrational exp_one_irrational hb k l)
    (fun N => (eConvergent N : ℝ)) (fun N => (eUpper N : ℝ))
    (fun N => (e_mem_enclosure N).1) (fun N => (e_mem_enclosure N).2)
    (by
      have := e_width_tendsto
      refine this.congr fun N => ?_
      rw [eUpper]
      push_cast
      ring)
  refine ⟨N, ?_⟩
  rw [← Rat.floor_cast (α := ℝ) ((b : ℚ) ^ (k + l) * eConvergent N),
    ← Rat.floor_cast (α := ℝ) ((b : ℚ) ^ (k + l) * eUpper N)]
  push_cast
  exact hN

/-- [counterexample; formal-checked] **The certificate is load-bearing.** The block of `0` ratios
has the convergent `1`, whose floor at radix ten reads the digit `0`; the first digit of `e` after
the point is `7`. A block without the certificate does not read the window. -/
theorem uncertified_block_misreads :
    window 10 0 1 (Real.exp 1) = 7 ∧ ⌊(10 : ℚ) ^ (0 + 1) * eConvergent 0⌋ % (10 ^ 1 : ℤ) = 0 := by
  have h3 := e_mem_enclosure 3
  have hlo : (27 / 10 : ℝ) ≤ Real.exp 1 := by
    have := (e_enclosure 3).1
    rw [eConvergent_cast] at this
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hhi : Real.exp 1 < 28 / 10 := by
    have := h3.2
    rw [eUpper, eConvergent_eq] at this
    norm_num [Finset.sum_range_succ, Nat.factorial, eTerm] at this
    linarith
  constructor
  · rw [window]
    have : ⌊(10 : ℝ) ^ (0 + 1) * Real.exp 1⌋ = 27 := by
      rw [Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith
    push_cast at this ⊢
    rw [this]
    norm_num
  · rw [eConvergent_eq]
    norm_num [eTerm]

/-! ## 5. π through Machin's arms -/

/-- [definition] The partial sum of the arm `arctan x` returned by the partial navigator of `n`
ratios `arctanRatio x i = −x²(2i+1)/(2i+3)` from `(x, x)`. -/
def armSum (x : ℚ) (n : ℕ) : ℚ := ((compile (ratioWord (arctanRatio x) n)).act (x, x)).2

theorem armSum_eq (x : ℚ) (n : ℕ) : armSum x n = ∑ i ∈ range (n + 1), arctanTerm x i := by
  have h := partial_navigator_act (arctanRatio x) (arctanTerm x) (arctanTerm_succ x) n
  have h0 : arctanTerm x 0 = x := by simp [arctanTerm]
  rw [h0] at h
  rw [armSum, h]

theorem armSum_cast (x : ℚ) (n : ℕ) :
    (armSum x n : ℝ) =
      ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i * ((x : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
  rw [armSum_eq]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  simp only [arctanTerm]
  push_cast
  ring

theorem arm_antitone {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone fun i : ℕ => x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
  intro i j hij
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  calc x ^ (2 * j + 1) / (2 * (j : ℝ) + 1)
      ≤ x ^ (2 * i + 1) / (2 * (j : ℝ) + 1) :=
        div_le_div_of_nonneg_right (pow_le_pow_of_le_one h0 h1 (by omega)) (by positivity)
    _ ≤ x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

theorem arm_tendsto {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * (i : ℝ) + 1))) atTop
      (𝓝 (Real.arctan x)) := by
  have hs := (Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1))
  refine hs.tendsto_sum_nat.congr fun n => sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- [proved-derived; formal-checked] **Consecutive partial sums of an arm bracket it:**
`S_(2N+1) ≤ arctan x ≤ S_(2N)` for `0 ≤ x < 1`, each read from a finite block. -/
theorem arm_enclosure {x : ℚ} (h0 : 0 ≤ x) (h1 : x < 1) (N : ℕ) :
    (armSum x (2 * N + 1) : ℝ) ≤ Real.arctan x ∧ Real.arctan x ≤ (armSum x (2 * N) : ℝ) := by
  have h0' : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have h1' : (x : ℝ) < 1 := by exact_mod_cast h1
  constructor
  · have h := (arm_antitone h0' h1'.le).alternating_series_le_tendsto (arm_tendsto h0' h1') (N + 1)
    rw [armSum_cast, show 2 * N + 1 + 1 = 2 * (N + 1) by ring]
    exact h
  · have h := (arm_antitone h0' h1'.le).tendsto_le_alternating_series (arm_tendsto h0' h1') N
    rw [armSum_cast]
    exact h

theorem armSum_tendsto {x : ℚ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Tendsto (fun n => (armSum x n : ℝ)) atTop (𝓝 (Real.arctan x)) := by
  have h0' : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have h1' : (x : ℝ) < 1 := by exact_mod_cast h1
  refine ((arm_tendsto h0' h1').comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
  rw [armSum_cast]
  rfl

/-- [definition] The lower end of Machin's enclosure of π after `N` blocks of two ratios per arm:
`16 S⁽⁵⁾_(2N+1) − 4 S⁽²³⁹⁾_(2N)`. -/
def piLower (N : ℕ) : ℚ := 16 * armSum (1 / 5) (2 * N + 1) - 4 * armSum (1 / 239) (2 * N)

/-- [definition] The upper end: `16 S⁽⁵⁾_(2N) − 4 S⁽²³⁹⁾_(2N+1)`. -/
def piUpper (N : ℕ) : ℚ := 16 * armSum (1 / 5) (2 * N) - 4 * armSum (1 / 239) (2 * N + 1)

theorem machin :
    Real.pi = 16 * Real.arctan ((1 / 5 : ℚ) : ℝ) - 4 * Real.arctan ((1 / 239 : ℚ) : ℝ) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  push_cast
  rw [one_div, one_div]
  linarith

/-- [proved-derived; formal-checked] **Machin's lifted phase is Gaussian-integer arithmetic:**
`(5 + i)⁴ = (239 + i)(2 + 2i)`, so the phase of `(5 + i)⁴` is that of `239 + i` plus a quarter-turn
carried by `2 + 2i`; `machin` is its arctangent reading. -/
theorem gaussian_machin_factorization :
    ((5 : ℂ) + Complex.I) ^ 4 = ((239 : ℂ) + Complex.I) * (2 + 2 * Complex.I) := by
  apply Complex.ext <;> norm_num [pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]

/-- [proved-derived; formal-checked] **Machin's arms enclose π:** `π = 16 arctan(1/5) − 4
arctan(1/239)` (`Real.four_mul_arctan_inv_5_sub_arctan_inv_239`) with each arm between consecutive
partial sums. -/
theorem pi_enclosure (N : ℕ) : (piLower N : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpper N : ℝ) := by
  obtain ⟨a1, a2⟩ := arm_enclosure (x := 1 / 5) (by norm_num) (by norm_num) N
  obtain ⟨b1, b2⟩ := arm_enclosure (x := 1 / 239) (by norm_num) (by norm_num) N
  rw [machin, piLower, piUpper]
  push_cast
  constructor <;> linarith

/-- [proved-derived; formal-checked] The width of Machin's enclosure tends to zero. -/
theorem pi_width_tendsto :
    Tendsto (fun N => (piUpper N : ℝ) - (piLower N : ℝ)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id]; omega) tendsto_id
  have h21 : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id]; omega) tendsto_id
  have d5 := ((armSum_tendsto (x := 1 / 5) (by norm_num) (by norm_num)).comp h2).sub
    ((armSum_tendsto (x := 1 / 5) (by norm_num) (by norm_num)).comp h21)
  have d239 := ((armSum_tendsto (x := 1 / 239) (by norm_num) (by norm_num)).comp h2).sub
    ((armSum_tendsto (x := 1 / 239) (by norm_num) (by norm_num)).comp h21)
  rw [sub_self] at d5 d239
  have := (d5.const_mul 16).add (d239.const_mul 4)
  rw [mul_zero, mul_zero, add_zero] at this
  refine this.congr fun N => ?_
  simp only [Function.comp, piLower, piUpper]
  push_cast
  ring

/-- [proved-derived; formal-checked] **The landmark π is the limit of Machin's partial
navigators**: the lower ends converge to it. -/
theorem pi_convergents_tendsto : Tendsto (fun N => (piLower N : ℝ)) atTop (𝓝 Real.pi) := by
  have hup : Tendsto (fun N => Real.pi - ((piUpper N : ℝ) - (piLower N : ℝ))) atTop
      (𝓝 Real.pi) := by
    simpa using tendsto_const_nhds.sub pi_width_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hup tendsto_const_nhds (fun N => ?_)
    (fun N => (pi_enclosure N).1)
  have := (pi_enclosure N).2
  simp only
  linarith

/-- [proved-derived; formal-checked] **A certified window of π.** When the floors of both ends of
Machin's enclosure agree at the scale `bᵏ⁺ˡ`, the window of `l` digits at offset `k` is the residue
of that floor. -/
theorem pi_window_certified {b : ℕ} (hb : 0 < b) (k l N : ℕ)
    (h : ⌊(b : ℚ) ^ (k + l) * piLower N⌋ = ⌊(b : ℚ) ^ (k + l) * piUpper N⌋) :
    window b k l Real.pi = ⌊(b : ℚ) ^ (k + l) * piLower N⌋ % (b ^ l : ℤ) := by
  obtain ⟨hL, hU⟩ := pi_enclosure N
  apply window_eq_of_endpoint_floors_eq hb hL hU
  · rw [← Rat.floor_cast (α := ℝ)]; push_cast; rfl
  · rw [h, ← Rat.floor_cast (α := ℝ)]; push_cast; rfl

/-- [proved-derived; formal-checked] **Every window of π is certified by a finite block of Machin's
arms**: in every radix `b > 0`, some `N` makes the floors of both enclosure ends agree. -/
theorem pi_window_certificate_exists {b : ℕ} (hb : 0 < b) (k l : ℕ) :
    ∃ N, ⌊(b : ℚ) ^ (k + l) * piLower N⌋ = ⌊(b : ℚ) ^ (k + l) * piUpper N⌋ := by
  obtain ⟨N, hN, -⟩ := window_of_enclosure hb k l (off_grid_of_irrational irrational_pi hb k l)
    (fun N => (piLower N : ℝ)) (fun N => (piUpper N : ℝ))
    (fun N => (pi_enclosure N).1) (fun N => (pi_enclosure N).2) pi_width_tendsto
  refine ⟨N, ?_⟩
  rw [← Rat.floor_cast (α := ℝ) ((b : ℚ) ^ (k + l) * piLower N),
    ← Rat.floor_cast (α := ℝ) ((b : ℚ) ^ (k + l) * piUpper N)]
  push_cast
  exact hN

section Audit
#print axioms compose_assoc
#print axioms compile_append
#print axioms partial_navigator_act
#print axioms window_of_enclosure
#print axioms on_grid_never_certifies
#print axioms e_enclosure
#print axioms e_convergents_tendsto
#print axioms exp_one_irrational
#print axioms e_window_certified
#print axioms e_window_certificate_exists
#print axioms uncertified_block_misreads
#print axioms arm_enclosure
#print axioms pi_enclosure
#print axioms pi_width_tendsto
#print axioms pi_convergents_tendsto
#print axioms pi_window_certified
#print axioms pi_window_certificate_exists
end Audit

end Holonics.Compression.Landmark.ConstraintIdentity
