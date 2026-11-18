import Mathlib
import HolonicsResearch.Landmarks.RegularComplexZeros
import HolonicsResearch.Zeta.FiniteLiCriterion
import HolonicsResearch.Holon.InertiaCount

/-!
# A regular complex's own half, as one chain of equivalences

[proved-derived; formal-checked] `Landmarks/RegularComplexZeros` places the zeros of the dart
determinant of a complex with `q + 1` darts at every cell and bounds its closed-walk count when
the modes are in the gap; `Zeta/FiniteLiCriterion` proves that a finite family of turns closed
under the circle's reversal is on the circle if and only if its counts stay under their total weight
on one side; `Holon/InertiaCount` counts the negative squares of the norm form
`[[q, A/2], [A/2, 1]]`. This module joins the three on one complex and states the join as one
theorem, `half_tfae`: five readings of the same complex that hold together or fail together.

[from training] The classical names. The dart operator is Hashimoto's edge operator, the
determinant formula is Ihara's and Bass's, the condition `λ² ≤ 4q` on the modes other than the
counts is the one Lubotzky, Phillips and Sarnak named "Ramanujan", and the one-sided positivity is
the finite form of Li's criterion. With `u = q^(−s)` the statement on the zeros is the analogue,
for this finite complex, of the Riemann hypothesis; nothing here is a statement about `ζ`.

## The setting

[definition] Finite `V` (cells) and `E` (contacts), `a b : E → V`, with `q + 1` darts at every
cell (`hreg`) and `1 ≤ q`. The cell operator `A = adjacency ℝ a b` has real modes
`λ i = eigen a b i`. A mode is a **count** when `λ i ² = (q + 1)²` (`countModes`: the constant
reading of a component at `q + 1`, and at `−(q + 1)` the alternating reading of a two-sided
component); the others are `otherModes`, numbering `nontrivialCount`.

* `smooth a b q l = (|E| − |V|)(1 + (−1)^l) + ∑ counts, (λ i / (q + 1))^l (q^l + 1)`: what the
  counts and the reversal's fixed part contribute to the closed-walk count at length `l` (a count
  `λ = ±(q + 1)` has cell roots `±q` and `±1`, `trivial_pair_pow`).
* `rem a b q l = walkCount a b l − smooth a b q l`: the remainder.
* `rootA`, `rootB`: the two roots of a cell `X² − λ X + q`, a conjugate pair in the gap
  `λ² ≤ 4q` and two reals `r`, `q / r` past it (`rootA_add_rootB`, `rootA_mul_rootB`,
  `normSq_rootA_of_le`, `not_normSq_of_gt`). `alpha`, `beta` are these at each mode.

## What is proved

* **H0, the remainder is a count of turns** (`rem_cast`, `count_gam`): `rem a b q l` is the sum
  over the modes other than the counts of `α i ^ l + β i ^ l`, and that sum is
  `FiniteLiCriterion.count` of the family `gam` on two copies of `otherModes` with weights one.
  The family is closed under the reversal `γ ↦ q / conj γ` (`gam_rev`): the reversal fixes each
  root of a pair in the gap and swaps the two real roots of a pair past it.
* **H1, the chain** (`half_tfae`). For `1 ≤ q` the following hold together:
  1. *tempered*: every mode other than a count has `λ² ≤ 4q`;
  2. *zeros on the circle*: every zero `u` of `det (1 − u B)` with `u² ≠ 1` and `u ≠ ±1/q` has
     `|u|² = 1/q`;
  3. *the count, both sides*: `|rem l| ≤ 2 · nontrivialCount · (√q)^l` at every length `l`;
  4. *the count, one side*: `rem l ≤ 2 · nontrivialCount · (√q)^l` at every length `l ≥ 1`;
  5. *the index*: the norm form's negative squares number the counts outside the gap,
     `n₋ [[q, A/2], [A/2, 1]] = #{i | 4q < λ i ² ∧ λ i ² = (q + 1)²}`.
  The single implications are named: `zeros_of_tempered`, `exists_zero_off_circle` (a mode past
  the gap that is not a count gives a real zero with `u² ≠ 1`, `u ≠ ±1/q`, off the circle),
  `abs_rem_le_of_tempered`, `tempered_of_rem_le`, `tempered_iff_negIndex_filter`; and the pairs
  `tempered_iff_zeros`, `tempered_iff_count`, `tempered_iff_count_le`, `tempered_iff_negIndex`
  (for `2 ≤ q`, where every count is outside the gap: `n₋ = #counts`).
* **H2, the one-sided scaled criterion** (`normSq_eq_of_re_count_le`): for a finite family of
  nonzero modes closed under `α ↦ q / conj α`, with positive weights, if the real parts of the
  counts stay under `(∑ m) (√q)^l` at every `l ≥ 1` then every mode has `|α|² = q`. This is the
  one-sided form of `FiniteLiCriterion.count_bound_iff_normSq`, and it is what makes reading 4
  enough: the upper side alone decides.
* **H3, the reversal on the zeros** (`zero_reversal`): away from `u² = 1` and `(q u)² = 1`,
  `u` is a zero of the dart determinant if and only if `1 / (q u)` is.
* **H4, the half as an exponent** (`norm_zero_of_tempered`, `tempered_iff_re_half`): on a tempered
  complex every such zero has `‖u‖ = q^(−1/2)`; and for `2 ≤ q` the complex is tempered if and
  only if every zero written `u = q^(−s)`, with `u² ≠ 1` and `u ≠ ±1/q`, has `Re s = 1/2`.

## What this does not state

* That `walkCount` counts closed walks of darts without backtracking: it is the trace of a power
  of the dart operator, as in `RegularComplexZeros`; the Euler product over prime cycles is
  `Landmarks/IharaEulerProduct`'s subject.
* Which complexes are tempered. The chain says what temperedness is equivalent to, on any regular
  complex; it constructs no tempered family and bounds no family's modes.
* A rate. Reading 4 failing means some length `l ≥ 1` has `rem l` past the bound; no bound on that
  first length is given (the return of a finite family of turns in `FiniteLiCriterion` is by
  compactness).
* The index on the dart space. Reading 5 counts the norm form on `V ⊕ V`, counts included; the
  restriction to the lift of the other modes is not written here.
* Anything about the integers: a regular complex is a finite specimen of the half.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix

namespace Holonics.Landmarks.RegularComplexHalf

open scoped ComplexConjugate
open RegularComplexZeros Holonics.Zeta.FiniteLiCriterion Holonics.Holon.Inertia
  Holonics.Holon.InertiaCount

/-! ## 1. The two roots of a cell -/

section Roots

/-- [definition] The first root of the cell `X² − λ X + q`: `(λ + i √(4q − λ²)) / 2` in the gap
`λ² ≤ 4q`, and the real `(λ + √(λ² − 4q)) / 2` past it. -/
noncomputable def rootA (lam q : ℝ) : ℂ :=
  if lam ^ 2 ≤ 4 * q then
    ((lam / 2 : ℝ) : ℂ) + ((Real.sqrt (4 * q - lam ^ 2) / 2 : ℝ) : ℂ) * Complex.I
  else (((lam + Real.sqrt (lam ^ 2 - 4 * q)) / 2 : ℝ) : ℂ)

/-- [definition] The second root of the cell `X² − λ X + q`. -/
noncomputable def rootB (lam q : ℝ) : ℂ :=
  if lam ^ 2 ≤ 4 * q then
    ((lam / 2 : ℝ) : ℂ) - ((Real.sqrt (4 * q - lam ^ 2) / 2 : ℝ) : ℂ) * Complex.I
  else (((lam - Real.sqrt (lam ^ 2 - 4 * q)) / 2 : ℝ) : ℂ)

/-- [proved-derived; formal-checked] The two roots sum to `λ`. -/
theorem rootA_add_rootB (lam q : ℝ) : rootA lam q + rootB lam q = (lam : ℂ) := by
  unfold rootA rootB
  split_ifs with h
  · push_cast
    ring
  · push_cast
    ring

/-- [proved-derived; formal-checked] The two roots multiply to `q`. -/
theorem rootA_mul_rootB (lam q : ℝ) : rootA lam q * rootB lam q = (q : ℂ) := by
  unfold rootA rootB
  split_ifs with h
  · have hs : Real.sqrt (4 * q - lam ^ 2) ^ 2 = 4 * q - lam ^ 2 := Real.sq_sqrt (by linarith)
    have hsc : ((Real.sqrt (4 * q - lam ^ 2) : ℝ) : ℂ) ^ 2 = 4 * (q : ℂ) - (lam : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, hs]
      push_cast
      ring
    push_cast
    linear_combination (1 / 4 : ℂ) * hsc -
      (((Real.sqrt (4 * q - lam ^ 2) : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq
  · have hs : Real.sqrt (lam ^ 2 - 4 * q) ^ 2 = lam ^ 2 - 4 * q :=
      Real.sq_sqrt (by linarith [not_le.mp h])
    rw [← Complex.ofReal_mul]
    congr 1
    linear_combination (-1 / 4 : ℝ) * hs

/-- A root pair with sum `λ` and product `q`: each is a root of the cell. -/
theorem cell_of_sum_prod {lam q : ℝ} {α β : ℂ} (hs : α + β = (lam : ℂ))
    (hp : α * β = (q : ℂ)) : α ^ 2 - (lam : ℂ) * α + (q : ℂ) = 0 := by
  linear_combination α * hs - hp

theorem rootA_ne_zero {lam q : ℝ} (hq : q ≠ 0) : rootA lam q ≠ 0 := by
  intro h0
  have h := rootA_mul_rootB lam q
  rw [h0, zero_mul] at h
  exact hq (Complex.ofReal_eq_zero.mp h.symm)

theorem rootB_ne_zero {lam q : ℝ} (hq : q ≠ 0) : rootB lam q ≠ 0 := by
  intro h0
  have h := rootA_mul_rootB lam q
  rw [h0, mul_zero] at h
  exact hq (Complex.ofReal_eq_zero.mp h.symm)

/-- [proved-derived; formal-checked] In the gap the first root is at the half: `|α|² = q`. -/
theorem normSq_rootA_of_le {lam q : ℝ} (h : lam ^ 2 ≤ 4 * q) :
    Complex.normSq (rootA lam q) = q :=
  RegularGraphNormForm.cell_normSq_of_le
    (cell_of_sum_prod (rootA_add_rootB lam q) (rootA_mul_rootB lam q)) h

/-- [proved-derived; formal-checked] In the gap the second root is at the half: `|β|² = q`. -/
theorem normSq_rootB_of_le {lam q : ℝ} (h : lam ^ 2 ≤ 4 * q) :
    Complex.normSq (rootB lam q) = q :=
  RegularGraphNormForm.cell_normSq_of_le
    (cell_of_sum_prod (by rw [add_comm]; exact rootA_add_rootB lam q)
      (by rw [mul_comm]; exact rootA_mul_rootB lam q)) h

/-- Past the gap the first root is real. -/
theorem conj_rootA_of_gt {lam q : ℝ} (h : 4 * q < lam ^ 2) :
    conj (rootA lam q) = rootA lam q := by
  unfold rootA
  rw [if_neg (not_le.mpr h), Complex.conj_ofReal]

/-- Past the gap the second root is real. -/
theorem conj_rootB_of_gt {lam q : ℝ} (h : 4 * q < lam ^ 2) :
    conj (rootB lam q) = rootB lam q := by
  unfold rootB
  rw [if_neg (not_le.mpr h), Complex.conj_ofReal]

/-- [proved-derived; formal-checked] Past the gap the two roots are not both at the half. -/
theorem not_normSq_of_gt {lam q : ℝ} (h : 4 * q < lam ^ 2) :
    ¬ (Complex.normSq (rootA lam q) = q ∧ Complex.normSq (rootB lam q) = q) := by
  rintro ⟨h1, h2⟩
  have hs : Real.sqrt (lam ^ 2 - 4 * q) ^ 2 = lam ^ 2 - 4 * q := Real.sq_sqrt (by linarith)
  unfold rootA at h1
  unfold rootB at h2
  rw [if_neg (not_le.mpr h), Complex.normSq_ofReal] at h1 h2
  have h3 : lam ^ 2 = 4 * q := by linear_combination h1 + h2 - (1 / 2 : ℝ) * hs
  linarith

/-- [proved-derived; formal-checked] In the gap the reversal `γ ↦ q / conj γ` fixes the first
root. -/
theorem rootA_reversal_of_le {lam q : ℝ} (hq : q ≠ 0) (h : lam ^ 2 ≤ 4 * q) :
    (q : ℂ) / conj (rootA lam q) = rootA lam q := by
  rw [div_eq_iff ((map_ne_zero (starRingEnd ℂ)).mpr (rootA_ne_zero hq)), Complex.mul_conj,
    normSq_rootA_of_le h]

/-- [proved-derived; formal-checked] In the gap the reversal fixes the second root. -/
theorem rootB_reversal_of_le {lam q : ℝ} (hq : q ≠ 0) (h : lam ^ 2 ≤ 4 * q) :
    (q : ℂ) / conj (rootB lam q) = rootB lam q := by
  rw [div_eq_iff ((map_ne_zero (starRingEnd ℂ)).mpr (rootB_ne_zero hq)), Complex.mul_conj,
    normSq_rootB_of_le h]

/-- [proved-derived; formal-checked] Past the gap the reversal carries the first root to the
second. -/
theorem rootA_reversal_of_gt {lam q : ℝ} (hq : q ≠ 0) (h : 4 * q < lam ^ 2) :
    (q : ℂ) / conj (rootA lam q) = rootB lam q := by
  rw [conj_rootA_of_gt h, div_eq_iff (rootA_ne_zero hq), mul_comm, rootA_mul_rootB]

/-- [proved-derived; formal-checked] Past the gap the reversal carries the second root to the
first. -/
theorem rootB_reversal_of_gt {lam q : ℝ} (hq : q ≠ 0) (h : 4 * q < lam ^ 2) :
    (q : ℂ) / conj (rootB lam q) = rootA lam q := by
  rw [conj_rootB_of_gt h, div_eq_iff (rootB_ne_zero hq), rootA_mul_rootB]

/-- [proved-derived; formal-checked] **A count's pair.** A cell with `λ² = (q + 1)²` has the roots
`±q` and `±1` with the sign of `λ`: any root pair of it contributes
`(λ / (q + 1))^l (q^l + 1)` at length `l`. -/
theorem trivial_pair_pow {q : ℕ} {lam : ℝ} (hlam : lam ^ 2 = ((q : ℝ) + 1) ^ 2) {α β : ℂ}
    (hs : α + β = (lam : ℂ)) (hp : α * β = (q : ℂ)) (l : ℕ) :
    α ^ l + β ^ l = ((lam : ℂ) / ((q : ℂ) + 1)) ^ l * ((q : ℂ) ^ l + 1) := by
  have hq1 : ((q : ℂ) + 1) ≠ 0 := by
    have h : ((q : ℝ) + 1) ≠ 0 := by positivity
    exact_mod_cast h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hlam with rfl | rfl
  · have e : (((q : ℝ) + 1 : ℝ) : ℂ) / ((q : ℂ) + 1) = 1 := by
      push_cast
      exact div_self hq1
    rw [e, one_pow, one_mul]
    push_cast at hs
    have hfac : (α - 1) * (α - (q : ℂ)) = 0 := by linear_combination α * hs - hp
    rcases mul_eq_zero.mp hfac with h | h
    · have ha : α = 1 := sub_eq_zero.mp h
      have hb : β = (q : ℂ) := by
        rw [ha] at hs
        linear_combination hs
      rw [ha, hb]
      ring
    · have ha : α = (q : ℂ) := sub_eq_zero.mp h
      have hb : β = 1 := by
        rw [ha] at hs
        linear_combination hs
      rw [ha, hb]
      ring
  · have e : ((-((q : ℝ) + 1) : ℝ) : ℂ) / ((q : ℂ) + 1) = -1 := by
      push_cast
      rw [neg_div, div_self hq1]
    rw [e]
    push_cast at hs
    have hfac : (α + 1) * (α + (q : ℂ)) = 0 := by linear_combination α * hs - hp
    rcases mul_eq_zero.mp hfac with h | h
    · have ha : α = -1 := eq_neg_of_add_eq_zero_left h
      have hb : β = -(q : ℂ) := by
        rw [ha] at hs
        linear_combination hs
      rw [ha, hb, neg_pow (q : ℂ)]
      ring
    · have ha : α = -(q : ℂ) := eq_neg_of_add_eq_zero_left h
      have hb : β = -1 := by
        rw [ha] at hs
        linear_combination hs
      rw [ha, hb, neg_pow (q : ℂ)]
      ring

end Roots

/-! ## 2. The one-sided scaled criterion -/

section OneSided

variable {ι : Type*} [Fintype ι]

/-- [proved-derived; formal-checked] **H2, the one-sided scaled criterion.** For `q > 0` and a
finite family of nonzero modes closed under `α ↦ q / conj α`, with positive weights: if the real
parts of the counts stay under `(∑ i, m i) (√q)^l` at every length `l ≥ 1`, every mode has
`|α|² = q`. -/
theorem normSq_eq_of_re_count_le (m : ι → ℝ) (hm : ∀ i, 0 < m i) {q : ℝ} (hq : 0 < q)
    (α : ι → ℂ) (σ : ι → ι) (hα0 : ∀ i, α i ≠ 0)
    (hσ : ∀ i, α (σ i) = (q : ℂ) / conj (α i))
    (h : ∀ l : ℕ, 1 ≤ l → (count m α l).re ≤ (∑ i, m i) * Real.sqrt q ^ l) :
    ∀ i, Complex.normSq (α i) = q := by
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt q := ⟨_, rfl⟩
  rw [← hsdef] at h
  have hs : 0 < s := by
    rw [hsdef]
    exact Real.sqrt_pos.mpr hq
  have hss : s * s = q := by
    rw [hsdef]
    exact Real.mul_self_sqrt hq.le
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hqc : (q : ℂ) = (s : ℂ) * (s : ℂ) := by
    rw [← Complex.ofReal_mul, hss]
  obtain ⟨w, hwdef⟩ : ∃ w : ι → ℂ, ∀ i, w i = α i / (s : ℂ) :=
    ⟨fun i => α i / (s : ℂ), fun _ => rfl⟩
  have hw0 : ∀ i, w i ≠ 0 := fun i => by
    rw [hwdef]
    exact div_ne_zero (hα0 i) hsc
  have hσw : ∀ i, w (σ i) = (conj (w i))⁻¹ := by
    intro i
    have hc : conj (α i) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr (hα0 i)
    rw [hwdef, hwdef, hσ, map_div₀, Complex.conj_ofReal, inv_div, hqc]
    field_simp
  have hcount : ∀ l : ℕ, count m w l = count m α l / ((s ^ l : ℝ) : ℂ) := by
    intro l
    unfold count
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, div_pow, mul_div_assoc, Complex.ofReal_pow]
  have hall := norm_eq_one_of_re_count_le m w hm σ hw0 hσw (fun n hn => by
    rw [hcount, Complex.div_ofReal_re, div_le_iff₀ (pow_pos hs n)]
    exact h n hn)
  intro i
  have h1 := hall i
  rw [hwdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    div_eq_one_iff_eq hs.ne'] at h1
  rw [Complex.normSq_eq_norm_sq, h1, sq, hss]

end OneSided

/-! ## 3. The complex: counts, the smooth part and the remainder -/

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (a b : E → V)

/-- [definition] The counts: the modes with `λ² = (q + 1)²`. -/
noncomputable def countModes (q : ℕ) : Finset V :=
  Finset.univ.filter fun i => eigen a b i ^ 2 = ((q : ℝ) + 1) ^ 2

/-- [definition] The modes other than the counts. -/
noncomputable def otherModes (q : ℕ) : Finset V :=
  Finset.univ.filter fun i => ¬ eigen a b i ^ 2 = ((q : ℝ) + 1) ^ 2

theorem mem_countModes (q : ℕ) (i : V) :
    i ∈ countModes a b q ↔ eigen a b i ^ 2 = ((q : ℝ) + 1) ^ 2 := by
  simp [countModes]

theorem mem_otherModes (q : ℕ) (i : V) :
    i ∈ otherModes a b q ↔ eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 := by
  simp [otherModes]

/-- [definition] The number of modes other than the counts. -/
noncomputable def nontrivialCount (q : ℕ) : ℕ := (otherModes a b q).card

/-- [definition] The smooth part of the closed-walk count at length `l`: the reversal's fixed part
`(|E| − |V|)(1 + (−1)^l)` and each count's `(λ / (q + 1))^l (q^l + 1)`. -/
noncomputable def smooth (q l : ℕ) : ℝ :=
  ((Fintype.card E : ℝ) - Fintype.card V) * (1 + (-1) ^ l) +
    ∑ i ∈ countModes a b q, (eigen a b i / ((q : ℝ) + 1)) ^ l * ((q : ℝ) ^ l + 1)

/-- [definition] The remainder of the closed-walk count at length `l`. -/
noncomputable def rem (q l : ℕ) : ℝ := walkCount a b l - smooth a b q l

/-- [definition] The first root of each mode's cell. -/
noncomputable def alpha (q : ℕ) (i : V) : ℂ := rootA (eigen a b i) q

/-- [definition] The second root of each mode's cell. -/
noncomputable def beta (q : ℕ) (i : V) : ℂ := rootB (eigen a b i) q

theorem alpha_add_beta (q : ℕ) (i : V) :
    alpha a b q i + beta a b q i = ((eigen a b i : ℝ) : ℂ) :=
  rootA_add_rootB _ _

theorem alpha_mul_beta (q : ℕ) (i : V) : alpha a b q i * beta a b q i = (q : ℂ) := by
  unfold alpha beta
  rw [rootA_mul_rootB]
  push_cast
  rfl

theorem norm_alpha_of_le {q : ℕ} {i : V} (h : eigen a b i ^ 2 ≤ 4 * (q : ℝ)) :
    ‖alpha a b q i‖ = Real.sqrt q := by
  have h1 : Complex.normSq (alpha a b q i) = (q : ℝ) := normSq_rootA_of_le h
  rw [Complex.normSq_eq_norm_sq] at h1
  rw [← h1, Real.sqrt_sq (norm_nonneg _)]

theorem norm_beta_of_le {q : ℕ} {i : V} (h : eigen a b i ^ 2 ≤ 4 * (q : ℝ)) :
    ‖beta a b q i‖ = Real.sqrt q := by
  have h1 : Complex.normSq (beta a b q i) = (q : ℝ) := normSq_rootB_of_le h
  rw [Complex.normSq_eq_norm_sq] at h1
  rw [← h1, Real.sqrt_sq (norm_nonneg _)]

/-- [proved-derived; formal-checked] The smooth part read in `ℂ`: the reversal's fixed part and
the counts' root pairs. -/
theorem smooth_cast {q : ℕ} (hVE : Fintype.card V ≤ Fintype.card E) (l : ℕ) :
    ((smooth a b q l : ℝ) : ℂ) =
      ((Fintype.card E - Fintype.card V : ℕ) : ℂ) * (1 + (-1) ^ l) +
        ∑ i ∈ countModes a b q, (alpha a b q i ^ l + beta a b q i ^ l) := by
  unfold smooth
  push_cast [Nat.cast_sub hVE]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [trivial_pair_pow ((mem_countModes a b q i).mp hi) (alpha_add_beta a b q i)
    (alpha_mul_beta a b q i) l]

/-- [proved-derived; formal-checked] **H0, the remainder is the other modes' root pairs.** On a
regular complex with `|V| ≤ |E|`,
`rem l = ∑ i ∈ otherModes, (α i ^ l + β i ^ l)`. -/
theorem rem_cast {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) (l : ℕ) :
    ((rem a b q l : ℝ) : ℂ) =
      ∑ i ∈ otherModes a b q, (alpha a b q i ^ l + beta a b q i ^ l) := by
  have htr := trace_hashimoto_pow a b hreg hVE (alpha_add_beta a b q) (alpha_mul_beta a b q) l
  rw [← walkCount_cast] at htr
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset V)
    (fun i => eigen a b i ^ 2 = ((q : ℝ) + 1) ^ 2)
    (fun i => alpha a b q i ^ l + beta a b q i ^ l)
  unfold rem
  rw [Complex.ofReal_sub, htr, smooth_cast a b hVE l, ← hsplit]
  unfold countModes otherModes
  ring

/-! ## 4. The remainder as a count of turns closed under the reversal -/

/-- [definition] The family of the other modes' roots, on two copies of `otherModes`. -/
noncomputable def gam (q : ℕ) : (otherModes a b q) ⊕ (otherModes a b q) → ℂ :=
  Sum.elim (fun i => alpha a b q i) (fun i => beta a b q i)

/-- [definition] The reversal on the family's index: the identity on a pair in the gap, the swap
on a pair past it. -/
noncomputable def rev (q : ℕ) :
    (otherModes a b q) ⊕ (otherModes a b q) → (otherModes a b q) ⊕ (otherModes a b q) :=
  Sum.elim (fun i => if eigen a b i ^ 2 ≤ 4 * (q : ℝ) then Sum.inl i else Sum.inr i)
    (fun i => if eigen a b i ^ 2 ≤ 4 * (q : ℝ) then Sum.inr i else Sum.inl i)

theorem gam_ne_zero {q : ℕ} (hq : 1 ≤ q) (j : (otherModes a b q) ⊕ (otherModes a b q)) :
    gam a b q j ≠ 0 := by
  have hq0 : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rcases j with i | i
  · exact rootA_ne_zero hq0
  · exact rootB_ne_zero hq0

/-- [proved-derived; formal-checked] The family is closed under the reversal `γ ↦ q / conj γ`. -/
theorem gam_rev {q : ℕ} (hq : 1 ≤ q) (j : (otherModes a b q) ⊕ (otherModes a b q)) :
    gam a b q (rev a b q j) = (((q : ℕ) : ℝ) : ℂ) / conj (gam a b q j) := by
  have hq0 : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rcases j with i | i
  · by_cases h : eigen a b i ^ 2 ≤ 4 * (q : ℝ)
    · have hr : rev a b q (Sum.inl i) = Sum.inl i := by simp [rev, h]
      rw [hr]
      exact (rootA_reversal_of_le hq0 h).symm
    · have hr : rev a b q (Sum.inl i) = Sum.inr i := by simp [rev, h]
      rw [hr]
      exact (rootA_reversal_of_gt hq0 (not_le.mp h)).symm
  · by_cases h : eigen a b i ^ 2 ≤ 4 * (q : ℝ)
    · have hr : rev a b q (Sum.inr i) = Sum.inr i := by simp [rev, h]
      rw [hr]
      exact (rootB_reversal_of_le hq0 h).symm
    · have hr : rev a b q (Sum.inr i) = Sum.inl i := by simp [rev, h]
      rw [hr]
      exact (rootB_reversal_of_gt hq0 (not_le.mp h)).symm

/-- [proved-derived; formal-checked] **H0, the remainder is a count of turns.** The count of the
family `gam` with weights one is the remainder. -/
theorem count_gam {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) (l : ℕ) :
    count (fun _ : (otherModes a b q) ⊕ (otherModes a b q) => (1 : ℝ)) (gam a b q) l =
      ((rem a b q l : ℝ) : ℂ) := by
  rw [rem_cast a b hreg hVE l]
  unfold count
  rw [Fintype.sum_sum_type]
  simp only [Complex.ofReal_one, one_mul, gam, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_add_distrib,
    Finset.sum_coe_sort (otherModes a b q) (fun i => alpha a b q i ^ l),
    Finset.sum_coe_sort (otherModes a b q) (fun i => beta a b q i ^ l)]

/-- The family's total weight is twice the number of the other modes. -/
theorem sum_one_eq (q : ℕ) :
    ∑ _j : (otherModes a b q) ⊕ (otherModes a b q), (1 : ℝ) =
      2 * (nontrivialCount a b q : ℝ) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_coe, nsmul_eq_mul,
    mul_one, nontrivialCount]
  push_cast
  ring

/-! ## 5. The single implications -/

/-- [proved-derived; formal-checked] **Tempered gives the zeros on the circle.** If every mode
other than a count has `λ² ≤ 4q`, a zero `u` of the dart determinant with `u² ≠ 1` and `u ≠ ±1/q`
has `|u|² = 1/q`. The edge `λ² = 4q` is included. -/
theorem zeros_of_tempered {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (htemp : ∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ))
    {u : ℂ} (h0 : (1 - u • IharaBass.hashimoto ℂ a b).det = 0) (hu : u ^ 2 ≠ 1)
    (h1 : u ≠ 1 / (q : ℂ)) (h2 : u ≠ -(1 / (q : ℂ))) :
    Complex.normSq u = 1 / (q : ℝ) := by
  obtain ⟨i, hi⟩ := (det_hashimoto_eq_zero_iff_cell a b hreg hu).mp h0
  by_cases ht : eigen a b i ^ 2 = ((q : ℝ) + 1) ^ 2
  · rcases trivial_cell_zero ht hu hi with h | h
    · exact absurd h h1
    · exact absurd h h2
  · have hle := htemp i ht
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hi
    have hcell : u⁻¹ ^ 2 - ((eigen a b i : ℝ) : ℂ) * u⁻¹ + (((q : ℕ) : ℝ) : ℂ) = 0 := by
      have e : u⁻¹ ^ 2 - ((eigen a b i : ℝ) : ℂ) * u⁻¹ + (((q : ℕ) : ℝ) : ℂ) =
          (1 - ((eigen a b i : ℝ) : ℂ) * u + (q : ℂ) * u ^ 2) * u⁻¹ ^ 2 := by
        push_cast
        field_simp
      rw [e, hi, zero_mul]
    have hn := RegularGraphNormForm.cell_normSq_of_le hcell hle
    rw [map_inv₀] at hn
    rw [one_div, ← hn, inv_inv]

/-- [proved-derived; formal-checked] **A mode past the gap that is not a count is heard in the
zeros.** It gives the dart determinant a real zero `u` with `u² ≠ 1`, `u ≠ ±1/q` and
`|u|² ≠ 1/q`. -/
theorem exists_zero_off_circle {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    {i : V} (h1 : 4 * (q : ℝ) < eigen a b i ^ 2)
    (h2 : eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2) :
    ∃ u : ℂ, (1 - u • IharaBass.hashimoto ℂ a b).det = 0 ∧ u ^ 2 ≠ 1 ∧ u ≠ 1 / (q : ℂ) ∧
      u ≠ -(1 / (q : ℂ)) ∧ Complex.normSq u ≠ 1 / (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨u, hu, hne⟩ := Holonics.Zeta.HermiteBiehlerHalf.cell_boost hq0 h1
  have hu1 : u ^ 2 ≠ 1 := by
    intro h
    apply h2
    have hlu : eigen a b i * u = (q : ℝ) + 1 := by linear_combination -hu + (q : ℝ) * h
    calc eigen a b i ^ 2 = (eigen a b i * u) ^ 2 := by rw [mul_pow, h, mul_one]
      _ = ((q : ℝ) + 1) ^ 2 := by rw [hlu]
  have hu2 : u ≠ 1 / (q : ℝ) := by
    intro h
    apply h2
    have hqu : (q : ℝ) * u = 1 := by
      rw [h]
      field_simp
    have hl : eigen a b i = (q : ℝ) + 1 := by
      linear_combination (-(q : ℝ)) * hu + ((q : ℝ) * u + 1 - eigen a b i) * hqu
    rw [hl]
  have hu3 : u ≠ -(1 / (q : ℝ)) := by
    intro h
    apply h2
    have hqu : (q : ℝ) * u = -1 := by
      rw [h]
      field_simp
    have hl : eigen a b i = -((q : ℝ) + 1) := by
      linear_combination (q : ℝ) * hu + (eigen a b i + 1 - (q : ℝ) * u) * hqu
    rw [hl]
    ring
  have hu1c : ((u : ℝ) : ℂ) ^ 2 ≠ 1 := by
    intro h
    exact hu1 (by exact_mod_cast h)
  refine ⟨(u : ℂ), ?_, hu1c, ?_, ?_, ?_⟩
  · rw [det_hashimoto_eq_zero_iff_cell a b hreg hu1c]
    refine ⟨i, ?_⟩
    have := congrArg (fun x : ℝ => (x : ℂ)) hu
    simpa using this
  · intro h
    apply hu2
    apply Complex.ofReal_injective
    rw [h]
    push_cast
    ring
  · intro h
    apply hu3
    apply Complex.ofReal_injective
    rw [h]
    push_cast
    ring
  · rw [Complex.normSq_ofReal]
    intro h
    exact hne (by rw [sq]; exact h)

/-- [proved-derived; formal-checked] **Tempered gives the count on both sides.** If every mode
other than a count has `λ² ≤ 4q`, then `|rem l| ≤ 2 · nontrivialCount · (√q)^l` at every `l`. -/
theorem abs_rem_le_of_tempered {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E)
    (htemp : ∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ))
    (l : ℕ) :
    |rem a b q l| ≤ 2 * (nontrivialCount a b q : ℝ) * Real.sqrt q ^ l := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, rem_cast a b hreg hVE l]
  calc ‖∑ i ∈ otherModes a b q, (alpha a b q i ^ l + beta a b q i ^ l)‖
      ≤ ∑ i ∈ otherModes a b q, ‖alpha a b q i ^ l + beta a b q i ^ l‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ otherModes a b q, 2 * Real.sqrt q ^ l := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hle := htemp i ((mem_otherModes a b q i).mp hi)
        calc ‖alpha a b q i ^ l + beta a b q i ^ l‖
            ≤ ‖alpha a b q i ^ l‖ + ‖beta a b q i ^ l‖ := norm_add_le _ _
          _ = 2 * Real.sqrt q ^ l := by
              rw [norm_pow, norm_pow, norm_alpha_of_le a b hle, norm_beta_of_le a b hle]
              ring
    _ = 2 * (nontrivialCount a b q : ℝ) * Real.sqrt q ^ l := by
        rw [Finset.sum_const, nsmul_eq_mul, nontrivialCount]
        ring

/-- [proved-derived; formal-checked] **The count on one side gives tempered.** If
`rem l ≤ 2 · nontrivialCount · (√q)^l` at every length `l ≥ 1`, every mode other than a count has
`λ² ≤ 4q`. The lower side is not asked. -/
theorem tempered_of_rem_le {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (h : ∀ l : ℕ, 1 ≤ l → rem a b q l ≤ 2 * (nontrivialCount a b q : ℝ) * Real.sqrt q ^ l) :
    ∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ) := by
  have hVE := card_le_card_of_regular a b hreg hq
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast hq
  have hall := normSq_eq_of_re_count_le
    (fun _ : (otherModes a b q) ⊕ (otherModes a b q) => (1 : ℝ)) (fun _ => one_pos) hq0
    (gam a b q) (rev a b q) (gam_ne_zero a b hq) (gam_rev a b hq)
    (fun l hl => by
      rw [count_gam a b hreg hVE l, Complex.ofReal_re, sum_one_eq a b q]
      exact h l hl)
  intro i hi
  by_contra hlt
  have hi' : i ∈ otherModes a b q := (mem_otherModes a b q i).mpr hi
  exact not_normSq_of_gt (not_le.mp hlt)
    ⟨hall (Sum.inl ⟨i, hi'⟩), hall (Sum.inr ⟨i, hi'⟩)⟩

/-- [proved-derived; formal-checked] The norm form's negative squares, read in this module's
modes: they number the modes with `4q < λ²`. -/
theorem negIndex_eq (q : ℕ) :
    negIndex (normMatrix (IharaBass.adjacency ℝ a b) (q : ℝ)) =
      (Finset.univ.filter fun i => 4 * (q : ℝ) < eigen a b i ^ 2).card :=
  negIndex_normMatrix (adjacency_isHermitian a b) (q : ℝ)

/-- [proved-derived; formal-checked] **Tempered is the index.** Every mode other than a count has
`λ² ≤ 4q` if and only if the norm form's negative squares number the counts outside the gap. -/
theorem tempered_iff_negIndex_filter (q : ℕ) :
    (∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ)) ↔
      negIndex (normMatrix (IharaBass.adjacency ℝ a b) (q : ℝ)) =
        (Finset.univ.filter fun i => 4 * (q : ℝ) < eigen a b i ^ 2 ∧
          eigen a b i ^ 2 = ((q : ℝ) + 1) ^ 2).card := by
  rw [negIndex_eq]
  constructor
  · intro h
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro hlt
      refine ⟨hlt, ?_⟩
      by_contra hne
      exact absurd (h i hne) (not_le.mpr hlt)
    · exact fun hi => hi.1
  · intro h i hi
    by_contra hlt
    have hsub : (Finset.univ.filter fun i => 4 * (q : ℝ) < eigen a b i ^ 2 ∧
        eigen a b i ^ 2 = ((q : ℝ) + 1) ^ 2) ⊆
        (Finset.univ.filter fun i => 4 * (q : ℝ) < eigen a b i ^ 2) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, hj.2.1⟩
    have heq := Finset.eq_of_subset_of_card_le hsub h.le
    have hmem : i ∈ (Finset.univ.filter fun i => 4 * (q : ℝ) < eigen a b i ^ 2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hlt⟩
    rw [← heq, Finset.mem_filter] at hmem
    exact hi hmem.2.2

/-! ## 6. The chain -/

/-- [proved-derived; formal-checked] **H1, the complex's own half as one chain.** On a complex
with `q + 1` darts at every cell, `1 ≤ q`, the following hold together: every mode other than a
count is in the closed gap; every zero of the dart determinant away from `u² = 1` and `u = ±1/q`
is on the circle `|u|² = 1/q`; the closed-walk count's remainder is within
`2 · nontrivialCount · (√q)^l` on both sides at every length; it is under that bound on the upper
side at every length `l ≥ 1`; the norm form's negative squares number the counts outside the
gap. -/
theorem half_tfae {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ v : V,
      (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1) :
    List.TFAE [
      ∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ),
      ∀ u : ℂ, (1 - u • IharaBass.hashimoto ℂ a b).det = 0 → u ^ 2 ≠ 1 → u ≠ 1 / (q : ℂ) →
        u ≠ -(1 / (q : ℂ)) → Complex.normSq u = 1 / (q : ℝ),
      ∀ l : ℕ, |rem a b q l| ≤ 2 * (nontrivialCount a b q : ℝ) * Real.sqrt q ^ l,
      ∀ l : ℕ, 1 ≤ l → rem a b q l ≤ 2 * (nontrivialCount a b q : ℝ) * Real.sqrt q ^ l,
      negIndex (normMatrix (IharaBass.adjacency ℝ a b) (q : ℝ)) =
        (Finset.univ.filter fun i => 4 * (q : ℝ) < eigen a b i ^ 2 ∧
          eigen a b i ^ 2 = ((q : ℝ) + 1) ^ 2).card] := by
  have hVE := card_le_card_of_regular a b hreg hq
  tfae_have 1 → 2 := fun h u h0 hu h1 h2 => zeros_of_tempered a b hreg h h0 hu h1 h2
  tfae_have 2 → 1 := by
    intro h i hi
    by_contra hlt
    obtain ⟨u, h0, hu, h1, h2, hn⟩ := exists_zero_off_circle a b hq hreg (not_le.mp hlt) hi
    exact hn (h u h0 hu h1 h2)
  tfae_have 1 → 3 := fun h l => abs_rem_le_of_tempered a b hreg hVE h l
  tfae_have 3 → 4 := fun h l _ => (le_abs_self _).trans (h l)
  tfae_have 4 → 1 := tempered_of_rem_le a b hq hreg
  tfae_have 1 ↔ 5 := tempered_iff_negIndex_filter a b q
  tfae_finish

/-- [proved-derived; formal-checked] Tempered if and only if the zeros are on the circle. -/
theorem tempered_iff_zeros {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ v : V,
      (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1) :
    (∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ)) ↔
      ∀ u : ℂ, (1 - u • IharaBass.hashimoto ℂ a b).det = 0 → u ^ 2 ≠ 1 → u ≠ 1 / (q : ℂ) →
        u ≠ -(1 / (q : ℂ)) → Complex.normSq u = 1 / (q : ℝ) :=
  (half_tfae a b hq hreg).out 0 1

/-- [proved-derived; formal-checked] Tempered if and only if the count's remainder is within the
half's bound on both sides at every length. -/
theorem tempered_iff_count {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ v : V,
      (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1) :
    (∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ)) ↔
      ∀ l : ℕ, |rem a b q l| ≤ 2 * (nontrivialCount a b q : ℝ) * Real.sqrt q ^ l :=
  (half_tfae a b hq hreg).out 0 2

/-- [proved-derived; formal-checked] Tempered if and only if the count's remainder is under the
half's bound on the upper side at every length `l ≥ 1`: Li's form. -/
theorem tempered_iff_count_le {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ v : V,
      (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1) :
    (∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ)) ↔
      ∀ l : ℕ, 1 ≤ l → rem a b q l ≤ 2 * (nontrivialCount a b q : ℝ) * Real.sqrt q ^ l :=
  (half_tfae a b hq hreg).out 0 3

/-- [proved-derived; formal-checked] **Tempered is the index, `q ≥ 2`.** There every count is
outside the gap, so the complex is tempered if and only if the norm form's negative squares
number the counts. -/
theorem tempered_iff_negIndex {q : ℕ} (hq : 2 ≤ q) :
    (∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ)) ↔
      negIndex (normMatrix (IharaBass.adjacency ℝ a b) (q : ℝ)) = (countModes a b q).card := by
  rw [tempered_iff_negIndex_filter]
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hfil : (Finset.univ.filter fun i => 4 * (q : ℝ) < eigen a b i ^ 2 ∧
      eigen a b i ^ 2 = ((q : ℝ) + 1) ^ 2) = countModes a b q := by
    unfold countModes
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      nlinarith
  rw [hfil]

/-! ## 7. The reversal on the zeros, and the half as an exponent -/

/-- [proved-derived; formal-checked] **H3, the reversal on the zeros.** Away from `u² = 1` and
`(q u)² = 1`, `u` is a zero of the dart determinant if and only if `1 / (q u)` is: the cell
`1 − λ u + q u²` at `1 / (q u)` is the same cell divided by `q u²`. -/
theorem zero_reversal {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ v : V,
      (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    {u : ℂ} (hu0 : u ≠ 0) (hu : u ^ 2 ≠ 1) (hqu : ((q : ℂ) * u) ^ 2 ≠ 1) :
    (1 - u • IharaBass.hashimoto ℂ a b).det = 0 ↔
      (1 - (1 / ((q : ℂ) * u)) • IharaBass.hashimoto ℂ a b).det = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqu0 : (q : ℂ) * u ^ 2 ≠ 0 := mul_ne_zero hq0 (pow_ne_zero 2 hu0)
  have hv : (1 / ((q : ℂ) * u)) ^ 2 ≠ 1 := by
    rw [div_pow, one_pow, Ne, div_eq_one_iff_eq (pow_ne_zero 2 (mul_ne_zero hq0 hu0))]
    exact fun h => hqu h.symm
  rw [det_hashimoto_eq_zero_iff_cell a b hreg hu, det_hashimoto_eq_zero_iff_cell a b hreg hv]
  have key : ∀ lam : ℂ, 1 - lam * (1 / ((q : ℂ) * u)) + (q : ℂ) * (1 / ((q : ℂ) * u)) ^ 2 =
      (1 - lam * u + (q : ℂ) * u ^ 2) / ((q : ℂ) * u ^ 2) := by
    intro lam
    field_simp
    ring
  refine exists_congr fun i => ?_
  rw [key, div_eq_zero_iff, or_iff_left hqu0]

/-- [proved-derived; formal-checked] **H4, the half as an exponent.** On a tempered complex every
zero of the dart determinant away from `u² = 1` and `u = ±1/q` has `‖u‖ = q^(−1/2)`. -/
theorem norm_zero_of_tempered {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (htemp : ∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ))
    {u : ℂ} (h0 : (1 - u • IharaBass.hashimoto ℂ a b).det = 0) (hu : u ^ 2 ≠ 1)
    (h1 : u ≠ 1 / (q : ℂ)) (h2 : u ≠ -(1 / (q : ℂ))) :
    ‖u‖ = (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have h := zeros_of_tempered a b hreg htemp h0 hu h1 h2
  rw [Complex.normSq_eq_norm_sq] at h
  rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, ← one_div, ← h,
    Real.sqrt_sq (norm_nonneg _)]

/-- [proved-derived; formal-checked] In the chart `u = q^(−s)` with `q ≥ 2`, the circle
`|u|² = 1/q` is the line `Re s = 1/2`. -/
theorem normSq_cpow_neg {q : ℕ} (hq : 2 ≤ q) (s : ℂ) :
    Complex.normSq ((q : ℂ) ^ (-s)) = 1 / (q : ℝ) ↔ s.re = 1 / 2 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hn : Complex.normSq ((q : ℂ) ^ (-s)) = (q : ℝ) ^ (-2 * s.re) := by
    rw [Complex.normSq_eq_norm_sq, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re, ← Real.rpow_natCast,
      ← Real.rpow_mul hq0.le]
    congr 1
    push_cast
    ring
  have h1 : (1 : ℝ) / q = (q : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, one_div]
  rw [hn, h1]
  constructor
  · intro h
    have hle := (Real.rpow_le_rpow_left_iff hq1).mp h.le
    have hge := (Real.rpow_le_rpow_left_iff hq1).mp h.ge
    linarith
  · intro h
    rw [h]
    norm_num

/-- [proved-derived; formal-checked] **H4, the half as a line, `q ≥ 2`.** The complex is tempered
if and only if every zero of the dart determinant written `u = q^(−s)`, with `u² ≠ 1` and
`u ≠ ±1/q`, has `Re s = 1/2`. At `q = 1` the circle is `|u| = 1` and `q^(−s)` reads no real part,
which is why `q ≥ 2` is asked. -/
theorem tempered_iff_re_half {q : ℕ} (hq : 2 ≤ q)
    (hreg : ∀ v : V,
      (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1) :
    (∀ i, eigen a b i ^ 2 ≠ ((q : ℝ) + 1) ^ 2 → eigen a b i ^ 2 ≤ 4 * (q : ℝ)) ↔
      ∀ s : ℂ, (1 - ((q : ℂ) ^ (-s)) • IharaBass.hashimoto ℂ a b).det = 0 →
        ((q : ℂ) ^ (-s)) ^ 2 ≠ 1 → (q : ℂ) ^ (-s) ≠ 1 / (q : ℂ) →
        (q : ℂ) ^ (-s) ≠ -(1 / (q : ℂ)) → s.re = 1 / 2 := by
  have hq1 : 1 ≤ q := by omega
  rw [tempered_iff_zeros a b hq1 hreg]
  constructor
  · intro h s h0 hu h1 h2
    exact (normSq_cpow_neg hq s).mp (h _ h0 hu h1 h2)
  · intro h u h0 hu h1 h2
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at h0
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hlog : Complex.log (q : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q)]
      exact Complex.ofReal_ne_zero.mpr
        (Real.log_pos (by exact_mod_cast (by omega : 1 < q))).ne'
    have hus : (q : ℂ) ^ (-(-(Complex.log u / Complex.log q))) = u := by
      rw [neg_neg, Complex.cpow_def_of_ne_zero hq0]
      have e : Complex.log (q : ℂ) * (Complex.log u / Complex.log q) = Complex.log u := by
        field_simp
      rw [e, Complex.exp_log hu0]
    have hre := h (-(Complex.log u / Complex.log q)) (by rw [hus]; exact h0)
      (by rw [hus]; exact hu) (by rw [hus]; exact h1) (by rw [hus]; exact h2)
    have hn := (normSq_cpow_neg hq _).mpr hre
    rwa [hus] at hn

section Audit

#print axioms rootA_add_rootB
#print axioms rootA_mul_rootB
#print axioms not_normSq_of_gt
#print axioms trivial_pair_pow
#print axioms normSq_eq_of_re_count_le
#print axioms rem_cast
#print axioms gam_rev
#print axioms count_gam
#print axioms zeros_of_tempered
#print axioms exists_zero_off_circle
#print axioms abs_rem_le_of_tempered
#print axioms tempered_of_rem_le
#print axioms tempered_iff_negIndex_filter
#print axioms half_tfae
#print axioms tempered_iff_zeros
#print axioms tempered_iff_count
#print axioms tempered_iff_count_le
#print axioms tempered_iff_negIndex
#print axioms zero_reversal
#print axioms norm_zero_of_tempered
#print axioms normSq_cpow_neg
#print axioms tempered_iff_re_half

end Audit

end Holonics.Landmarks.RegularComplexHalf
