import Mathlib

/-!
# The finite Li criterion: the counts stay inside their bound if and only if every mode is at the half

[proved-derived; formal-checked] A finite family of modes `w i` with weights `m i > 0` has counts
`count m w n = ∑ i, m i * w i ^ n` and Li numbers `li m w n = ∑ i, m i * (1 − w i ^ n)`. When the
family is closed under the circle's reversal `w ↦ 1 / conj w`, three statements are one:

* every mode is on the circle, `‖w i‖ = 1`;
* the counts stay inside their bound at every length, `‖count m w n‖ ≤ ∑ i, m i`;
* the Li numbers have nonnegative real part at every length `n ≥ 1`.

The step that is not the triangle inequality is that a mode outside the circle is heard at some
length: its count's real part passes any bound. That step needs the modes of largest modulus to
return together near their opening phase at lengths as large as we like, which is the return of a
finite family of turns (a rotation of a finite torus comes back near the identity).

## What is proved

* **L1, the return of a finite family of turns** (`exists_pow_near_one`): for `‖u i‖ = 1`, every
  `ε > 0` and every `N`, there is `n ≥ N`, `n ≥ 1`, with `‖u i ^ n − 1‖ < ε` for every `i` at
  once. Proof: the powers lie in a compact ball, so a subsequence is Cauchy, and two of its terms
  far apart differ by a power close to one.
* **L2, a mode outside the circle is heard** (`exists_re_count_gt`): if some `‖w j‖ > 1`, then
  for every `C` there is `n ≥ 1` with `C < (count m w n).re`. The modes of largest modulus `R`
  return together (L1), so they contribute at least half their weight times `R ^ n`; every other
  mode is smaller by a factor that tends to zero.
* **L3, the count criterion.**
  * `norm_count_le`: modes in the closed disc keep `‖count m w n‖ ≤ ∑ i, m i`.
  * `norm_le_one_of_re_count_le`, `count_bounded_iff_norm_le_one`: with no reversal assumed, the
    counts are bounded by `∑ i, m i` at every length if and only if every mode is in the closed
    disc.
  * `exists_re_count_gt_of_norm_ne_one`: with the reversal, a mode off the circle on either side is
    heard at some length (its partner under the reversal is outside).
  * `count_criterion_tfae`: the three statements above are equivalent, with
    `norm_eq_one_iff_count_bounded` and `norm_eq_one_iff_li_nonneg` the two readings as
    biconditionals. The reversal is used only as a map `σ` of the index with
    `w (σ i) = (conj (w i))⁻¹`; that `σ` is an involution and that the weights are invariant under
    it are not needed for these statements, so they are not assumed.
* **L4, the scaled chart** (`count_bound_iff_normSq`): for `q > 0` and modes `α i ≠ 0` closed
  under `α ↦ q / conj α`, the bound `‖count m α l‖ ≤ (∑ i, m i) * q ^ (l / 2)` at every length `l`
  holds if and only if `normSq (α i) = q` for every mode.
* **L5, the line chart** (`li_line_criterion`): for modes `ρ i ≠ 0, 1` closed under
  `ρ ↦ 1 − conj ρ`, with `liLine m ρ n = ∑ i, m i * (1 − (1 − 1/ρ i) ^ n)`, the real parts of
  `liLine m ρ n` are nonnegative for every `n ≥ 1` if and only if `(ρ i).re = 1/2` for every mode.
  `cayley_norm_eq_one_iff` is the chart (`‖1 − 1/ρ‖ = 1 ↔ ρ.re = 1/2`) and `cayley_reversal` carries
  the line's reversal to the circle's.

## Reading

[interpretation] For a finite complex with `q + 1` contacts a cell, the modes are the nontrivial
`α` of its dart operator, the reversal is `α ↦ q / conj α` (the functional equation
`u ↦ 1 / (q u)` with the real structure), and `count m α l` is the remainder of the count of closed
walks of length `l` after its smooth part. L4 then says that the remainder staying within
`(∑ m) q ^ (l / 2)` at every length is the same statement as every nontrivial mode at the half,
`|α|² = q`. The implication from the half to the bound is the closed-walk count's bound; the
implication from the bound to the half is its converse, which holds for every finite family and
not only on a specimen. For the integers the modes are the zeros, the reversal is
`s ↦ 1 − conj s`, and L5 is the finite form of Li's criterion.

[from training] Li's criterion (X.-J. Li, 1997) states that the Riemann hypothesis holds if and
only if `λ_n = ∑_ρ (1 − (1 − 1/ρ) ^ n) ≥ 0` for every `n ≥ 1`; Bombieri and Lagarias (1999) showed
that the equivalence is a statement about any multiset of complex numbers under a convergence
condition, of which the finite case is the one proved here.

## What this does not state

Nothing here is about the zeta function's own zeros. An unending family of modes needs its
convergence (the sum over zeros is conditionally convergent and is taken in symmetric order) and
the archimedean term of the explicit formula; this file is the finite face only, where every sum is
a finite sum. The identification of a finite complex's closed-walk remainders with `count`
(through `det (1 − u B)`) is not made in this file. The lengths at which a mode off the circle is
heard are not bounded: L1 is a compactness statement and gives no rate.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace Holonics.Zeta.FiniteLiCriterion

open Filter Topology
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-! ### The counts and the Li numbers -/

/-- [definition] The count of a weighted family of modes at length `n`. -/
def count (m : ι → ℝ) (w : ι → ℂ) (n : ℕ) : ℂ := ∑ i, (m i : ℂ) * w i ^ n

/-- [definition] The Li number of a weighted family of modes at `n`, in the circle's chart. -/
def li (m : ι → ℝ) (w : ι → ℂ) (n : ℕ) : ℂ := ∑ i, (m i : ℂ) * (1 - w i ^ n)

/-- [proved-derived; formal-checked] The real part of a count is the weighted sum of the real
parts of the modes' powers. -/
theorem count_re (m : ι → ℝ) (w : ι → ℂ) (n : ℕ) :
    (count m w n).re = ∑ i, m i * (w i ^ n).re := by
  unfold count
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.re_ofReal_mul _ _

/-- [proved-derived; formal-checked] A Li number is the total weight less the count. -/
theorem li_eq (m : ι → ℝ) (w : ι → ℂ) (n : ℕ) :
    li m w n = ((∑ i, m i : ℝ) : ℂ) - count m w n := by
  unfold li count
  rw [Complex.ofReal_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- [proved-derived; formal-checked] The real part of a Li number is the total weight less the
real part of the count. -/
theorem li_re (m : ι → ℝ) (w : ι → ℂ) (n : ℕ) :
    (li m w n).re = ∑ i, m i - (count m w n).re := by
  rw [li_eq, Complex.sub_re, Complex.ofReal_re]

/-! ### L1: the return of a finite family of turns -/

/-- A strictly increasing sequence of naturals moves at least one step a step. -/
theorem strictMono_add_le {φ : ℕ → ℕ} (hφ : StrictMono φ) (a k : ℕ) : φ a + k ≤ φ (a + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : φ (a + k) < φ (a + (k + 1)) := hφ (by omega)
    omega

/-- [proved-derived; formal-checked] **L1, the return of a finite family of turns.** Finitely many
unit complex numbers have a common power, at a length as large as we like, at which every one of
them is within `ε` of one. -/
theorem exists_pow_near_one (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ ∀ i, ‖u i ^ n - 1‖ < ε := by
  obtain ⟨x, hxdef⟩ : ∃ x : ℕ → ι → ℂ, ∀ n i, x n i = u i ^ n :=
    ⟨fun n i => u i ^ n, fun _ _ => rfl⟩
  have hx : ∀ n, x n ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [hxdef, norm_pow, hu i, one_pow]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ι → ℂ) 1).tendsto_subseq hx
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
  have hdist : dist (x (φ (K + (N + 1)))) (x (φ K)) < ε :=
    hK (K + (N + 1)) (Nat.le_add_right _ _) K le_rfl
  have hgap : φ K + (N + 1) ≤ φ (K + (N + 1)) := strictMono_add_le hφ K (N + 1)
  refine ⟨φ (K + (N + 1)) - φ K, by omega, by omega, fun i => ?_⟩
  have hle : dist (x (φ (K + (N + 1))) i) (x (φ K) i) ≤ dist (x (φ (K + (N + 1)))) (x (φ K)) :=
    dist_le_pi_dist _ _ i
  have hsplit : u i ^ φ (K + (N + 1)) = u i ^ φ K * u i ^ (φ (K + (N + 1)) - φ K) := by
    rw [← pow_add]
    congr 1
    omega
  have hnorm : ‖u i ^ φ (K + (N + 1)) - u i ^ φ K‖ = ‖u i ^ (φ (K + (N + 1)) - φ K) - 1‖ := by
    have hfac : u i ^ φ (K + (N + 1)) - u i ^ φ K
        = u i ^ φ K * (u i ^ (φ (K + (N + 1)) - φ K) - 1) := by
      rw [mul_sub_one, ← hsplit]
    rw [hfac, norm_mul, norm_pow, hu i, one_pow, one_mul]
  rw [← hnorm, ← dist_eq_norm, ← hxdef, ← hxdef]
  exact lt_of_le_of_lt hle hdist

/-! ### L2: a mode outside the circle is heard -/

/-- [proved-derived; formal-checked] **L2, a mode outside the circle is heard.** If some mode has
modulus over one, the real part of the count passes every bound at some length `n ≥ 1`. -/
theorem exists_re_count_gt (m : ι → ℝ) (hm : ∀ i, 0 < m i) (w : ι → ℂ) {j : ι}
    (hj : 1 < ‖w j‖) (C : ℝ) : ∃ n : ℕ, 1 ≤ n ∧ C < (count m w n).re := by
  classical
  -- the largest modulus, attained at `i₀`
  obtain ⟨R, hmax, hR1, i₀, hi₀⟩ :
      ∃ R : ℝ, (∀ i, ‖w i‖ ≤ R) ∧ 1 < R ∧ ∃ i₀, ‖w i₀‖ = R := by
    obtain ⟨i₀, -, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun i => ‖w i‖) ⟨j, Finset.mem_univ j⟩
    exact ⟨‖w i₀‖, fun i => hmax i (Finset.mem_univ i),
      lt_of_lt_of_le hj (hmax j (Finset.mem_univ j)), i₀, rfl⟩
  have hR0 : 0 < R := lt_trans zero_lt_one hR1
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR0.ne'
  -- the turns of the modes of largest modulus
  obtain ⟨u, hudef⟩ : ∃ u : ι → ℂ, ∀ i, u i = if ‖w i‖ = R then w i / (R : ℂ) else 1 :=
    ⟨fun i => if ‖w i‖ = R then w i / (R : ℂ) else 1, fun _ => rfl⟩
  have hu : ∀ i, ‖u i‖ = 1 := by
    intro i
    by_cases h : ‖w i‖ = R
    · rw [hudef, if_pos h, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, h,
        div_self hR0.ne']
    · rw [hudef, if_neg h, norm_one]
  -- the smaller modes, relative to `R ^ n`, tend to zero
  have hf : Tendsto (fun n : ℕ => ∑ i, if ‖w i‖ = R then (0 : ℝ) else m i * (‖w i‖ / R) ^ n)
      atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ∑ i, if ‖w i‖ = R then (0 : ℝ) else m i * (‖w i‖ / R) ^ n)
        atTop (𝓝 (∑ _i : ι, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      by_cases h : ‖w i‖ = R
      · simp only [if_pos h]
        exact tendsto_const_nhds
      · simp only [if_neg h]
        have hlt : ‖w i‖ / R < 1 := (div_lt_one hR0).mpr (lt_of_le_of_ne (hmax i) h)
        have h0 : 0 ≤ ‖w i‖ / R := div_nonneg (norm_nonneg _) hR0.le
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hlt).const_mul (m i)
    simpa using h
  have hm0 : 0 < m i₀ / 4 := by
    have := hm i₀
    positivity
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hf.eventually (gt_mem_nhds hm0))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hR1).eventually_gt_atTop (4 * C / m i₀))
  obtain ⟨n, hnN, hn1, hn⟩ :=
    exists_pow_near_one u hu (show (0 : ℝ) < 1 / 2 by norm_num) (max N₁ N₂)
  refine ⟨n, hn1, ?_⟩
  have hf_n : (∑ i, if ‖w i‖ = R then (0 : ℝ) else m i * (‖w i‖ / R) ^ n) < m i₀ / 4 :=
    hN₁ n (le_trans (le_max_left _ _) hnN)
  have hR_n : 4 * C / m i₀ < R ^ n := hN₂ n (le_trans (le_max_right _ _) hnN)
  have hRn : 0 < R ^ n := pow_pos hR0 n
  -- each mode against its share
  have hterm : ∀ i, R ^ n * ((if ‖w i‖ = R then m i / 2 else 0)
        - (if ‖w i‖ = R then (0 : ℝ) else m i * (‖w i‖ / R) ^ n)) ≤ m i * (w i ^ n).re := by
    intro i
    by_cases h : ‖w i‖ = R
    · rw [if_pos h, if_pos h, sub_zero]
      have hui : u i = w i / (R : ℂ) := by rw [hudef, if_pos h]
      have hwi : w i = (R : ℂ) * u i := by
        rw [hui]
        field_simp
      have hre_u : 1 / 2 ≤ (u i ^ n).re := by
        have h1 : |(u i ^ n - 1).re| ≤ ‖u i ^ n - 1‖ := Complex.abs_re_le_norm _
        have h2 := hn i
        have h3 : (u i ^ n - 1).re = (u i ^ n).re - 1 := by
          rw [Complex.sub_re, Complex.one_re]
        rw [h3] at h1
        have h4 := (abs_le.mp h1).1
        linarith
      have hpow : (w i ^ n).re = R ^ n * (u i ^ n).re := by
        rw [hwi, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
      rw [hpow]
      have hmi := hm i
      nlinarith [mul_nonneg (mul_pos hRn hmi).le (sub_nonneg.mpr hre_u)]
    · rw [if_neg h, if_neg h, zero_sub]
      have h1 : -‖w i ^ n‖ ≤ (w i ^ n).re := (abs_le.mp (Complex.abs_re_le_norm _)).1
      rw [norm_pow] at h1
      have h2 : R ^ n * (‖w i‖ / R) ^ n = ‖w i‖ ^ n := by
        rw [← mul_pow, mul_div_cancel₀ _ hR0.ne']
      have h3 : R ^ n * -(m i * (‖w i‖ / R) ^ n) = -(m i * ‖w i‖ ^ n) := by
        rw [← h2]
        ring
      rw [h3]
      have h4 := mul_le_mul_of_nonneg_left h1 (hm i).le
      linarith
  have hsum_ge : R ^ n * ((∑ i, if ‖w i‖ = R then m i / 2 else 0)
        - ∑ i, if ‖w i‖ = R then (0 : ℝ) else m i * (‖w i‖ / R) ^ n)
      ≤ ∑ i, m i * (w i ^ n).re := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hS : m i₀ / 2 ≤ ∑ i, if ‖w i‖ = R then m i / 2 else 0 := by
    have hnn : ∀ i ∈ (Finset.univ : Finset ι), (0 : ℝ) ≤ if ‖w i‖ = R then m i / 2 else 0 := by
      intro i _
      split_ifs
      · exact (half_pos (hm i)).le
      · exact le_rfl
    have h := Finset.single_le_sum hnn (Finset.mem_univ i₀)
    rwa [if_pos hi₀] at h
  have hC : C < R ^ n * (m i₀ / 4) := by
    have h := (div_lt_iff₀ (hm i₀)).mp hR_n
    have h' : R ^ n * (m i₀ / 4) = R ^ n * m i₀ / 4 := by ring
    rw [h']
    linarith
  have hbr : m i₀ / 4 ≤ (∑ i, if ‖w i‖ = R then m i / 2 else 0)
        - ∑ i, if ‖w i‖ = R then (0 : ℝ) else m i * (‖w i‖ / R) ^ n := by
    linarith
  rw [count_re]
  exact lt_of_lt_of_le hC ((mul_le_mul_of_nonneg_left hbr hRn.le).trans hsum_ge)

/-! ### L3: the count criterion -/

/-- [proved-derived; formal-checked] Modes in the closed disc keep the counts inside their bound,
the total weight. -/
theorem norm_count_le (m : ι → ℝ) (w : ι → ℂ) (hm : ∀ i, 0 ≤ m i) (hw : ∀ i, ‖w i‖ ≤ 1)
    (n : ℕ) : ‖count m w n‖ ≤ ∑ i, m i := by
  unfold count
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm i), norm_pow]
  exact mul_le_of_le_one_right (hm i) (pow_le_one₀ (norm_nonneg _) (hw i))

/-- [proved-derived; formal-checked] If the real parts of the counts stay under the total weight at
every length `n ≥ 1`, every mode is in the closed disc. No reversal is assumed. -/
theorem norm_le_one_of_re_count_le (m : ι → ℝ) (w : ι → ℂ) (hm : ∀ i, 0 < m i)
    (h : ∀ n : ℕ, 1 ≤ n → (count m w n).re ≤ ∑ i, m i) : ∀ i, ‖w i‖ ≤ 1 := by
  intro j
  by_contra hj
  obtain ⟨n, hn1, hn⟩ := exists_re_count_gt m hm w (not_le.mp hj) (∑ i, m i)
  exact absurd (h n hn1) (not_le.mpr hn)

/-- [proved-derived; formal-checked] With no reversal assumed: the counts stay inside the total
weight at every length if and only if every mode is in the closed disc. -/
theorem count_bounded_iff_norm_le_one (m : ι → ℝ) (w : ι → ℂ) (hm : ∀ i, 0 < m i) :
    (∀ n : ℕ, ‖count m w n‖ ≤ ∑ i, m i) ↔ ∀ i, ‖w i‖ ≤ 1 := by
  constructor
  · intro h
    exact norm_le_one_of_re_count_le m w hm fun n _ =>
      (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans (h n)
  · intro h n
    exact norm_count_le m w (fun i => (hm i).le) h n

omit [Fintype ι] in
/-- The reversal's partner of a mode has the inverse modulus. -/
theorem norm_reversal {w : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, w (σ i) = (conj (w i))⁻¹) (i : ι) :
    ‖w (σ i)‖ = ‖w i‖⁻¹ := by
  rw [hσ, norm_inv, RCLike.norm_conj]

/-- [proved-derived; formal-checked] With the reversal, a mode off the circle on either side is
heard: the real part of the count passes every bound at some length `n ≥ 1`. -/
theorem exists_re_count_gt_of_norm_ne_one (m : ι → ℝ) (w : ι → ℂ) (hm : ∀ i, 0 < m i)
    (σ : ι → ι) (hw0 : ∀ i, w i ≠ 0) (hσ : ∀ i, w (σ i) = (conj (w i))⁻¹) {j : ι}
    (hj : ‖w j‖ ≠ 1) (C : ℝ) : ∃ n : ℕ, 1 ≤ n ∧ C < (count m w n).re := by
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · have hpos : 0 < ‖w j‖ := norm_pos_iff.mpr (hw0 j)
    have hσj : 1 < ‖w (σ j)‖ := by
      rw [norm_reversal hσ j]
      exact (one_lt_inv₀ hpos).mpr hlt
    exact exists_re_count_gt m hm w hσj C
  · exact exists_re_count_gt m hm w hgt C

/-- [proved-derived; formal-checked] With the reversal, counts whose real parts stay under the
total weight at every length `n ≥ 1` put every mode on the circle. -/
theorem norm_eq_one_of_re_count_le (m : ι → ℝ) (w : ι → ℂ) (hm : ∀ i, 0 < m i)
    (σ : ι → ι) (hw0 : ∀ i, w i ≠ 0) (hσ : ∀ i, w (σ i) = (conj (w i))⁻¹)
    (h : ∀ n : ℕ, 1 ≤ n → (count m w n).re ≤ ∑ i, m i) : ∀ i, ‖w i‖ = 1 := by
  intro j
  by_contra hj
  obtain ⟨n, hn1, hn⟩ := exists_re_count_gt_of_norm_ne_one m w hm σ hw0 hσ hj (∑ i, m i)
  exact absurd (h n hn1) (not_le.mpr hn)

/-- [proved-derived; formal-checked] **L3, the count criterion.** For a finite family of nonzero
modes closed under the circle's reversal, with positive weights: every mode is on the circle, if
and only if the counts stay inside the total weight at every length, if and only if the Li numbers
have nonnegative real part at every `n ≥ 1`. -/
theorem count_criterion_tfae (m : ι → ℝ) (w : ι → ℂ) (hm : ∀ i, 0 < m i)
    (σ : ι → ι) (hw0 : ∀ i, w i ≠ 0) (hσ : ∀ i, w (σ i) = (conj (w i))⁻¹) :
    List.TFAE [∀ i, ‖w i‖ = 1,
      ∀ n : ℕ, ‖count m w n‖ ≤ ∑ i, m i,
      ∀ n : ℕ, 1 ≤ n → 0 ≤ (li m w n).re] := by
  tfae_have 1 → 2 := fun h n =>
    norm_count_le m w (fun i => (hm i).le) (fun i => (h i).le) n
  tfae_have 1 → 3 := by
    intro h n _
    rw [li_re]
    have h1 := norm_count_le m w (fun i => (hm i).le) (fun i => (h i).le) n
    have h2 : (count m w n).re ≤ ‖count m w n‖ :=
      le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    linarith
  tfae_have 2 → 1 := fun h =>
    norm_eq_one_of_re_count_le m w hm σ hw0 hσ fun n _ =>
      (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans (h n)
  tfae_have 3 → 1 := by
    intro h
    refine norm_eq_one_of_re_count_le m w hm σ hw0 hσ fun n hn => ?_
    have h1 := h n hn
    rw [li_re] at h1
    linarith
  tfae_finish

/-- [proved-derived; formal-checked] The count reading of L3: every mode is on the circle if and
only if the counts stay inside the total weight at every length. -/
theorem norm_eq_one_iff_count_bounded (m : ι → ℝ) (w : ι → ℂ) (hm : ∀ i, 0 < m i)
    (σ : ι → ι) (hw0 : ∀ i, w i ≠ 0) (hσ : ∀ i, w (σ i) = (conj (w i))⁻¹) :
    (∀ i, ‖w i‖ = 1) ↔ ∀ n : ℕ, ‖count m w n‖ ≤ ∑ i, m i :=
  (count_criterion_tfae m w hm σ hw0 hσ).out 0 1

/-- [proved-derived; formal-checked] The Li reading of L3: every mode is on the circle if and only
if the Li numbers have nonnegative real part at every `n ≥ 1`. -/
theorem norm_eq_one_iff_li_nonneg (m : ι → ℝ) (w : ι → ℂ) (hm : ∀ i, 0 < m i)
    (σ : ι → ι) (hw0 : ∀ i, w i ≠ 0) (hσ : ∀ i, w (σ i) = (conj (w i))⁻¹) :
    (∀ i, ‖w i‖ = 1) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ (li m w n).re :=
  (count_criterion_tfae m w hm σ hw0 hσ).out 0 2

/-! ### L4: the scaled chart, the regular complex's count -/

/-- [proved-derived; formal-checked] **L4, the scaled chart.** For `q > 0` and nonzero modes
closed under `α ↦ q / conj α`, with positive weights: the counts stay within
`(∑ i, m i) * q ^ (l / 2)` at every length `l` if and only if every mode has `normSq (α i) = q`.
This is the count bound of a finite complex with `q + 1` contacts a cell together with its
converse. -/
theorem count_bound_iff_normSq (m : ι → ℝ) (hm : ∀ i, 0 < m i) {q : ℝ} (hq : 0 < q)
    (α : ι → ℂ) (σ : ι → ι) (hα0 : ∀ i, α i ≠ 0)
    (hσ : ∀ i, α (σ i) = (q : ℂ) / conj (α i)) :
    (∀ l : ℕ, ‖count m α l‖ ≤ (∑ i, m i) * q ^ ((l : ℝ) / 2))
      ↔ ∀ i, Complex.normSq (α i) = q := by
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt q := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hsdef]
    exact Real.sqrt_pos.mpr hq
  have hss : s * s = q := by
    rw [hsdef]
    exact Real.mul_self_sqrt hq.le
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hqc : (q : ℂ) = (s : ℂ) * (s : ℂ) := by
    rw [← Complex.ofReal_mul, hss]
  -- the modes in the circle's chart
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
  have hpow : ∀ l : ℕ, q ^ ((l : ℝ) / 2) = s ^ l := by
    intro l
    rw [hsdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    congr 1
    ring
  have hcount : ∀ l : ℕ, ‖count m w l‖ = ‖count m α l‖ / s ^ l := by
    intro l
    have h : count m w l = count m α l / (s : ℂ) ^ l := by
      unfold count
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hwdef, div_pow, mul_div_assoc]
    rw [h, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hnorm : ∀ i, ‖w i‖ = 1 ↔ Complex.normSq (α i) = q := by
    intro i
    rw [hwdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
      div_eq_one_iff_eq hs.ne', Complex.normSq_eq_norm_sq]
    constructor
    · intro h
      rw [h, hsdef]
      exact Real.sq_sqrt hq.le
    · intro h
      rw [hsdef, ← h]
      exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hcrit := norm_eq_one_iff_count_bounded m w hm σ hw0 hσw
  constructor
  · intro h i
    refine (hnorm i).mp (hcrit.mpr (fun l => ?_) i)
    rw [hcount, div_le_iff₀ (pow_pos hs l), ← hpow]
    exact h l
  · intro h l
    have h1 := hcrit.mp (fun i => (hnorm i).mpr (h i)) l
    rw [hcount, div_le_iff₀ (pow_pos hs l), ← hpow] at h1
    exact h1

/-! ### L5: the line chart, Li's form -/

/-- [proved-derived; formal-checked] The chart from the line to the circle: `1 − 1/ρ` has modulus
one if and only if `ρ` has real part one half. -/
theorem cayley_norm_eq_one_iff {ρ : ℂ} (h0 : ρ ≠ 0) : ‖1 - 1 / ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have h1 : 1 - 1 / ρ = (ρ - 1) / ρ := by
    field_simp
  have hpos : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have key : ‖ρ - 1‖ = ‖ρ‖ ↔ Complex.normSq (ρ - 1) = Complex.normSq ρ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    constructor
    · intro h
      rw [h]
    · intro h
      have h' := congrArg Real.sqrt h
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h'
  rw [h1, norm_div, div_eq_one_iff_eq hpos, key, Complex.normSq_apply, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  constructor <;> intro h <;> nlinarith

/-- [proved-derived; formal-checked] The chart carries the line's reversal `ρ ↦ 1 − conj ρ` to the
circle's reversal `w ↦ 1 / conj w`; stated on `c = conj ρ`. -/
theorem cayley_reversal {c : ℂ} (h0 : c ≠ 0) (h1 : c ≠ 1) :
    1 - 1 / (1 - c) = (1 - 1 / c)⁻¹ := by
  have h1' : (1 : ℂ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h2 : c - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h3 : (1 : ℂ) - 1 / c = (c - 1) / c := by
    field_simp
  have h4 : c / (c - 1) = -c / (1 - c) := by
    rw [div_eq_div_iff h2 h1']
    ring
  have h5 : 1 - 1 / (1 - c) = -c / (1 - c) := by
    rw [eq_div_iff h1', sub_mul, one_mul, one_div_mul_cancel h1']
    ring
  rw [h3, inv_div, h4, h5]

/-- [definition] The Li number of a weighted family of modes in the line's chart. -/
def liLine (m : ι → ℝ) (ρ : ι → ℂ) (n : ℕ) : ℂ := ∑ i, (m i : ℂ) * (1 - (1 - 1 / ρ i) ^ n)

/-- [proved-derived; formal-checked] The line's Li numbers are the circle's at `w = 1 − 1/ρ`. -/
theorem liLine_eq_li (m : ι → ℝ) (ρ : ι → ℂ) (n : ℕ) :
    liLine m ρ n = li m (fun i => 1 - 1 / ρ i) n := rfl

/-- [proved-derived; formal-checked] **L5, the finite Li criterion.** For a finite family of modes
`ρ i ≠ 0, 1` closed under the line's reversal `ρ ↦ 1 − conj ρ`, with positive weights: the Li
numbers have nonnegative real part at every `n ≥ 1` if and only if every mode has real part one
half. -/
theorem li_line_criterion (m : ι → ℝ) (hm : ∀ i, 0 < m i) (ρ : ι → ℂ) (σ : ι → ι)
    (hρ0 : ∀ i, ρ i ≠ 0) (hρ1 : ∀ i, ρ i ≠ 1) (hσ : ∀ i, ρ (σ i) = 1 - conj (ρ i)) :
    (∀ n : ℕ, 1 ≤ n → 0 ≤ (liLine m ρ n).re) ↔ ∀ i, (ρ i).re = 1 / 2 := by
  have hw0 : ∀ i, (fun i => 1 - 1 / ρ i) i ≠ 0 := by
    intro i
    have h : 1 - 1 / ρ i = (ρ i - 1) / ρ i := by
      have := hρ0 i
      field_simp
    show 1 - 1 / ρ i ≠ 0
    rw [h]
    exact div_ne_zero (sub_ne_zero.mpr (hρ1 i)) (hρ0 i)
  have hσw : ∀ i, (fun i => 1 - 1 / ρ i) (σ i) = (conj ((fun i => 1 - 1 / ρ i) i))⁻¹ := by
    intro i
    have hc0 : conj (ρ i) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr (hρ0 i)
    have hc1 : conj (ρ i) ≠ 1 := by
      intro h
      apply hρ1 i
      have h' := congrArg (starRingEnd ℂ) h
      rwa [Complex.conj_conj, map_one] at h'
    show 1 - 1 / ρ (σ i) = (conj (1 - 1 / ρ i))⁻¹
    rw [hσ, map_sub, map_one, map_div₀, map_one]
    exact cayley_reversal hc0 hc1
  have hcrit := norm_eq_one_iff_li_nonneg m (fun i => 1 - 1 / ρ i) hm σ hw0 hσw
  constructor
  · intro h i
    exact (cayley_norm_eq_one_iff (hρ0 i)).mp (hcrit.mpr h i)
  · intro h
    exact hcrit.mp fun i => (cayley_norm_eq_one_iff (hρ0 i)).mpr (h i)

section Audit

#print axioms exists_pow_near_one
#print axioms exists_re_count_gt
#print axioms norm_count_le
#print axioms norm_le_one_of_re_count_le
#print axioms count_bounded_iff_norm_le_one
#print axioms exists_re_count_gt_of_norm_ne_one
#print axioms count_criterion_tfae
#print axioms norm_eq_one_iff_count_bounded
#print axioms norm_eq_one_iff_li_nonneg
#print axioms count_bound_iff_normSq
#print axioms cayley_norm_eq_one_iff
#print axioms cayley_reversal
#print axioms li_line_criterion

end Audit

end Holonics.Zeta.FiniteLiCriterion
