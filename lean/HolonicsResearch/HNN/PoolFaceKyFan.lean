import HolonicsResearch.HNN.EffectiveTension

/-!
# The best pool face removes the leading generalized eigenvalues: Ky Fan's maximum principle

The record `research/records/2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT.md`
(§6 and §8) founds a face from a pool: with the face's tension `S`, the pool's cross remainder
`M = K − B H⁺ L` and its own remainder `Q = C − Lᵀ H⁺ L`, a face `Wᵀ c` read from the pool removes
`M W (Wᵀ Q W)⁺ Wᵀ Mᵀ` (`EffectiveTension.tension_fromRows_pool`), and the best rank-`k` face
removes the sum of the `k` leading generalized eigenvalues of `(Mᵀ M, Q)`. #410's box "The effective
tension at a contact" left that last clause owed as a Ky Fan maximum principle, which Mathlib does not
hold; this file proves it.

[proved-standard; formal-checked] What is proved.

1. **Weights in the unit interval** (`sum_mul_le_of_separated`). If `0 ≤ w_i ≤ 1`, `Σ w_i = |t|`
   and every value inside `t` is at least every value outside it, then `Σ λ_i w_i ≤ Σ_(i∈t) λ_i`.
   The proof is one inequality: `(1_t(i) − w_i)(λ_i − τ) ≥ 0` at every `i` for a threshold `τ`
   between the two sides, and its sum is `Σ_t λ − Σ λ w`.
2. **Ky Fan's maximum principle** (`trace_le_leadingSum`, `exists_trace_eq_leadingSum`,
   `isGreatest_trace`). For a real symmetric `A` with eigenvalues `λ₀ ≥ λ₁ ≥ …` (Mathlib's
   `eigenvalues₀`, sorted), every `W` with orthonormal columns (`Wᵀ W = 1`, `k` columns) has
   `tr(Wᵀ A W) ≤ λ₀ + … + λ_(k−1)` (`leadingSum`), and the top `k` eigenvectors attain it. In the
   eigenbasis, `tr(Wᵀ A W) = Σ_i λ_i w_i` with `w_i = Σ_j (Uᵀ W)_ij²` (`trace_eq_sum_weights`),
   `Σ w_i = k` and `w_i ≤ 1` because `(UᵀW)(UᵀW)ᵀ` is an orthogonal projection
   (`weight_le_one`), so item 1 closes it.
3. **The generalized pencil** (`reduced`, `det_sub_smul`, `reduced_eigen`, `trace_le_gen`,
   `exists_trace_eq_gen`). For `Q ≻ 0` with its square root `R` (`sqrtPD`, `R R = Q`, `Rᵀ = R`)
   and `R⁻¹` (`invSqrtPD`), the generalized eigenvalues of `(B, Q)` are the eigenvalues of
   `R⁻¹ B R⁻¹`: `det(B − λQ) = det Q · det(R⁻¹ B R⁻¹ − λ)`, and `R⁻¹ B R⁻¹ v = λ v` exactly when
   `B (R⁻¹ v) = λ Q (R⁻¹ v)`. Every `W` normalized on the pool, `Wᵀ Q W = 1`, has
   `tr(Wᵀ B W)` at most the sum of the `k` leading ones, and some `W` attains it.
4. **The best pool face** (`removal_eq_trace`, `pool_face_removal_le`,
   `exists_pool_face_removal_eq`). With `B = Mᵀ M`, a face `Wᵀ c` normalized on the pool's own
   remainder removes a tension whose trace is `tr(Wᵀ Mᵀ M W)`, so no rank-`k` pool face removes more
   than the sum of the `k` leading generalized eigenvalues of `(Mᵀ M, Q)`, and the leading
   generalized eigenvectors remove exactly that, whatever generalized inverse the joint Gram takes.
   All `d` of them sum to `tr(M Q⁻¹ Mᵀ)`, what the whole pool removes (`leadingSum_card`,
   `trace_reduced`, `whole_pool_sum`).

Limits. The removal is read by its trace (the record's "sum of the eigenvalues"); the Loewner order
of the removed blocks is not compared. `Q` is positive definite: a pool whose remainder is singular
is read on the range of `Q`, which is not built. The normalization `Wᵀ Q W = 1` is the record's; any
rank-`k` face is a rebase of a normalized one (`EffectiveTension.tension_rebase`), which is not
restated here.

The computational object is the helical pair interaction: the pool's faces meet the covector at a
pair contact, and the face founded is the one whose contact carries the most of what the present
face leaves. Of the winding guide's six general objects this touches faces and placement (which
face is founded) and the tower thread (the covector a level carries back); the helix, the pair,
the cell holonomy and the tube stay attached.

Consumers: the atlas rows `contact.pool-founding`, `contact.tension-founds-face` and
`contact.effective-tension`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

open Matrix

namespace Holonics.HNN.PoolFaceKyFan

/-! ## 1. Weights in the unit interval -/

/-- [proved-standard; formal-checked] **Weights in the unit interval.** If the weights lie in
`[0, 1]` and sum to `|t|`, and every value in `t` is at least every value outside it, the weighted
sum is at most the sum over `t`. -/
theorem sum_mul_le_of_separated {ι : Type*} [Fintype ι] [DecidableEq ι] (lam wt : ι → ℝ)
    (t : Finset ι) (hsep : ∀ i ∈ t, ∀ j ∉ t, lam j ≤ lam i) (h0 : ∀ i, 0 ≤ wt i)
    (h1 : ∀ i, wt i ≤ 1) (hsum : ∑ i, wt i = t.card) :
    ∑ i, lam i * wt i ≤ ∑ i ∈ t, lam i := by
  obtain ⟨τ, hτt, hτc⟩ : ∃ τ, (∀ i ∈ t, τ ≤ lam i) ∧ (∀ j ∉ t, lam j ≤ τ) := by
    by_cases ht : t.Nonempty
    · refine ⟨t.inf' ht lam, fun i hi => Finset.inf'_le _ hi, fun j hj => ?_⟩
      exact (Finset.le_inf'_iff ht lam).2 fun i hi => hsep i hi j hj
    · refine ⟨∑ i, |lam i|, fun i hi => (ht ⟨i, hi⟩).elim, fun j _ => ?_⟩
      exact (le_abs_self _).trans
        (Finset.single_le_sum (fun i _ => abs_nonneg (lam i)) (Finset.mem_univ j))
  have key : ∀ i, 0 ≤ ((if i ∈ t then 1 else 0) - wt i) * (lam i - τ) := by
    intro i
    by_cases hi : i ∈ t
    · simp only [hi, if_true]
      exact mul_nonneg (by linarith [h1 i]) (by linarith [hτt i hi])
    · simp only [hi, if_false]
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith [h0 i]) (by linarith [hτc i hi])
  have hS : 0 ≤ ∑ i, ((if i ∈ t then 1 else 0) - wt i) * (lam i - τ) :=
    Finset.sum_nonneg fun i _ => key i
  have hpt : ∀ i, ((if i ∈ t then 1 else 0) - wt i) * (lam i - τ) =
      (if i ∈ t then lam i else 0) - lam i * wt i - τ * (if i ∈ t then 1 else 0) + τ * wt i := by
    intro i
    split_ifs <;> ring
  have hind : ∑ i, (if i ∈ t then (1 : ℝ) else 0) = t.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hlt : ∑ i, (if i ∈ t then lam i else 0) = ∑ i ∈ t, lam i := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hlt, hind, hsum] at hS
  linarith

/-! ## 2. Ky Fan's maximum principle -/

section KyFan

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]

/-- [definition] The sum of the `k` leading eigenvalues of a symmetric matrix, read on Mathlib's
sorted eigenvalues `λ₀ ≥ λ₁ ≥ …`. -/
def leadingSum {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => (i : ℕ) < k), hA.eigenvalues₀ i

/-- [definition] The index map that `IsHermitian.eigenvalues` reads its sorted eigenvalues through. -/
def sortEquiv (n : Type*) [Fintype n] : Fin (Fintype.card n) ≃ n :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

/-- [definition] The places of the `k` leading eigenvalues, in the matrix's own index. -/
def leadingSet (n : Type*) [Fintype n] [DecidableEq n] (k : ℕ) : Finset n :=
  Finset.univ.filter fun i => ((sortEquiv n).symm i : ℕ) < k

/-- [proved-standard; formal-checked] Mathlib's eigenvalue at `i` is the sorted one at `i`'s place. -/
theorem eigenvalues_apply {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i = hA.eigenvalues₀ ((sortEquiv n).symm i) := rfl

/-- [proved-standard; formal-checked] The leading set's eigenvalues sum to the leading sum. -/
theorem sum_leadingSet {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    ∑ i ∈ leadingSet n k, hA.eigenvalues i = leadingSum hA k := by
  rw [leadingSet, leadingSum, Finset.sum_filter, Finset.sum_filter]
  simp_rw [eigenvalues_apply]
  exact Equiv.sum_comp (sortEquiv n).symm
    (fun j : Fin (Fintype.card n) => if (j : ℕ) < k then hA.eigenvalues₀ j else 0)

/-- [proved-standard; formal-checked] The leading set holds `k` places when `k` is at most the
dimension. -/
theorem card_leadingSet {k : ℕ} (hk : k ≤ Fintype.card n) : (leadingSet n k).card = k := by
  have h1 : (leadingSet n k).card =
      (Finset.univ.filter fun j : Fin (Fintype.card n) => (j : ℕ) < k).card := by
    rw [leadingSet]
    refine Finset.card_bij (fun i _ => (sortEquiv n).symm i) ?_ ?_ ?_
    · intro i hi
      simpa using hi
    · intro i _ j _ h
      exact (sortEquiv n).symm.injective h
    · intro j hj
      exact ⟨sortEquiv n j, by simpa using hj, by simp⟩
  have h2 : Finset.univ.filter (fun j : Fin (Fintype.card n) => (j : ℕ) < k) =
      (Finset.range k).attachFin (fun m hm => lt_of_lt_of_le (Finset.mem_range.1 hm) hk) := by
    ext j
    simp [Finset.mem_attachFin]
  rw [h1, h2, Finset.card_attachFin, Finset.card_range]

/-- [proved-standard; formal-checked] All the eigenvalues together sum to the trace. -/
theorem leadingSum_card {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    leadingSum hA (Fintype.card n) = trace A := by
  have h : leadingSet n (Fintype.card n) = Finset.univ := by
    ext i
    simp [leadingSet]
  rw [← sum_leadingSet, h, hA.trace_eq_sum_eigenvalues]
  simp

/-- [proved-standard; formal-checked] Every leading eigenvalue is at least every other one. -/
theorem leadingSet_separated {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    ∀ i ∈ leadingSet n k, ∀ j ∉ leadingSet n k, hA.eigenvalues j ≤ hA.eigenvalues i := by
  intro i hi j hj
  simp only [leadingSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi hj
  rw [eigenvalues_apply, eigenvalues_apply]
  exact hA.eigenvalues₀_antitone (Fin.le_def.2 (by omega))

/-- [definition] The eigenvector matrix `U` of a symmetric matrix. -/
abbrev eigU {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ := (hA.eigenvectorUnitary : _)

/-- [proved-standard; formal-checked] `Uᵀ U = 1`. -/
theorem eigU_transpose_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) : (eigU hA)ᵀ * eigU hA = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- [proved-standard; formal-checked] `U Uᵀ = 1`. -/
theorem eigU_mul_transpose {A : Matrix n n ℝ} (hA : A.IsHermitian) : eigU hA * (eigU hA)ᵀ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- [proved-standard; formal-checked] The spectral theorem over `ℝ`: `A = U diag(λ) Uᵀ`. -/
theorem spectral_real {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A = eigU hA * diagonal hA.eigenvalues * (eigU hA)ᵀ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, Function.id_comp]

omit [DecidableEq κ] in
/-- [proved-standard; formal-checked] `tr(Vᵀ diag(d) V) = Σ_i d_i Σ_j V_ij²`. -/
theorem trace_transpose_diagonal_mul (V : Matrix n κ ℝ) (d : n → ℝ) :
    trace (Vᵀ * diagonal d * V) = ∑ i, d i * ∑ j, V i j ^ 2 := by
  have h : ∀ j, (Vᵀ * diagonal d * V) j j = ∑ i, d i * V i j ^ 2 := by
    intro j
    rw [mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_diagonal, transpose_apply]
    ring
  simp only [trace, diag, h]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- [definition] The weight `w_i = Σ_j (Uᵀ W)_ij²` a frame `W` puts on the eigenvector `i`. -/
def weight {A : Matrix n n ℝ} (hA : A.IsHermitian) (W : Matrix n κ ℝ) (i : n) : ℝ :=
  ∑ j, ((eigU hA)ᵀ * W) i j ^ 2

omit [DecidableEq κ] in
/-- [proved-standard; formal-checked] In the eigenbasis, `tr(Wᵀ A W) = Σ_i λ_i w_i`. -/
theorem trace_eq_sum_weights {A : Matrix n n ℝ} (hA : A.IsHermitian) (W : Matrix n κ ℝ) :
    trace (Wᵀ * A * W) = ∑ i, hA.eigenvalues i * weight hA W i := by
  have h : Wᵀ * A * W = ((eigU hA)ᵀ * W)ᵀ * diagonal hA.eigenvalues * ((eigU hA)ᵀ * W) := by
    conv_lhs => rw [spectral_real hA]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [h, trace_transpose_diagonal_mul]
  rfl

omit [DecidableEq κ] in
/-- [proved-standard; formal-checked] A weight is nonnegative. -/
theorem weight_nonneg {A : Matrix n n ℝ} (hA : A.IsHermitian) (W : Matrix n κ ℝ) (i : n) :
    0 ≤ weight hA W i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- [proved-standard; formal-checked] The weights of an orthonormal frame sum to its rank. -/
theorem sum_weight {A : Matrix n n ℝ} (hA : A.IsHermitian) {W : Matrix n κ ℝ} (hW : Wᵀ * W = 1) :
    ∑ i, weight hA W i = Fintype.card κ := by
  set V := (eigU hA)ᵀ * W with hV
  have hVV : Vᵀ * V = 1 := by
    rw [hV, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (eigU hA),
      eigU_mul_transpose, Matrix.one_mul, hW]
  have h : ∀ j, ∑ i, V i j ^ 2 = 1 := by
    intro j
    have := congrFun (congrFun hVV j) j
    rw [mul_apply, one_apply_eq] at this
    simpa [transpose_apply, sq] using this
  unfold weight
  rw [← hV, Finset.sum_comm]
  simp [h]

/-- [proved-standard; formal-checked] **A weight is at most one**: `(UᵀW)(UᵀW)ᵀ` is an orthogonal
projection, so its diagonal entry `w_i` satisfies `w_i = Σ_l P_il² ≥ w_i²`. -/
theorem weight_le_one {A : Matrix n n ℝ} (hA : A.IsHermitian) {W : Matrix n κ ℝ}
    (hW : Wᵀ * W = 1) (i : n) : weight hA W i ≤ 1 := by
  set V := (eigU hA)ᵀ * W with hV
  have hVV : Vᵀ * V = 1 := by
    rw [hV, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (eigU hA),
      eigU_mul_transpose, Matrix.one_mul, hW]
  set P := V * Vᵀ with hP
  have hPP : P * P = P := by
    rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hVV, Matrix.one_mul]
  have hPt : Pᵀ = P := by rw [hP, transpose_mul, transpose_transpose]
  have hw : weight hA W i = P i i := by
    rw [weight, ← hV, hP, mul_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [transpose_apply, sq]
  have hsq : P i i ^ 2 ≤ P i i := by
    have h1 : P i i = ∑ l, P i l ^ 2 := by
      conv_lhs => rw [← hPP]
      rw [mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      have : P l i = P i l := by rw [← transpose_apply P i l, hPt]
      rw [this, sq]
    calc P i i ^ 2 ≤ ∑ l, P i l ^ 2 :=
          Finset.single_le_sum (f := fun l => P i l ^ 2) (fun l _ => sq_nonneg _)
            (Finset.mem_univ i)
      _ = P i i := h1.symm
  have h0 : 0 ≤ P i i := hw ▸ weight_nonneg hA W i
  rw [hw]
  nlinarith

/-- [proved-standard; formal-checked] **Ky Fan's maximum principle, the bound**: an orthonormal frame
of `k` columns reads at most the sum of the `k` leading eigenvalues. -/
theorem trace_le_leadingSum {A : Matrix n n ℝ} (hA : A.IsHermitian) {W : Matrix n κ ℝ}
    (hW : Wᵀ * W = 1) : trace (Wᵀ * A * W) ≤ leadingSum hA (Fintype.card κ) := by
  have hk : Fintype.card κ ≤ Fintype.card n := by
    have h := sum_weight hA hW
    have : ∑ i, weight hA W i ≤ ∑ _i : n, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => weight_le_one hA hW i
    rw [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    exact_mod_cast this
  rw [trace_eq_sum_weights, ← sum_leadingSet]
  refine sum_mul_le_of_separated _ _ _ (leadingSet_separated hA _) (weight_nonneg hA W)
    (weight_le_one hA hW) ?_
  rw [sum_weight hA hW, card_leadingSet hk]

/-- [proved-standard; formal-checked] **Ky Fan's maximum principle, attained**: the top `k`
eigenvectors form an orthonormal frame that reads the sum of the `k` leading eigenvalues. -/
theorem exists_trace_eq_leadingSum {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hk : Fintype.card κ ≤ Fintype.card n) :
    ∃ W : Matrix n κ ℝ, Wᵀ * W = 1 ∧ trace (Wᵀ * A * W) = leadingSum hA (Fintype.card κ) := by
  set t := leadingSet n (Fintype.card κ)
  have hct : Fintype.card κ = Fintype.card t := by
    rw [Fintype.card_coe, card_leadingSet hk]
  let σ : κ ≃ t := Fintype.equivOfCardEq hct
  let E : Matrix n κ ℝ := Matrix.of fun i j => if i = (σ j : n) then 1 else 0
  have hE : ∀ i j, E i j = if i = (σ j : n) then 1 else 0 := fun _ _ => rfl
  have hEE : Eᵀ * E = 1 := by
    ext j j'
    rw [mul_apply, one_apply]
    simp only [transpose_apply, hE]
    by_cases h : j = j'
    · subst h
      rw [Finset.sum_eq_single (σ j : n)]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h1 : i = (σ j : n)
      · have h2 : i ≠ (σ j' : n) := by
          rw [h1]; intro h3; exact h (σ.injective (Subtype.ext h3))
        simp [h2]
      · simp [h1]
  refine ⟨eigU hA * E, ?_, ?_⟩
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (eigU hA)ᵀ, eigU_transpose_mul,
      Matrix.one_mul, hEE]
  · rw [trace_eq_sum_weights, ← sum_leadingSet]
    have hw : ∀ i, weight hA (eigU hA * E) i = if i ∈ t then 1 else 0 := by
      intro i
      rw [weight, ← Matrix.mul_assoc, eigU_transpose_mul, Matrix.one_mul]
      simp only [hE]
      by_cases hi : i ∈ t
      · rw [if_pos hi]
        rw [Finset.sum_eq_single (σ.symm ⟨i, hi⟩)]
        · simp
        · intro b _ hb
          have : i ≠ (σ b : n) := by
            intro h; apply hb; apply σ.injective; rw [Equiv.apply_symm_apply]; exact Subtype.ext h.symm
          simp [this]
        · simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun j _ => ?_
        have : i ≠ (σ j : n) := fun h => hi (h ▸ (σ j).2)
        simp [this]
    simp_rw [hw, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- [proved-standard; formal-checked] **Ky Fan's maximum principle**: the sum of the `k` leading
eigenvalues is the greatest trace an orthonormal frame of `k` columns reads. -/
theorem isGreatest_trace {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hk : Fintype.card κ ≤ Fintype.card n) :
    IsGreatest {r | ∃ W : Matrix n κ ℝ, Wᵀ * W = 1 ∧ r = trace (Wᵀ * A * W)}
      (leadingSum hA (Fintype.card κ)) := by
  obtain ⟨W, hW, he⟩ := exists_trace_eq_leadingSum (κ := κ) hA hk
  exact ⟨⟨W, hW, he.symm⟩, fun r ⟨W', hW', hr⟩ => hr ▸ trace_le_leadingSum hA hW'⟩

end KyFan

/-! ## 3. The generalized pencil -/

section Pencil

variable {m κ : Type*} [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

/-- [proved-standard; formal-checked] Two functions of one symmetric matrix multiply by their
diagonals: `U diag(a) Uᵀ · U diag(b) Uᵀ = U diag(ab) Uᵀ`. -/
theorem conj_mul_conj {A : Matrix m m ℝ} (hA : A.IsHermitian) (a b : m → ℝ) :
    eigU hA * diagonal a * (eigU hA)ᵀ * (eigU hA * diagonal b * (eigU hA)ᵀ) =
      eigU hA * diagonal (fun i => a i * b i) * (eigU hA)ᵀ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (eigU hA)ᵀ (eigU hA), eigU_transpose_mul, Matrix.one_mul,
    ← Matrix.mul_assoc (diagonal a), diagonal_mul_diagonal]

/-- [proved-standard; formal-checked] A function of a symmetric matrix is symmetric. -/
theorem conj_transpose_self {A : Matrix m m ℝ} (hA : A.IsHermitian) (a : m → ℝ) :
    (eigU hA * diagonal a * (eigU hA)ᵀ)ᵀ = eigU hA * diagonal a * (eigU hA)ᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

variable {Q : Matrix m m ℝ} (hQ : Q.PosDef)

/-- [definition] The square root `R = U diag(√μ) Uᵀ` of a positive definite `Q`. -/
def sqrtPD : Matrix m m ℝ :=
  eigU hQ.isHermitian * diagonal (fun i => √(hQ.isHermitian.eigenvalues i)) * (eigU hQ.isHermitian)ᵀ

/-- [definition] Its inverse `R⁻¹ = U diag(1/√μ) Uᵀ`. -/
def invSqrtPD : Matrix m m ℝ :=
  eigU hQ.isHermitian * diagonal (fun i => (√(hQ.isHermitian.eigenvalues i))⁻¹) *
    (eigU hQ.isHermitian)ᵀ

/-- [proved-standard; formal-checked] `R R = Q`. -/
theorem sqrtPD_mul_self : sqrtPD hQ * sqrtPD hQ = Q := by
  have h : (fun i => √(hQ.isHermitian.eigenvalues i) * √(hQ.isHermitian.eigenvalues i)) =
      hQ.isHermitian.eigenvalues :=
    funext fun i => Real.mul_self_sqrt (hQ.eigenvalues_pos i).le
  rw [sqrtPD, conj_mul_conj, h, ← spectral_real]

/-- [proved-standard; formal-checked] `Rᵀ = R`. -/
theorem sqrtPD_transpose : (sqrtPD hQ)ᵀ = sqrtPD hQ := conj_transpose_self _ _

/-- [proved-standard; formal-checked] `(R⁻¹)ᵀ = R⁻¹`. -/
theorem invSqrtPD_transpose : (invSqrtPD hQ)ᵀ = invSqrtPD hQ := conj_transpose_self _ _

/-- [proved-standard; formal-checked] `R R⁻¹ = 1`. -/
theorem sqrtPD_mul_inv : sqrtPD hQ * invSqrtPD hQ = 1 := by
  rw [sqrtPD, invSqrtPD, conj_mul_conj]
  have : (fun i => √(hQ.isHermitian.eigenvalues i) * (√(hQ.isHermitian.eigenvalues i))⁻¹) =
      fun _ => (1 : ℝ) := by
    ext i
    exact mul_inv_cancel₀ (Real.sqrt_pos.2 (hQ.eigenvalues_pos i)).ne'
  rw [this, diagonal_one, Matrix.mul_one, eigU_mul_transpose]

/-- [proved-standard; formal-checked] `R⁻¹ R = 1`. -/
theorem invSqrtPD_mul : invSqrtPD hQ * sqrtPD hQ = 1 := by
  rw [sqrtPD, invSqrtPD, conj_mul_conj]
  have : (fun i => (√(hQ.isHermitian.eigenvalues i))⁻¹ * √(hQ.isHermitian.eigenvalues i)) =
      fun _ => (1 : ℝ) := by
    ext i
    exact inv_mul_cancel₀ (Real.sqrt_pos.2 (hQ.eigenvalues_pos i)).ne'
  rw [this, diagonal_one, Matrix.mul_one, eigU_mul_transpose]

/-- [proved-standard; formal-checked] `R⁻¹ R⁻¹ = Q⁻¹`. -/
theorem invSqrtPD_mul_self : invSqrtPD hQ * invSqrtPD hQ = Q⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  calc invSqrtPD hQ * invSqrtPD hQ * Q = invSqrtPD hQ * invSqrtPD hQ * (sqrtPD hQ * sqrtPD hQ) := by
        rw [sqrtPD_mul_self]
    _ = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (invSqrtPD hQ) (sqrtPD hQ) (sqrtPD hQ),
          invSqrtPD_mul, Matrix.one_mul, invSqrtPD_mul]

/-- [definition] The pencil `(B, Q)` reduced to one symmetric matrix, `R⁻¹ B R⁻¹`; its eigenvalues
are the generalized eigenvalues of `(B, Q)`. -/
def reduced (B : Matrix m m ℝ) : Matrix m m ℝ := invSqrtPD hQ * B * invSqrtPD hQ

/-- [proved-standard; formal-checked] The reduced pencil is symmetric. -/
theorem isHermitian_reduced {B : Matrix m m ℝ} (hB : B.IsHermitian) : (reduced hQ B).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, reduced, transpose_mul, transpose_mul,
    invSqrtPD_transpose, ← conjTranspose_eq_transpose_of_trivial B, hB.eq, Matrix.mul_assoc]

/-- [proved-standard; formal-checked] **The generalized characteristic polynomial**:
`det(B − λQ) = det Q · det(R⁻¹ B R⁻¹ − λ)`, so the generalized eigenvalues of `(B, Q)` are the
eigenvalues of the reduced matrix (`det Q > 0`). -/
theorem det_sub_smul (B : Matrix m m ℝ) (lam : ℝ) :
    (B - lam • Q).det = Q.det * (reduced hQ B - lam • 1).det := by
  have h : B - lam • Q = sqrtPD hQ * (reduced hQ B - lam • 1) * sqrtPD hQ := by
    rw [reduced, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      sqrtPD_mul_self, ← Matrix.mul_assoc, ← Matrix.mul_assoc, sqrtPD_mul_inv, Matrix.one_mul,
      Matrix.mul_assoc, invSqrtPD_mul, Matrix.mul_one]
  rw [h]
  calc (sqrtPD hQ * (reduced hQ B - lam • 1) * sqrtPD hQ).det
      = (sqrtPD hQ * sqrtPD hQ).det * (reduced hQ B - lam • 1).det := by
        rw [det_mul, det_mul, det_mul]; ring
    _ = Q.det * (reduced hQ B - lam • 1).det := by rw [sqrtPD_mul_self]

/-- [proved-standard; formal-checked] The generalized eigenvalues sum to `tr(B Q⁻¹)`. -/
theorem trace_reduced (B : Matrix m m ℝ) : trace (reduced hQ B) = trace (B * Q⁻¹) := by
  rw [reduced, trace_mul_comm (invSqrtPD hQ * B), ← Matrix.mul_assoc, invSqrtPD_mul_self,
    trace_mul_comm]

/-- [proved-standard; formal-checked] **Generalized eigenvectors**: `R⁻¹ B R⁻¹ v = λ v` exactly
when `B (R⁻¹ v) = λ Q (R⁻¹ v)`. -/
theorem reduced_eigen (B : Matrix m m ℝ) (lam : ℝ) (v : m → ℝ) :
    reduced hQ B *ᵥ v = lam • v ↔ B *ᵥ (invSqrtPD hQ *ᵥ v) = lam • (Q *ᵥ (invSqrtPD hQ *ᵥ v)) := by
  have hQR : Q * invSqrtPD hQ = sqrtPD hQ := by
    calc Q * invSqrtPD hQ = sqrtPD hQ * sqrtPD hQ * invSqrtPD hQ := by rw [sqrtPD_mul_self]
      _ = sqrtPD hQ := by rw [Matrix.mul_assoc, sqrtPD_mul_inv, Matrix.mul_one]
  have hQv : Q *ᵥ (invSqrtPD hQ *ᵥ v) = sqrtPD hQ *ᵥ v := by
    rw [mulVec_mulVec, hQR]
  rw [hQv]
  constructor
  · intro h
    have : sqrtPD hQ *ᵥ (reduced hQ B *ᵥ v) = B *ᵥ (invSqrtPD hQ *ᵥ v) := by
      rw [reduced, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        sqrtPD_mul_inv, Matrix.one_mul]
    rw [← this, h, mulVec_smul]
  · intro h
    rw [reduced, ← mulVec_mulVec, ← mulVec_mulVec, h, mulVec_smul, mulVec_mulVec, invSqrtPD_mul,
      one_mulVec]

/-- [proved-standard; formal-checked] **The pencil's bound**: a frame normalized on `Q`
(`Wᵀ Q W = 1`, `k` columns) reads `tr(Wᵀ B W)` at most the sum of the `k` leading generalized
eigenvalues of `(B, Q)`. -/
theorem trace_le_gen {B : Matrix m m ℝ} (hB : B.IsHermitian) {W : Matrix m κ ℝ}
    (hW : Wᵀ * Q * W = 1) :
    trace (Wᵀ * B * W) ≤ leadingSum (isHermitian_reduced hQ hB) (Fintype.card κ) := by
  have hV : (sqrtPD hQ * W)ᵀ * (sqrtPD hQ * W) = 1 := by
    rw [transpose_mul, sqrtPD_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (sqrtPD hQ),
      sqrtPD_mul_self, ← Matrix.mul_assoc, hW]
  have h := trace_le_leadingSum (isHermitian_reduced hQ hB) hV
  have he : (sqrtPD hQ * W)ᵀ * reduced hQ B * (sqrtPD hQ * W) = Wᵀ * B * W := by
    rw [transpose_mul, sqrtPD_transpose, reduced]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (sqrtPD hQ) (invSqrtPD hQ), sqrtPD_mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (invSqrtPD hQ) (sqrtPD hQ), invSqrtPD_mul, Matrix.one_mul]
  rwa [he] at h

/-- [proved-standard; formal-checked] **The pencil's bound is attained** by the leading generalized
eigenvectors, normalized on `Q`. -/
theorem exists_trace_eq_gen {B : Matrix m m ℝ} (hB : B.IsHermitian)
    (hk : Fintype.card κ ≤ Fintype.card m) :
    ∃ W : Matrix m κ ℝ, Wᵀ * Q * W = 1 ∧
      trace (Wᵀ * B * W) = leadingSum (isHermitian_reduced hQ hB) (Fintype.card κ) := by
  obtain ⟨V, hV, he⟩ := exists_trace_eq_leadingSum (κ := κ) (isHermitian_reduced hQ hB) hk
  refine ⟨invSqrtPD hQ * V, ?_, ?_⟩
  · have hQR : invSqrtPD hQ * Q * invSqrtPD hQ = 1 := by
      calc invSqrtPD hQ * Q * invSqrtPD hQ =
          invSqrtPD hQ * (sqrtPD hQ * sqrtPD hQ) * invSqrtPD hQ := by rw [sqrtPD_mul_self]
        _ = 1 := by
          rw [← Matrix.mul_assoc, invSqrtPD_mul, Matrix.one_mul, sqrtPD_mul_inv]
    rw [transpose_mul, invSqrtPD_transpose,
      show Vᵀ * invSqrtPD hQ * Q * (invSqrtPD hQ * V) = Vᵀ * (invSqrtPD hQ * Q * invSqrtPD hQ) * V by
        simp only [Matrix.mul_assoc],
      hQR, Matrix.mul_one, hV]
  · rw [← he, reduced, transpose_mul, invSqrtPD_transpose]
    simp only [Matrix.mul_assoc]

end Pencil

/-! ## 4. The best pool face -/

section Pool

open Holonics.HNN.EffectiveTension

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n o m κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype o] [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

omit [Fintype m] [DecidableEq m] in
/-- [proved-standard; formal-checked] `Mᵀ M` is symmetric. -/
theorem isHermitian_gram (M : Matrix o m ℝ) : (Mᵀ * M).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_transpose]

omit [DecidableEq m] in
/-- [proved-standard; formal-checked] **What a normalized pool face removes**: reading `Wᵀ c` with
`Wᵀ Q W = 1` lowers the tension's trace by `tr(Wᵀ Mᵀ M W)`, for every generalized inverse of the
joint face Gram. -/
theorem removal_eq_trace (A : Matrix n ι ℝ) (Cp : Matrix m ι ℝ) (Y : Matrix o ι ℝ) {w : ι → ℝ}
    (hw : ∀ t, 0 ≤ w t) {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) {W : Matrix m κ ℝ}
    (hW : Wᵀ * faceRemainder A Cp w G * W = 1) {G' : Matrix (n ⊕ κ) (n ⊕ κ) ℝ}
    (hG' : IsGInv (moment (fromRows A (Wᵀ * Cp)) (fromRows A (Wᵀ * Cp)) w) G') :
    trace (tension A Y w G - tension (fromRows A (Wᵀ * Cp)) Y w G') =
      trace (Wᵀ * ((crossRemainder A Cp Y w G)ᵀ * crossRemainder A Cp Y w G) * W) := by
  have hGQ : IsGInv (Wᵀ * faceRemainder A Cp w G * W) 1 := by
    rw [IsGInv, hW, Matrix.mul_one, Matrix.mul_one]
  rw [tension_fromRows_pool A Cp W Y hw hG hGQ hG', sub_sub_cancel, Matrix.mul_one,
    trace_mul_comm, transpose_mul]
  simp only [Matrix.mul_assoc]

/-- [proved-standard; formal-checked] **No rank-`k` pool face removes more** than the sum of the `k`
leading generalized eigenvalues of `(Mᵀ M, Q)`. -/
theorem pool_face_removal_le (A : Matrix n ι ℝ) (Cp : Matrix m ι ℝ) (Y : Matrix o ι ℝ)
    {w : ι → ℝ} (hw : ∀ t, 0 ≤ w t) {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G)
    (hQ : (faceRemainder A Cp w G).PosDef) {W : Matrix m κ ℝ}
    (hW : Wᵀ * faceRemainder A Cp w G * W = 1) {G' : Matrix (n ⊕ κ) (n ⊕ κ) ℝ}
    (hG' : IsGInv (moment (fromRows A (Wᵀ * Cp)) (fromRows A (Wᵀ * Cp)) w) G') :
    trace (tension A Y w G - tension (fromRows A (Wᵀ * Cp)) Y w G') ≤
      leadingSum (isHermitian_reduced hQ (isHermitian_gram (crossRemainder A Cp Y w G)))
        (Fintype.card κ) := by
  rw [removal_eq_trace A Cp Y hw hG hW hG']
  exact trace_le_gen hQ (isHermitian_gram _) hW

/-- [proved-standard; formal-checked] **The best pool face**: the leading generalized eigenvectors of
`(Mᵀ M, Q)`, normalized on `Q`, found a face that removes exactly the sum of the `k` leading
generalized eigenvalues, whatever generalized inverse the joint face Gram takes. -/
theorem exists_pool_face_removal_eq (A : Matrix n ι ℝ) (Cp : Matrix m ι ℝ) (Y : Matrix o ι ℝ)
    {w : ι → ℝ} (hw : ∀ t, 0 ≤ w t) {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G)
    (hQ : (faceRemainder A Cp w G).PosDef) (hk : Fintype.card κ ≤ Fintype.card m) :
    ∃ W : Matrix m κ ℝ, Wᵀ * faceRemainder A Cp w G * W = 1 ∧
      ∀ G' : Matrix (n ⊕ κ) (n ⊕ κ) ℝ,
        IsGInv (moment (fromRows A (Wᵀ * Cp)) (fromRows A (Wᵀ * Cp)) w) G' →
        trace (tension A Y w G - tension (fromRows A (Wᵀ * Cp)) Y w G') =
          leadingSum (isHermitian_reduced hQ (isHermitian_gram (crossRemainder A Cp Y w G)))
            (Fintype.card κ) := by
  obtain ⟨W, hW, he⟩ := exists_trace_eq_gen (κ := κ) hQ
    (isHermitian_gram (crossRemainder A Cp Y w G)) hk
  exact ⟨W, hW, fun G' hG' => (removal_eq_trace A Cp Y hw hG hW hG').trans he⟩

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **The whole pool** (the record's `tr M Q⁺ Mᵀ = Σ μ`): all the
generalized eigenvalues of `(Mᵀ M, Q)` sum to `tr(M Q⁻¹ Mᵀ)`, which is what reading the whole pool
beside the face removes (`EffectiveTension.tension_fromRows` with `G_Q = Q⁻¹`). -/
theorem whole_pool_sum (A : Matrix n ι ℝ) (Cp : Matrix m ι ℝ) (Y : Matrix o ι ℝ) {w : ι → ℝ}
    {G : Matrix n n ℝ} (hQ : (faceRemainder A Cp w G).PosDef) :
    leadingSum (isHermitian_reduced hQ (isHermitian_gram (crossRemainder A Cp Y w G)))
        (Fintype.card m) =
      trace (crossRemainder A Cp Y w G * (faceRemainder A Cp w G)⁻¹ *
        (crossRemainder A Cp Y w G)ᵀ) := by
  rw [leadingSum_card, trace_reduced, Matrix.mul_assoc, trace_mul_comm]

end Pool

end Holonics.HNN.PoolFaceKyFan
