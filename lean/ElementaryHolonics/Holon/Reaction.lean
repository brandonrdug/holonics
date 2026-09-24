import ElementaryHolonics.Holon.Conformance

/-!
# Holon.Reaction: the learned reaction must be a modulated skew interconnection

[definition] The native divergence is the learned complex-bilinear `c ⊗ s` reaction block. The
ruling replaces it by a modulated skew interconnection `J(c)`. This module proves why.

[proved-derived; formal-checked]

1. **Impossibility.** A complex-bilinear reaction `B(c, s) = Σ_k c_k W_k s` with
   `Re⟨s, B(c, s)⟩ = 0` for every complex `c` and `s` has every `W_k = 0`
   (`bilinear_reaction_workless_iff_zero`): the probes `c = δ_k` and `c = i δ_k` kill the real and
   imaginary parts of `⟨s, W_k s⟩`, and complex polarization (`eq_zero_of_herm_zero`) finishes.
2. **The real form.** `J(c) = Σ_k (Re c_k A_k + Im c_k B_k)` with skew-Hermitian `A_k, B_k` is
   skew-Hermitian for every `c` (`skewReaction_skew`) and does no work, `Re⟨s, J(c)s⟩ = 0`
   (`skewReaction_workless`, `re_herm_skew`). Realified it is a skew-symmetric real structure
   (`realify_skew`), so the flow `ẋ = (realify J(c(τ)) − M) x` is the modulated medium Holon of
   `Holon.Conformance`, whose energy changes by exactly `−⟨x, M x⟩` (`reaction_balance`): the
   reaction contributes zero power for every contrast trajectory.
3. **The projection.** `skewPart W = ½(W − Wᴴ)` is skew-Hermitian (`skewPart_skew`), fixes
   skew-Hermitian matrices (`skewPart_of_skew`), is idempotent (`skewPart_idem`), and its residual
   is Frobenius-orthogonal to every skew-Hermitian matrix (`skewPart_orthogonal`): it is the
   orthogonal projection onto the skew-Hermitian subspace.
4. **Runaway witness.** A Hermitian slice `W = κ > 0` driven by a contrast equal to the amplitude
   has per-step gain `1 + hκ|s| > 1`, strictly increasing with the amplitude; its projection is `0`
   and the projected step with resistance `r ≥ 0` has gain `1 − hr ≤ 1` (`runaway_witness`).
-/

noncomputable section

namespace Soma.Holonics.HolonCore

open Matrix ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 0. The pairing trick -/

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] If the terms of a double sum are anti-conjugate under the swap
(`a j i = −conj (a i j)`), its real part vanishes. -/
theorem re_sum_antiConj (a : n → n → ℂ) (h : ∀ i j, a j i = -conj (a i j)) :
    (∑ i, ∑ j, a i j).re = 0 := by
  have hswap : ∑ i, ∑ j, a i j = ∑ i, ∑ j, a j i := Finset.sum_comm
  have hS : ∑ i, ∑ j, a j i = ∑ i, ∑ j, -conj (a i j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h i j
  have hre : (∑ i, ∑ j, -conj (a i j)).re = -(∑ i, ∑ j, a i j).re := by
    simp only [Complex.re_sum, Complex.neg_re, Complex.conj_re, Finset.sum_neg_distrib]
  have := congrArg Complex.re (hswap.trans hS)
  rw [hre] at this
  linarith

/-- [definition] The Hermitian pairing `⟨s, v⟩ = Σ conj(s_i) v_i`. -/
def herm (s v : n → ℂ) : ℂ := star s ⬝ᵥ v

omit [DecidableEq n] in
theorem herm_mulVec (s : n → ℂ) (M : Matrix n n ℂ) :
    herm s (M *ᵥ s) = ∑ i, ∑ j, conj (s i) * (M i j * s j) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **A skew-Hermitian map does no work**: `Re⟨s, M s⟩ = 0`. -/
theorem re_herm_skew {M : Matrix n n ℂ} (hM : Mᴴ = -M) (s : n → ℂ) : (herm s (M *ᵥ s)).re = 0 := by
  rw [herm_mulVec]
  apply re_sum_antiConj
  intro i j
  have hij : M j i = -conj (M i j) := by
    have := congrFun (congrFun hM i) j
    simp [Matrix.conjTranspose_apply] at this
    have := congrArg conj this
    simpa using this
  rw [hij]; simp [map_mul]; ring

/-! ## 1. Impossibility: a complex-bilinear reaction that does no work is zero -/

/-- [definition] The complex-bilinear reaction `B(c, s) = Σ_k c_k W_k s`. -/
def bilinearReaction {κ : Type*} [Fintype κ] (W : κ → Matrix n n ℂ) (c : κ → ℂ) (s : n → ℂ) :
    n → ℂ :=
  ∑ k, c k • (W k *ᵥ s)

/-- [proved-derived; formal-checked] **Polarization over `ℂ`**: `⟨s, W s⟩ = 0` for every `s` forces
`W = 0` (probes `δ_i`, `δ_i + δ_j`, `δ_i + i δ_j`). -/
theorem eq_zero_of_herm_zero {W : Matrix n n ℂ} (h : ∀ s, herm s (W *ᵥ s) = 0) : W = 0 := by
  have hsingle : ∀ i j (x y : ℂ), herm (Pi.single i x) (W *ᵥ Pi.single j y) = conj x * W i j * y := by
    intro i j x y
    simp [herm, dotProduct, mulVec, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul,
      Finset.sum_ite_eq', mul_assoc]
  have hadd : ∀ a b c d : n → ℂ, herm (a + b) (W *ᵥ (c + d)) =
      herm a (W *ᵥ c) + herm a (W *ᵥ d) + herm b (W *ᵥ c) + herm b (W *ᵥ d) := by
    intro a b c d
    simp only [herm, star_add, mulVec_add, add_dotProduct, dotProduct_add]; ring
  ext i j
  have hii : ∀ i, W i i = 0 := fun i => by
    have := h (Pi.single i 1); rw [hsingle] at this; simpa using this
  by_cases hij : i = j
  · subst hij; simpa using hii i
  · have h1 := h (Pi.single i 1 + Pi.single j 1)
    have h2 := h (Pi.single i 1 + Pi.single j Complex.I)
    rw [hadd, hsingle, hsingle, hsingle, hsingle] at h1 h2
    simp only [map_one, one_mul, mul_one, hii, Complex.conj_I, add_zero, zero_add] at h1 h2
    have e1 : W i j + W j i = 0 := by linear_combination h1
    have e2 : W i j - W j i = 0 := by
      have h3 : Complex.I * (W i j - W j i) = 0 := by
        linear_combination h2
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    simp only [Matrix.zero_apply]
    linear_combination (e1 + e2) / 2

/-- [proved-derived; formal-checked] **Impossibility.** If a complex-bilinear reaction does no
work for every complex contrast `c` and state `s` (`Re⟨s, B(c,s)⟩ = 0`), then every `W_k = 0`:
probing with `c = δ_k` kills `Re⟨s, W_k s⟩` and with `c = i δ_k` kills `Im⟨s, W_k s⟩`. A
power-neutral reaction cannot be complex-bilinear unless it vanishes. -/
theorem bilinear_reaction_workless_iff_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : κ → Matrix n n ℂ)
    (h : ∀ c s, (herm s (bilinearReaction W c s)).re = 0) : ∀ k, W k = 0 := by
  intro k
  apply eq_zero_of_herm_zero
  intro s
  have hc : ∀ z : ℂ, herm s (bilinearReaction W (Pi.single k z) s) = z * herm s (W k *ᵥ s) := by
    intro z
    simp [bilinearReaction, herm, Pi.single_apply, dotProduct_smul, ite_smul]
  have hre := h (Pi.single k 1) s
  have him := h (Pi.single k Complex.I) s
  rw [hc] at hre him
  apply Complex.ext
  · simpa using hre
  · simp [Complex.mul_re] at him
    simpa using him

/-! ## 2. The real form: a modulated skew interconnection -/

/-- [definition] **The modulated skew reaction** `J(c) = Σ_k (Re c_k A_k + Im c_k B_k)`. -/
def skewReaction {κ : Type*} [Fintype κ] (A B : κ → Matrix n n ℂ) (c : κ → ℂ) : Matrix n n ℂ :=
  ∑ k, (((c k).re : ℂ) • A k + ((c k).im : ℂ) • B k)

omit [Fintype n] [DecidableEq n] in
/-- [proved-derived; formal-checked] With every `A_k`, `B_k` skew-Hermitian, `J(c)` is
skew-Hermitian for every complex contrast `c`. -/
theorem skewReaction_skew {κ : Type*} [Fintype κ] {A B : κ → Matrix n n ℂ}
    (hA : ∀ k, (A k)ᴴ = -A k) (hB : ∀ k, (B k)ᴴ = -B k) (c : κ → ℂ) :
    (skewReaction A B c)ᴴ = -skewReaction A B c := by
  simp only [skewReaction, Matrix.conjTranspose_sum, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, hA, hB, Complex.star_def, Complex.conj_ofReal, smul_neg,
    ← Finset.sum_neg_distrib, neg_add]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The real form does no work**: `Re⟨s, J(c) s⟩ = 0` for every
contrast and state. -/
theorem skewReaction_workless {κ : Type*} [Fintype κ] {A B : κ → Matrix n n ℂ}
    (hA : ∀ k, (A k)ᴴ = -A k) (hB : ∀ k, (B k)ᴴ = -B k) (c : κ → ℂ) (s : n → ℂ) :
    (herm s (skewReaction A B c *ᵥ s)).re = 0 :=
  re_herm_skew (skewReaction_skew hA hB c) s

/-- [definition] Realify a complex matrix on `(Re, Im)` coordinates. -/
def realify (M : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (M.map Complex.re) (-(M.map Complex.im)) (M.map Complex.im) (M.map Complex.re)

omit [Fintype n] [DecidableEq n] in
/-- [proved-derived; formal-checked] A skew-Hermitian matrix realifies to a skew-symmetric one. -/
theorem realify_skew {M : Matrix n n ℂ} (hM : Mᴴ = -M) : (realify M)ᵀ = -realify M := by
  have hre : ∀ i j, (M j i).re = -(M i j).re := fun i j => by
    have h0 := congrFun (congrFun hM i) j
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply] at h0
    have := congrArg Complex.re h0
    rw [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  have him : ∀ i j, (M j i).im = (M i j).im := fun i j => by
    have h0 := congrFun (congrFun hM i) j
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply] at h0
    have := congrArg Complex.im h0
    rw [Complex.star_def, Complex.conj_im, Complex.neg_im] at this
    linarith
  rw [realify, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  congr 1 <;> ext i j <;>
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, neg_neg] <;>
    first | rw [hre] | rw [him]

/-- [proved-derived; formal-checked] **The reaction balance.** Along the realified flow
`ẋ = (realify J(c(τ)) − M) x` with `J(c)` skew-Hermitian (the modulated Dirac structure of
`mediumHolon`, storage `½|x|²`), the energy changes by exactly `−⟨x, M x⟩`: the reaction
contributes zero power for every contrast trajectory. -/
theorem reaction_balance (J : ℝ → Matrix n n ℂ) (hJ : ∀ t, (J t)ᴴ = -J t)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) {x : ℝ → n ⊕ n → ℝ} {t : ℝ}
    (hx : ∀ i, HasDerivAt (fun s => x s i) (((realify (J t) - M) *ᵥ (1 *ᵥ x t)) i) t) :
    HasDerivAt (fun s => storageEnergy 1 (x s)) (-((1 *ᵥ x t) ⬝ᵥ (M *ᵥ (1 *ᵥ x t)))) t := by
  have hv : (realify (J t) - M) *ᵥ (1 *ᵥ x t) =
      (realify (J t) - M) *ᵥ (1 *ᵥ x t) + (0 : Matrix (n ⊕ n) (Fin 0) ℝ) *ᵥ 0 := by simp
  rw [hv] at hx
  have h := (mediumHolon (realify_skew (hJ t)) M 1 (Matrix.transpose_one) 0).energy_balance_const hx
    (medium_admits (realify_skew (hJ t)) M 1 Matrix.transpose_one 0 (x t) 0)
  refine h.congr_deriv ?_
  simp [mediumHolon]

/-! ## 3. The projection onto skew-Hermitian reactions -/

/-- [definition] The skew-Hermitian part `½(W − Wᴴ)`. -/
def skewPart (W : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (W - Wᴴ)

omit [Fintype n] [DecidableEq n] in
theorem skewPart_skew (W : Matrix n n ℂ) : (skewPart W)ᴴ = -skewPart W := by
  rw [skewPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  simp only [star_div₀, star_one, star_ofNat]
  rw [← smul_neg, neg_sub]

omit [Fintype n] [DecidableEq n] in
/-- [proved-derived; formal-checked] **The projection fixes skew-Hermitian matrices and is
idempotent.** -/
theorem skewPart_of_skew {W : Matrix n n ℂ} (hW : Wᴴ = -W) : skewPart W = W := by
  rw [skewPart, hW, sub_neg_eq_add, ← two_smul ℂ W, smul_smul]; norm_num

omit [Fintype n] [DecidableEq n] in
theorem skewPart_idem (W : Matrix n n ℂ) : skewPart (skewPart W) = skewPart W :=
  skewPart_of_skew (skewPart_skew W)

/-- [definition] The real Frobenius pairing `Re Σ conj(A_ij) B_ij`. -/
def frob (A B : Matrix n n ℂ) : ℝ := (∑ i, ∑ j, conj (A i j) * B i j).re

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **It is the orthogonal projection** (Frobenius): the residual
`W − skewPart W` is orthogonal to every skew-Hermitian `K`. -/
theorem skewPart_orthogonal (W K : Matrix n n ℂ) (hK : Kᴴ = -K) :
    frob (W - skewPart W) K = 0 := by
  have hH : (W - skewPart W)ᴴ = W - skewPart W := by
    rw [Matrix.conjTranspose_sub, skewPart_skew, skewPart, sub_neg_eq_add]
    ext i j
    simp [Matrix.conjTranspose_apply]
    ring
  unfold frob
  apply re_sum_antiConj
  intro i j
  have h1 : (W - skewPart W) j i = conj ((W - skewPart W) i j) := by
    have := congrFun (congrFun hH i) j
    simp only [Matrix.conjTranspose_apply] at this
    rw [← this]; simp
  have h2 : K j i = -conj (K i j) := by
    have := congrFun (congrFun hK i) j
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
    have := congrArg conj this
    simpa using this
  rw [h1, h2]; simp [map_mul]

/-! ## 4. The runaway witness -/

/-- [counterexample; formal-checked] **Runaway under a Hermitian slice; bounded under the
projection.** A real slice `W = κ > 0` (pure Hermitian part) with contrast `Δ = s` growing with the
state gives the explicit step `s⁺ = (1 + hκ|Δ|) s`: gain `> 1`, strictly increasing with the
amplitude (hence with the energy). Its skew-Hermitian projection is `0`, so the projected step with
resistance `r ≥ 0` has gain `1 − h r ≤ 1`. -/
theorem runaway_witness {h κ r : ℝ} (hh : 0 < h) (hκ : 0 < κ) (hr : 0 ≤ r) :
    (∀ s : ℝ, 0 < s → 1 < 1 + h * κ * |s|) ∧
    (∀ s s' : ℝ, 0 ≤ s → s < s' → 1 + h * κ * |s| < 1 + h * κ * |s'|) ∧
    skewPart (!![(κ : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) = 0 ∧
    1 - h * r ≤ 1 := by
  refine ⟨fun s hs => ?_, fun s s' hs hss => ?_, ?_, by nlinarith⟩
  · rw [abs_of_pos hs]; nlinarith [mul_pos (mul_pos hh hκ) hs]
  · rw [abs_of_nonneg hs, abs_of_nonneg (by linarith)]
    nlinarith [mul_pos hh hκ]
  · ext i j; fin_cases i; fin_cases j
    simp [skewPart, Matrix.conjTranspose_apply]

end Soma.Holonics.HolonCore
