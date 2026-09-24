import Holonics.Holon.Element
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Holon.Deposition: deposition work, passivity under learning, and the passive projection

[definition] The deposition facet `Θ̇` of the Holon. A port Holon whose storage `Q` and a learned
active relation `L` (entering the flow as `(J − R + L) Q x`) change between commits. The word
may be passive at fixed material and still diverge under learning: the balance carries two terms
that fixed-material passivity does not see — the learned power `⟨e, L e⟩` and the deposition work
`½⟨x, ΔQ x⟩`.

[proved-derived; formal-checked]

1. **Continuous balance** over `ℝ`: along `ẋ = (J − R + L) Q(τ) x + B u`,
   `dE/dτ = −⟨e, R e⟩ + ⟨e, L e⟩ + ⟨e, B u⟩ + ½⟨x, Q̇ x⟩`, `e = Q x` (`learned_energy_balance`).
   **Commit balance** over a field: one implicit-midpoint word at `Θ_k` then a deposit
   `Q_k → Q_(k+1)` gives exactly
   `E(x⁺; Q⁺) − E(x; Q) = −h⟨ē,Rē⟩ + h⟨ē,Lē⟩ + h⟨ē,Bu⟩ + ½⟨x⁺, (Q⁺ − Q) x⁺⟩`
   (`commit_balance`): the word balance at `Θ_k` plus the deposition work.
2. **Passivity-preserving deposition.** If every word is passive (`R ⪰ 0`, `⟨e, L e⟩ ≤ 0` — the
   effort form of `AᵀQ + QA ⪯ 0` for `A = L Q`, `learned_rate_form`), inputs are off, `h ≥ 0`, and
   each deposit satisfies `Q_(k+1) ⪯ (1 + ε_k) Q_k` with `1 + ε_k ≥ 0`, then the committed energy obeys
   `E_n ≤ ∏_(k<n) (1 + ε_k) · E_0` (`committed_energy_bound`, from the abstract recurrence
   `energy_product_bound`), and over `ℝ` `∏(1 + ε_k) ≤ exp(Σ ε_k)` (`product_le_exp_sum`): bounded
   when `Σ ε_k < ∞`, non-increasing when every `ε_k ≤ 0`.
3. **Divergence witness.** The normal law `W H = B` with orthonormal features (`H = 1`) and the
   indefinite bilinear block `B = diag(1, −1)` learns `L = W` whose rate form `WᵀQ + QW = 2W` is
   indefinite; with `h = 1` the committed state `(3ⁿ, 0)` is a midpoint trajectory and its energy
   grows by the factor `9` per commit (`normal_law_divergence_witness`).
4. **The passive projection.** Clipping the positive eigenvalues of the symmetric part
   (`clipNeg`, spectral theorem over `ℝ`) gives `projectPassive L` with `⟨e, L' e⟩ ≤ 0` for every
   `e` (`projectPassive_passive`), fixing every already-passive `L` (`projectPassive_of_passive`);
   hence projecting each update restores the bound of item 2 (`projected_committed_energy_bound`).
5. **The certified projection (exact over `ℚ`).** For a certified congruence `Pᵀ (sym L) P = diag d`
   with `P P⁻¹ = 1`, removing `P⁻ᵀ diag(d₊) P⁻¹` gives `S' = P⁻ᵀ diag(min(d,0)) P⁻¹ ⪯ 0`
   (`congruenceClip_eq`, `congruenceClip_nonpos`), equal to `S` when `S ⪯ 0` (`d_i = ⟨Pδ_i, S Pδ_i⟩`,
   `congruence_diag`, `congruenceClip_of_nonpos`); the projected relation is passive, fixes passive
   relations, and restores the committed-energy bound (`projectPassiveCongruence_passive`,
   `projectPassiveCongruence_of_passive`, `certified_committed_energy_bound`). It is not the
   eigen-clip: for `S = [[1,1],[1,0]]` with `P = [[1,−1],[0,1]]` the certified clip is `diag(0,−1)`,
   whose removed part does not commute with `S`, while the eigen-clip does (`clipNeg_commute`,
   `congruence_vs_eigen_witness`).
-/

noncomputable section

namespace Holonics.HolonCore

open Matrix

/-! ## 1. The commit balance -/

section Commit

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {σ μ : Type*} [Fintype σ] [Fintype μ]

/-- [proved-derived; formal-checked] The deposition work of a storage change at fixed state. -/
theorem deposition_work (Q Q' : Matrix σ σ 𝕜) (x : σ → 𝕜) :
    storageEnergy Q' x - storageEnergy Q x = (1 / 2) * (x ⬝ᵥ ((Q' - Q) *ᵥ x)) := by
  simp only [storageEnergy, sub_mulVec, dotProduct_sub]; ring

/-- [proved-derived; formal-checked] **The commit balance.** An implicit-midpoint word of
`q̇ = (J − R + L) Q q + B u` at the material `Q`, followed by the deposit `Q → Q'`:
`E(x⁺; Q') − E(x; Q) = −h⟨ē,Rē⟩ + h⟨ē,Lē⟩ + h⟨ē,Bu⟩ + ½⟨x⁺, (Q' − Q) x⁺⟩` with
`ē = Q (x + x⁺)/2`. -/
theorem commit_balance {Q J R L : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (hJ : Jᵀ = -J) (Q' : Matrix σ σ 𝕜)
    (B : Matrix σ μ 𝕜) (h : 𝕜) (x x' : σ → 𝕜) (u : μ → 𝕜)
    (hstep : x' - x = h • ((J - R + L) *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) + B *ᵥ u)) :
    storageEnergy Q' x' - storageEnergy Q x =
      -(h * ((Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) ⬝ᵥ (R *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x')))))) +
        h * ((Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) ⬝ᵥ (L *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))))) +
        h * ((Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) ⬝ᵥ (B *ᵥ u)) +
        (1 / 2) * (x' ⬝ᵥ ((Q' - Q) *ᵥ x')) := by
  have hstep' : x' - x = h • ((J - (R - L)) *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) + B *ᵥ u) := by
    rw [hstep]; congr 2; abel_nf
  have hw := midpoint_balance hQ hJ B h x x' u hstep'
  have hd := deposition_work Q Q' x'
  rw [show storageEnergy Q' x' - storageEnergy Q x =
      (storageEnergy Q' x' - storageEnergy Q x') + (storageEnergy Q x' - storageEnergy Q x) by ring,
    hd, hw]
  simp only [sub_mulVec, dotProduct_sub]
  ring

omit [CharZero 𝕜] in
/-- [proved-derived; formal-checked] The effort form of the learned rate: for `A = L Q` with `Q`
symmetric, `⟨x, (AᵀQ + QA) x⟩ = 2⟨Qx, L Qx⟩`. -/
theorem learned_rate_form {Q L : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (x : σ → 𝕜) :
    x ⬝ᵥ (((L * Q)ᵀ * Q + Q * (L * Q)) *ᵥ x) = 2 * ((Q *ᵥ x) ⬝ᵥ (L *ᵥ (Q *ᵥ x))) := by
  rw [add_mulVec, dotProduct_add, Matrix.transpose_mul, hQ]
  simp only [← mulVec_mulVec]
  rw [symm_dot hQ x, symm_dot hQ x, dotProduct_comm (Lᵀ *ᵥ _), transpose_dot,
    dotProduct_comm (L *ᵥ _)]
  ring

end Commit

/-! ### The continuous balance under learning -/

/-- [proved-derived; formal-checked] **The balance under learning and deposition.** Along
`ẋ = (J − R + L) Q(τ) x + B u` with `J` skew and `Q(τ)` symmetric,
`dE/dτ = −⟨e, R e⟩ + ⟨e, L e⟩ + ⟨e, B u⟩ + ½⟨x, Q̇ x⟩`, `e = Q(τ) x`. -/
theorem learned_energy_balance {σ μ : Type*} [Fintype σ] [Fintype μ] {J R L : Matrix σ σ ℝ}
    (hJ : Jᵀ = -J) (B : Matrix σ μ ℝ) (u : μ → ℝ) {x : ℝ → σ → ℝ} {Q : ℝ → Matrix σ σ ℝ}
    {Qd : Matrix σ σ ℝ} {t : ℝ}
    (hx : ∀ i, HasDerivAt (fun s => x s i)
      (((J - R + L) *ᵥ (Q t *ᵥ x t) + B *ᵥ u) i) t)
    (hQ : ∀ i j, HasDerivAt (fun s => Q s i j) (Qd i j) t) (hsymm : (Q t)ᵀ = Q t) :
    HasDerivAt (fun s => storageEnergy (Q s) (x s))
      (-((Q t *ᵥ x t) ⬝ᵥ (R *ᵥ (Q t *ᵥ x t))) + (Q t *ᵥ x t) ⬝ᵥ (L *ᵥ (Q t *ᵥ x t)) +
        (Q t *ᵥ x t) ⬝ᵥ (B *ᵥ u) + (1 / 2) * (x t ⬝ᵥ (Qd *ᵥ x t))) t := by
  refine (hasDerivAt_storageEnergy hx hQ hsymm).congr_deriv ?_
  set e := Q t *ᵥ x t
  have hskew : e ⬝ᵥ (J *ᵥ e) = 0 := by
    have := skew_dot hJ e e
    linarith
  rw [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_add, dotProduct_sub, hskew]
  ring

/-! ## 2. Passivity-preserving deposition -/

section Bound

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- [proved-derived; formal-checked] **The abstract commit recurrence.** A passive word
(`W_k ≤ E_k`) followed by a deposit that scales storage by at most `1 + ε_k ≥ 0`
(`E_(k+1) ≤ (1 + ε_k) W_k`) gives `E_n ≤ ∏_(k<n) (1 + ε_k) · E_0`. -/
theorem energy_product_bound (E W ε : ℕ → 𝕜) (hW : ∀ k, W k ≤ E k)
    (hE : ∀ k, E (k + 1) ≤ (1 + ε k) * W k) (hε : ∀ k, 0 ≤ 1 + ε k) :
    ∀ n, E n ≤ (∏ k ∈ Finset.range n, (1 + ε k)) * E 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      calc E (n + 1) ≤ (1 + ε n) * W n := hE n
        _ ≤ (1 + ε n) * E n := mul_le_mul_of_nonneg_left (hW n) (hε n)
        _ ≤ (1 + ε n) * ((∏ k ∈ Finset.range n, (1 + ε k)) * E 0) :=
            mul_le_mul_of_nonneg_left ih (hε n)
        _ = _ := by ring

variable {σ : Type*} [Fintype σ]

/-- [proved-derived; formal-checked] **Passivity-preserving deposition.** Committed midpoint words
of `q̇ = (J_k − R_k + L_k) Q_k q` with `R_k ⪰ 0`, `⟨e, L_k e⟩ ≤ 0`, `h ≥ 0`, and deposits
`Q_(k+1) ⪯ (1 + ε_k) Q_k`, `1 + ε_k ≥ 0`: the committed energy obeys
`E(x_n; Q_n) ≤ ∏_(k<n) (1 + ε_k) E(x_0; Q_0)`. -/
theorem committed_energy_bound (x : ℕ → σ → 𝕜) (Q J R L : ℕ → Matrix σ σ 𝕜) (ε : ℕ → 𝕜)
    (h : 𝕜) (hh : 0 ≤ h) (hQ : ∀ k, (Q k)ᵀ = Q k) (hJ : ∀ k, (J k)ᵀ = -J k)
    (hR : ∀ k e, 0 ≤ e ⬝ᵥ (R k *ᵥ e)) (hL : ∀ k e, e ⬝ᵥ (L k *ᵥ e) ≤ 0)
    (hstep : ∀ k, x (k + 1) - x k =
      h • ((J k - R k + L k) *ᵥ (Q k *ᵥ ((1 / 2 : 𝕜) • (x k + x (k + 1))))))
    (hdep : ∀ k y, storageEnergy (Q (k + 1)) y ≤ (1 + ε k) * storageEnergy (Q k) y)
    (hε : ∀ k, 0 ≤ 1 + ε k) (n : ℕ) :
    storageEnergy (Q n) (x n) ≤
      (∏ k ∈ Finset.range n, (1 + ε k)) * storageEnergy (Q 0) (x 0) := by
  refine energy_product_bound (fun k => storageEnergy (Q k) (x k))
    (fun k => storageEnergy (Q k) (x (k + 1))) ε (fun k => ?_) (fun k => hdep k _) hε n
  have hstep' : x (k + 1) - x k =
      h • ((J k - (R k - L k)) *ᵥ (Q k *ᵥ ((1 / 2 : 𝕜) • (x k + x (k + 1)))) +
        (0 : Matrix σ (Fin 0) 𝕜) *ᵥ 0) := by
    rw [hstep k]; congr 1; simp only [zero_mulVec, add_zero]; congr 1; abel
  have hw := midpoint_balance (hQ k) (hJ k) 0 h (x k) (x (k + 1)) 0 hstep'
  set e := Q k *ᵥ ((1 / 2 : 𝕜) • (x k + x (k + 1)))
  have hRL : 0 ≤ e ⬝ᵥ ((R k - L k) *ᵥ e) := by
    rw [sub_mulVec, dotProduct_sub]; linarith [hR k e, hL k e]
  simp only [zero_mulVec, dotProduct_zero, mul_zero, add_zero] at hw
  have : 0 ≤ h * (e ⬝ᵥ ((R k - L k) *ᵥ e)) := mul_nonneg hh hRL
  show storageEnergy (Q k) (x (k + 1)) ≤ storageEnergy (Q k) (x k)
  linarith

end Bound

/-- [proved-derived; formal-checked] Over `ℝ`, `∏ (1 + ε_k) ≤ exp (Σ ε_k)` when every `1 + ε_k ≥ 0`:
the committed energy is bounded whenever `Σ ε_k` is. -/
theorem product_le_exp_sum (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ 1 + ε k) (n : ℕ) :
    ∏ k ∈ Finset.range n, (1 + ε k) ≤ Real.exp (∑ k ∈ Finset.range n, ε k) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod (fun k _ => hε k)
  intro k _
  linarith [Real.add_one_le_exp (ε k)]

/-! ## 3. The divergence witness -/

/-- [definition] The indefinite bilinear block `diag(1, −1)`. -/
def indefiniteBlock : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- [definition] The divergent committed state `(3ⁿ, 0)`. -/
def divergentState (n : ℕ) : Fin 2 → ℚ := ![3 ^ n, 0]

/-- [counterexample; formal-checked] **Learning diverges through an indefinite normal-law block.**
With orthonormal features (`H = 1`), the normal law `W H = B` returns `W = B = diag(1, −1)`; the
learned rate form `WᵀQ + QW = 2W` (at `Q = 1`) is indefinite; with `J = R = 0`, `h = 1`, the state
`(3ⁿ, 0)` is a midpoint trajectory of `q̇ = W q`, and its energy is `9ⁿ/2`: it grows by `9` per
commit although the material `Q` never changes. -/
theorem normal_law_divergence_witness :
    indefiniteBlock * 1 = indefiniteBlock ∧
    (0 < (![1, 0] : Fin 2 → ℚ) ⬝ᵥ ((indefiniteBlockᵀ * 1 + 1 * indefiniteBlock) *ᵥ ![1, 0]) ∧
      (![0, 1] : Fin 2 → ℚ) ⬝ᵥ ((indefiniteBlockᵀ * 1 + 1 * indefiniteBlock) *ᵥ ![0, 1]) < 0) ∧
    (∀ n, divergentState (n + 1) - divergentState n =
      (1 : ℚ) • ((0 - 0 + indefiniteBlock) *ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ
        ((1 / 2 : ℚ) • (divergentState n + divergentState (n + 1)))))) ∧
    ∀ n, storageEnergy 1 (divergentState n) = 9 ^ n / 2 := by
  refine ⟨by simp, ⟨?_, ?_⟩, fun n => ?_, fun n => ?_⟩
  · simp [indefiniteBlock, mulVec, dotProduct, Fin.sum_univ_two]
  · simp [indefiniteBlock, mulVec, dotProduct, Fin.sum_univ_two]
  · ext i; fin_cases i
    · simp [divergentState, indefiniteBlock, pow_succ]
      ring
    · simp [divergentState, indefiniteBlock]
  · simp [storageEnergy, divergentState, dotProduct, Fin.sum_univ_two]
    rw [← mul_pow]; norm_num; ring

/-! ## 4. The passive projection -/

section Projection

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] Clip the positive eigenvalues of a symmetric matrix: `U diag(min(λ, 0)) Uᵀ`. -/
def clipNeg {S : Matrix n n ℝ} (hS : S.IsHermitian) : Matrix n n ℝ :=
  (hS.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => min (hS.eigenvalues i) 0) *
    (hS.eigenvectorUnitary : Matrix n n ℝ)ᵀ

omit [DecidableEq n] in
theorem quad_conj (U D : Matrix n n ℝ) (e : n → ℝ) :
    e ⬝ᵥ ((U * D * Uᵀ) *ᵥ e) = (Uᵀ *ᵥ e) ⬝ᵥ (D *ᵥ (Uᵀ *ᵥ e)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

/-- [proved-derived; formal-checked] The clipped matrix is negative semidefinite. -/
theorem clipNeg_nonpos {S : Matrix n n ℝ} (hS : S.IsHermitian) (e : n → ℝ) :
    e ⬝ᵥ (clipNeg hS *ᵥ e) ≤ 0 := by
  rw [clipNeg, quad_conj]
  set y := (hS.eigenvectorUnitary : Matrix n n ℝ)ᵀ *ᵥ e
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_nonpos
  intro i _
  have := min_le_right (hS.eigenvalues i) 0
  nlinarith [sq_nonneg (y i)]

theorem spectral_real {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    S = (hS.eigenvectorUnitary : Matrix n n ℝ) * diagonal hS.eigenvalues *
      (hS.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  conv_lhs => rw [hS.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  simp [Matrix.star_eq_conjTranspose]

/-- [proved-derived; formal-checked] Clipping fixes a negative semidefinite matrix. -/
theorem clipNeg_of_nonpos {S : Matrix n n ℝ} (hS : S.IsHermitian)
    (hneg : ∀ e, e ⬝ᵥ (S *ᵥ e) ≤ 0) : clipNeg hS = S := by
  have hlam : ∀ i, hS.eigenvalues i ≤ 0 := by
    intro i
    rw [hS.eigenvalues_eq]
    simpa using hneg _
  conv_rhs => rw [spectral_real hS]
  rw [clipNeg]
  congr 3
  funext i
  exact min_eq_left (hlam i)

/-- [definition] The symmetric part `(L + Lᵀ)/2`. -/
def symPart (L : Matrix n n ℝ) : Matrix n n ℝ := (1 / 2 : ℝ) • (L + Lᵀ)

omit [Fintype n] [DecidableEq n] in
theorem symPart_isHermitian (L : Matrix n n ℝ) : (symPart L).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, symPart,
    Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

omit [DecidableEq n] in
theorem quad_symPart (L : Matrix n n ℝ) (e : n → ℝ) :
    e ⬝ᵥ (symPart L *ᵥ e) = e ⬝ᵥ (L *ᵥ e) := by
  rw [symPart, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, dotProduct_mulVec e Lᵀ,
    ← mulVec_transpose, Matrix.transpose_transpose, dotProduct_comm (L *ᵥ e), smul_eq_mul]
  ring

/-- [definition] **The passive projection**: remove the positive part of the symmetric part,
keep the skew part. -/
def projectPassive (L : Matrix n n ℝ) : Matrix n n ℝ :=
  L - (symPart L - clipNeg (symPart_isHermitian L))

/-- [proved-derived; formal-checked] **The projected relation is passive**: `⟨e, L' e⟩ ≤ 0`. -/
theorem projectPassive_passive (L : Matrix n n ℝ) (e : n → ℝ) :
    e ⬝ᵥ (projectPassive L *ᵥ e) ≤ 0 := by
  rw [projectPassive, sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub, quad_symPart]
  linarith [clipNeg_nonpos (symPart_isHermitian L) e]

/-- [proved-derived; formal-checked] **The projection fixes passive relations.** -/
theorem projectPassive_of_passive (L : Matrix n n ℝ) (hL : ∀ e, e ⬝ᵥ (L *ᵥ e) ≤ 0) :
    projectPassive L = L := by
  have : clipNeg (symPart_isHermitian L) = symPart L :=
    clipNeg_of_nonpos _ fun e => by rw [quad_symPart]; exact hL e
  rw [projectPassive, this, sub_self, sub_zero]

/-- [proved-derived; formal-checked] **Projecting each update restores the bound.** Whatever the
learned updates `L_k`, the committed trajectory run with `projectPassive L_k` obeys
`E_n ≤ ∏ (1 + ε_k) E_0`. -/
theorem projected_committed_energy_bound (x : ℕ → n → ℝ) (Q J R L : ℕ → Matrix n n ℝ)
    (ε : ℕ → ℝ) (h : ℝ) (hh : 0 ≤ h) (hQ : ∀ k, (Q k)ᵀ = Q k) (hJ : ∀ k, (J k)ᵀ = -J k)
    (hR : ∀ k e, 0 ≤ e ⬝ᵥ (R k *ᵥ e))
    (hstep : ∀ k, x (k + 1) - x k =
      h • ((J k - R k + projectPassive (L k)) *ᵥ (Q k *ᵥ ((1 / 2 : ℝ) • (x k + x (k + 1))))))
    (hdep : ∀ k y, storageEnergy (Q (k + 1)) y ≤ (1 + ε k) * storageEnergy (Q k) y)
    (hε : ∀ k, 0 ≤ 1 + ε k) (m : ℕ) :
    storageEnergy (Q m) (x m) ≤
      (∏ k ∈ Finset.range m, (1 + ε k)) * storageEnergy (Q 0) (x 0) :=
  committed_energy_bound x Q J R (fun k => projectPassive (L k)) ε h hh hQ hJ hR
    (fun k e => projectPassive_passive (L k) e) hstep hdep hε m

/-- [proved-derived; formal-checked] The eigen-clip commutes with the matrix it clips (both are
diagonal in the same orthonormal eigenbasis). -/
theorem clipNeg_commute {S : Matrix n n ℝ} (hS : S.IsHermitian) : S * clipNeg hS = clipNeg hS * S := by
  have hU : ((hS.eigenvectorUnitary : Matrix n n ℝ))ᵀ * (hS.eigenvectorUnitary : Matrix n n ℝ) = 1 := by
    have := Unitary.coe_star_mul_self hS.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hSU := spectral_real hS
  unfold clipNeg
  generalize (hS.eigenvectorUnitary : Matrix n n ℝ) = U at hU hSU ⊢
  generalize hS.eigenvalues = lam at hSU ⊢
  subst hSU
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
    ← Matrix.mul_assoc (diagonal lam), ← Matrix.mul_assoc (diagonal _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 3
  funext i; ring

end Projection

/-! ## 5. The certified-congruence projection (exact over `ℚ`) -/

section Congruence

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] **The congruence clip.** With a certified congruence `Pᵀ S P = diag d` and
`P⁻¹ = Pinv`, remove `P⁻ᵀ diag(d₊) P⁻¹`. -/
def congruenceClip (S Pinv : Matrix n n 𝕜) (d : n → 𝕜) : Matrix n n 𝕜 :=
  S - Pinvᵀ * diagonal (fun i => max (d i) 0) * Pinv

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DecidableEq n] in
theorem quad_congr (A D : Matrix n n 𝕜) (e : n → 𝕜) :
    e ⬝ᵥ ((Aᵀ * D * A) *ᵥ e) = (A *ᵥ e) ⬝ᵥ (D *ᵥ (A *ᵥ e)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

omit [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] Under the congruence, `S = P⁻ᵀ diag(d) P⁻¹` and the clip is
`P⁻ᵀ diag(min(d, 0)) P⁻¹`. -/
theorem congruenceClip_eq {S P Pinv : Matrix n n 𝕜} {d : n → 𝕜} (hP : P * Pinv = 1)
    (hD : Pᵀ * S * P = diagonal d) :
    congruenceClip S Pinv d = Pinvᵀ * diagonal (fun i => min (d i) 0) * Pinv := by
  have hS : S = Pinvᵀ * diagonal d * Pinv := by
    rw [← hD]
    have hT : Pinvᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hP, Matrix.transpose_one]
    simp only [Matrix.mul_assoc]
    rw [hP, Matrix.mul_one, ← Matrix.mul_assoc, hT, Matrix.one_mul]
  rw [congruenceClip]
  conv_lhs => rw [hS]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  congr 3
  funext i
  rcases le_total (d i) 0 with h | h
  · rw [max_eq_right h, min_eq_left h, sub_zero]
  · rw [max_eq_left h, min_eq_right h, sub_self]

/-- [proved-derived; formal-checked] **The congruence clip is negative semidefinite.** -/
theorem congruenceClip_nonpos {S P Pinv : Matrix n n 𝕜} {d : n → 𝕜} (hP : P * Pinv = 1)
    (hD : Pᵀ * S * P = diagonal d) (e : n → 𝕜) :
    e ⬝ᵥ (congruenceClip S Pinv d *ᵥ e) ≤ 0 := by
  rw [congruenceClip_eq hP hD, quad_congr]
  set y := Pinv *ᵥ e
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_nonpos
  intro i _
  have := min_le_right (d i) 0
  nlinarith [mul_self_nonneg (y i)]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] A congruence reads its diagonal: `⟨P δ_i, S P δ_i⟩ = d_i`. -/
theorem congruence_diag {S P : Matrix n n 𝕜} {d : n → 𝕜} (hD : Pᵀ * S * P = diagonal d) (i : n) :
    (P *ᵥ Pi.single i 1) ⬝ᵥ (S *ᵥ (P *ᵥ Pi.single i 1)) = d i := by
  rw [← quad_congr, hD]
  simp

omit [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **The congruence clip fixes a negative semidefinite `S`**:
each `d_i = ⟨P δ_i, S P δ_i⟩ ≤ 0`, so `d₊ = 0`. -/
theorem congruenceClip_of_nonpos {S P Pinv : Matrix n n 𝕜} {d : n → 𝕜}
    (hD : Pᵀ * S * P = diagonal d) (hneg : ∀ e, e ⬝ᵥ (S *ᵥ e) ≤ 0) :
    congruenceClip S Pinv d = S := by
  have hd : ∀ i, d i ≤ 0 := fun i => by
    rw [← congruence_diag hD i]; exact hneg _
  rw [congruenceClip]
  have : (fun i => max (d i) 0) = fun _ => (0 : 𝕜) := funext fun i => max_eq_right (hd i)
  rw [this, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul, sub_zero]

/-- [definition] The symmetric part over a field of characteristic zero. -/
def symPartK (L : Matrix n n 𝕜) : Matrix n n 𝕜 := (1 / 2 : 𝕜) • (L + Lᵀ)

omit [DecidableEq n] in
theorem quad_symPartK (L : Matrix n n 𝕜) (e : n → 𝕜) :
    e ⬝ᵥ (symPartK L *ᵥ e) = e ⬝ᵥ (L *ᵥ e) := by
  rw [symPartK, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, dotProduct_mulVec e Lᵀ,
    ← mulVec_transpose, Matrix.transpose_transpose, dotProduct_comm (L *ᵥ e), smul_eq_mul]
  ring

/-- [definition] **The certified passive projection** of a learned relation: remove
`P⁻ᵀ diag(d₊) P⁻¹` for a congruence `Pᵀ (sym L) P = diag d`; the skew part is kept. -/
def projectPassiveCongruence (L Pinv : Matrix n n 𝕜) (d : n → 𝕜) : Matrix n n 𝕜 :=
  L - Pinvᵀ * diagonal (fun i => max (d i) 0) * Pinv

/-- [proved-derived; formal-checked] **The certified projection is passive.** -/
theorem projectPassiveCongruence_passive {L P Pinv : Matrix n n 𝕜} {d : n → 𝕜}
    (hP : P * Pinv = 1) (hD : Pᵀ * symPartK L * P = diagonal d) (e : n → 𝕜) :
    e ⬝ᵥ (projectPassiveCongruence L Pinv d *ᵥ e) ≤ 0 := by
  have h := congruenceClip_nonpos hP hD e
  rw [congruenceClip, sub_mulVec, dotProduct_sub, quad_symPartK] at h
  rw [projectPassiveCongruence, sub_mulVec, dotProduct_sub]
  exact h

/-- [proved-derived; formal-checked] It fixes an already passive relation. -/
theorem projectPassiveCongruence_of_passive {L P Pinv : Matrix n n 𝕜} {d : n → 𝕜}
    (hD : Pᵀ * symPartK L * P = diagonal d) (hL : ∀ e, e ⬝ᵥ (L *ᵥ e) ≤ 0) :
    projectPassiveCongruence L Pinv d = L := by
  have hd : ∀ i, d i ≤ 0 := fun i => by
    rw [← congruence_diag hD i, quad_symPartK]; exact hL _
  rw [projectPassiveCongruence]
  have : (fun i => max (d i) 0) = fun _ => (0 : 𝕜) := funext fun i => max_eq_right (hd i)
  rw [this, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul, sub_zero]

/-- [proved-derived; formal-checked] **The committed-energy bound under the certified
projection**, composing `committed_energy_bound`: whatever the raw learned updates `L_k`, with
certified congruences `P_kᵀ (sym L_k) P_k = diag d_k`, the committed energy obeys
`E_m ≤ ∏ (1 + ε_k) E_0`. -/
theorem certified_committed_energy_bound [CharZero 𝕜] (x : ℕ → n → 𝕜)
    (Q J R L P Pinv : ℕ → Matrix n n 𝕜) (d : ℕ → n → 𝕜) (ε : ℕ → 𝕜) (h : 𝕜) (hh : 0 ≤ h)
    (hQ : ∀ k, (Q k)ᵀ = Q k) (hJ : ∀ k, (J k)ᵀ = -J k) (hR : ∀ k e, 0 ≤ e ⬝ᵥ (R k *ᵥ e))
    (hP : ∀ k, P k * Pinv k = 1) (hD : ∀ k, (P k)ᵀ * symPartK (L k) * P k = diagonal (d k))
    (hstep : ∀ k, x (k + 1) - x k = h • ((J k - R k + projectPassiveCongruence (L k) (Pinv k) (d k))
      *ᵥ (Q k *ᵥ ((1 / 2 : 𝕜) • (x k + x (k + 1))))))
    (hdep : ∀ k y, storageEnergy (Q (k + 1)) y ≤ (1 + ε k) * storageEnergy (Q k) y)
    (hε : ∀ k, 0 ≤ 1 + ε k) (m : ℕ) :
    storageEnergy (Q m) (x m) ≤
      (∏ k ∈ Finset.range m, (1 + ε k)) * storageEnergy (Q 0) (x 0) :=
  committed_energy_bound x Q J R (fun k => projectPassiveCongruence (L k) (Pinv k) (d k)) ε h hh
    hQ hJ hR (fun k e => projectPassiveCongruence_passive (hP k) (hD k) e) hstep hdep hε m

end Congruence

/-! ### Witness: the certified clip is not the eigen-clip -/

/-- [definition] `S = [[1, 1], [1, 0]]`, congruence `P = [[1, −1], [0, 1]]`, `Pᵀ S P = diag(1, −1)`. -/
def wS : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]
def wP : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, 1]
def wPinv : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- [counterexample; formal-checked] **The certified clip differs from the eigen-clip.** With the
non-orthogonal congruence `P`, the congruence clip is `diag(0, −1)`; the removed part
`[[1,1],[1,1]]` does not commute with `S`, whereas the eigen-clip commutes with `S`
(`clipNeg_commute`), so the two clips are different negative semidefinite matrices. -/
theorem congruence_vs_eigen_witness (hS : wS.IsHermitian) :
    wP * wPinv = 1 ∧ wPᵀ * wS * wP = diagonal ![1, -1] ∧
      congruenceClip wS wPinv ![1, -1] = !![0, 0; 0, -1] ∧
      congruenceClip wS wPinv ![1, -1] ≠ clipNeg hS := by
  have h1 : wP * wPinv = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [wP, wPinv, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : wPᵀ * wS * wP = diagonal ![1, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [wP, wS, Matrix.mul_apply, Fin.sum_univ_two, diagonal]
  have h3 : congruenceClip wS wPinv ![1, -1] = !![0, 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [congruenceClip, wS, wPinv, Matrix.mul_apply, Fin.sum_univ_two, diagonal]
  refine ⟨h1, h2, h3, fun h => ?_⟩
  have hc := clipNeg_commute hS
  rw [← h, h3] at hc
  have := congrFun (congrFun hc 0) 1
  simp [wS, Matrix.mul_apply, Fin.sum_univ_two] at this

end Holonics.HolonCore
