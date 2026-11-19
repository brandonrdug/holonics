import HolonicsResearch.HNN.EffectiveTension
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Matrix.PosDef

/-!
# The leverage of a new reading: what the encounters determine and what they leave open

The record `research/records/2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT.md`
(§§9 and 10) reads a new reading `v` against the Gram `G = Σ_t x_t x_tᵀ` of a face's encounters,
which is positive semidefinite with a kernel. #410's box "The leverage of a new reading" asks for
the split, the bound for every form, the value in range, the bordered minors and the two sequence
identities; this file proves them.

[proved-standard; formal-checked] What is proved.

1. **The pivot chart and the split** (`chartCol`, `pivotBlock`, `chartCoeff`, `supported`,
   `openPart`, `chartLeverage`, `IsPivotChart`; `supported_eq_mulVec`, `supported_mem_range`,
   `supported_add_openPart`, `supported_comp`, `openPart_comp`, `supported_of_mem_range`,
   `openPart_eq_zero_iff`). For pivot cells `e : κ → n` with `G_KK` invertible,
   `v = v_s + ρ` with `v_s = G_(:,K) G_KK⁻¹ v_K = G (spread (G_KK⁻¹ v_K)) ∈ range G` and `ρ_K = 0`.
   In a pivot chart, where also `G = G_(:,K) G_KK⁻¹ G_(K,:)`, `ρ = 0` if and only if `v ∈ range G`.
2. **The bound for every form** (`sq_form_le`, `form_spread_chartCoeff`, `chartLeverage_nonneg`,
   `sq_dotProduct_supported_le`, `supported_bound_attained`). On a positive semidefinite `G`,
   `|wᵀ v_s|² ≤ (wᵀ G w) · h_K` with `h_K = v_Kᵀ G_KK⁻¹ v_K ≥ 0`, for every `w` and with no range
   assumption on `w` (the Cauchy–Schwarz inequality of `G`, through `discrim_le_zero`); the form the
   chart places at the pivots attains it. This covers GPT-6's factor form `L·diag(d)·Lᵀ`, `d > 0`,
   which is one positive semidefinite `G`.
3. **The forms that agree on the cells** (`dotProduct_eq_of_cells`,
   `dotProduct_supported_eq_of_cells`, `dotProduct_sub_eq_openPart`,
   `dotProduct_supported_add_ker`). For `G = X Xᵀ`, forms with `wᵀ X = w′ᵀ X` share `wᵀ v_s` and
   differ on `v` by `(w − w′)ᵀ ρ`; on a symmetric `G` a form in `ker G` leaves `wᵀ v_s`.
4. **The value in range** (`ginv_value_eq`, `chartLeverage_of_mem_range`, `chartLeverage_eq_ginv`,
   `chartLeverage_chart_free`, `rebase_reading`, `rebase_form`, `ginv_value_rebase`,
   `chartLeverage_rebase`). In range, `h_K(Gu) = uᵀ G u = vᵀ G⁻ v` for every generalized inverse
   (`EffectiveTension.pinv` among them), so it is the same in every pivot chart, and an invertible
   rebase `x ↦ P x` (`G ↦ P G Pᵀ`, `v ↦ P v`) leaves it.
5. **Readings in sequence** (`gramAfter`, `lev`, `momentAfter`, `fitted`, `prequentialResidual`,
   `leastResidual`, `penalized`; `posDef_gramAfter`, `lev_nonneg`, `det_gramAfter_succ`,
   `det_gramAfter`, `prod_one_add_lev`, `value_add_reading`, `leastResidual_succ`,
   `sum_prequential_eq`, `penalized_eq`, `penalized_sub_leastResidual`, `prequential_isLeast`,
   `prequential_unit_prior`). From a positive definite prior `G₀`, with
   `G_t = G₀ + Σ_(s<t) x_s x_sᵀ` and `h_t = x_tᵀ G_t⁻¹ x_t`,
   `Π_(t<N) (1 + h_t) = det G_N / det G₀` (the matrix determinant lemma), and with
   `r_t = y_t − x_tᵀ G_t⁻¹ b_t` the prequential residual,
   `Σ_(t<N) r_t² / (1 + h_t) = min_w Σ_(t<N) (y_t − x_tᵀ w)² + wᵀ G₀ w`, attained at
   `G_N⁻¹ b_N`; at the unit prior, `min_w |y − Xw|² + wᵀw` and `det G_N`.
6. **The bordered minors** (`det_bordered_corner`, `det_bordered_passed`):
   `det [[G_KK, v_K], [v_Kᵀ, 0]] = −Δ · h_K` and `det [[G_KK, v_K], [G_(p,K), v_p]] = Δ · ρ_p`,
   `Δ = det G_KK`.
7. **GPT-6's example** (`witnessGram`, `witnessPinv`, `witnessPinv_laws`, `witness_bound`): on
   `G = [[1, 1], [1, 1]]` with `w = c = (1, 0)`, `(wᵀc)² = 1` against `(wᵀGw)(cᵀG⁺c) = 1/4`, while
   the chart on the first cell reads `h_K = 1` and `wᵀ v_s = 1`, its bound held with equality.

Limits. The chart is stated by its condition, `G_KK` invertible with a vanishing Schur complement;
that a fraction-free elimination's pivots give such a chart, and that it stores the bordered minors
of item 6 (Sylvester's identity), are not built: the minors are proved for any chart, the
elimination's being the pivots taken before `p`. The series `h_K = Σ_k Γ_k² / (Δ_(k−1) Δ_k)` over
the nested pivot blocks, the off-range limit `ε · vᵀ(G + εI)⁻¹ v → |(I − G G⁺) v|²`, the mean square
error `σ²(1 + h)` of a release in range (a declared noise model), the charge `½ log₂(1 + h)` and the
record's rank-5 check are not stated. The sequence identities are over the reals with a scalar
covector.

The computational object is the helical pair interaction: a contact's encounters are its Gram, and a
new reading meets them at the contact, which carries the supported part and leaves the open part to
another contact. Of the winding guide's six general objects this touches the pair (the contact's
encounters), faces and placement (the supported part a face releases, the open part it cannot) and
the tube (the readings in sequence along the passage's clock); the helix, the cell holonomy and the
tower thread stay attached.

Consumers: the atlas rows `contact.reading-leverage`, `release.leverage-probe` and
`spectro.reading-mass`, and #410's box "The leverage of a new reading".

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix Finset
open scoped MatrixOrder

namespace Holonics.HNN.ReadingLeverage

/-! ## 1. The pivot chart and the split of a reading -/

section Chart

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]

/-- [definition] The chart's columns `G_(:,K)`: the encounter Gram read at the pivot cells `e`. -/
def chartCol (G : Matrix n n ℝ) (e : κ → n) : Matrix n κ ℝ := G.submatrix id e

/-- [definition] The pivot block `G_KK`. -/
def pivotBlock (G : Matrix n n ℝ) (e : κ → n) : Matrix κ κ ℝ := G.submatrix e e

/-- [definition] The chart's coefficients `G_KK⁻¹ v_K` of a reading `v`. -/
noncomputable def chartCoeff (G : Matrix n n ℝ) (e : κ → n) (v : n → ℝ) : κ → ℝ :=
  (pivotBlock G e)⁻¹ *ᵥ (v ∘ e)

/-- [definition] The supported part `v_s = G_(:,K) G_KK⁻¹ v_K`. -/
noncomputable def supported (G : Matrix n n ℝ) (e : κ → n) (v : n → ℝ) : n → ℝ :=
  chartCol G e *ᵥ chartCoeff G e v

/-- [definition] The open part `ρ = v − v_s`: what the encounters leave to another contact. -/
noncomputable def openPart (G : Matrix n n ℝ) (e : κ → n) (v : n → ℝ) : n → ℝ :=
  v - supported G e v

/-- [definition] The chart's leverage `h_K = v_Kᵀ G_KK⁻¹ v_K`. -/
noncomputable def chartLeverage (G : Matrix n n ℝ) (e : κ → n) (v : n → ℝ) : ℝ :=
  (v ∘ e) ⬝ᵥ chartCoeff G e v

/-- [definition] A vector on the pivots placed at its cells, zero elsewhere. -/
def spread (e : κ → n) (a : κ → ℝ) : n → ℝ := fun i => ∑ k, if e k = i then a k else 0

/-- [definition] The chart's condition: `G_KK` invertible and `G = G_(:,K) G_KK⁻¹ G_(K,:)`, the
vanishing of the Schur complement of the pivot block, which says the pivot columns span
`range G`. -/
def IsPivotChart (G : Matrix n n ℝ) (e : κ → n) : Prop :=
  IsUnit (pivotBlock G e).det ∧ G = chartCol G e * (pivotBlock G e)⁻¹ * G.submatrix e id

omit [DecidableEq κ] in
/-- [proved-standard; formal-checked] Placing a vector at the pivot cells and applying `G` reads it
through the chart's columns. -/
theorem mulVec_spread (G : Matrix n n ℝ) (e : κ → n) (a : κ → ℝ) :
    G *ᵥ spread e a = chartCol G e *ᵥ a := by
  ext i
  simp only [mulVec, dotProduct, spread, chartCol, submatrix_apply, id, Finset.mul_sum, mul_ite,
    mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq]
  simp

omit [DecidableEq κ] in
/-- [proved-standard; formal-checked] A form paired with a vector placed at the pivots reads the
form at the pivots. -/
theorem dotProduct_spread (w : n → ℝ) (e : κ → n) (a : κ → ℝ) :
    w ⬝ᵥ spread e a = (w ∘ e) ⬝ᵥ a := by
  simp only [dotProduct, spread, Finset.mul_sum, mul_ite, mul_zero, Function.comp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq]
  simp

omit [Fintype n] [DecidableEq n] [DecidableEq κ] in
/-- [proved-standard; formal-checked] The chart's columns read at the pivots are the pivot block. -/
theorem chartCol_mulVec_comp (G : Matrix n n ℝ) (e : κ → n) (a : κ → ℝ) :
    (chartCol G e *ᵥ a) ∘ e = pivotBlock G e *ᵥ a := by
  funext k
  rfl

/-- [proved-standard; formal-checked] **The supported part lies in `range G`**: `v_s = G (spread
(G_KK⁻¹ v_K))`. -/
theorem supported_eq_mulVec (G : Matrix n n ℝ) (e : κ → n) (v : n → ℝ) :
    supported G e v = G *ᵥ spread e (chartCoeff G e v) := by
  rw [mulVec_spread, supported]

/-- [proved-standard; formal-checked] The supported part is a reading of `G`. -/
theorem supported_mem_range (G : Matrix n n ℝ) (e : κ → n) (v : n → ℝ) :
    ∃ u, G *ᵥ u = supported G e v :=
  ⟨_, (supported_eq_mulVec G e v).symm⟩

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] **The split** `v = v_s + ρ`. -/
theorem supported_add_openPart (G : Matrix n n ℝ) (e : κ → n) (v : n → ℝ) :
    supported G e v + openPart G e v = v := by
  rw [openPart, add_sub_cancel]

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] The supported part agrees with the reading on the pivots. -/
theorem supported_comp (G : Matrix n n ℝ) (e : κ → n) (hK : IsUnit (pivotBlock G e).det)
    (v : n → ℝ) : supported G e v ∘ e = v ∘ e := by
  rw [supported, chartCol_mulVec_comp, chartCoeff, mulVec_mulVec, mul_nonsing_inv _ hK,
    one_mulVec]

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] **`ρ_K = 0`**: the open part vanishes on the pivots. -/
theorem openPart_comp (G : Matrix n n ℝ) (e : κ → n) (hK : IsUnit (pivotBlock G e).det)
    (v : n → ℝ) : openPart G e v ∘ e = 0 := by
  have h := supported_comp G e hK v
  funext k
  have hk := congrFun h k
  simp only [Function.comp, Pi.zero_apply, openPart, Pi.sub_apply] at hk ⊢
  rw [hk, sub_self]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] In a pivot chart the supported part of a reading in `range G`
is the reading itself. -/
theorem supported_of_mem_range {G : Matrix n n ℝ} {e : κ → n} (hc : IsPivotChart G e)
    (u : n → ℝ) : supported G e (G *ᵥ u) = G *ᵥ u := by
  have hcomp : (G *ᵥ u) ∘ e = G.submatrix e id *ᵥ u := by
    funext k
    rfl
  rw [supported, chartCoeff, hcomp, mulVec_mulVec, mulVec_mulVec, ← hc.2]

/-- [proved-standard; formal-checked] **`ρ = 0` iff `v ∈ range G`**, in a pivot chart. -/
theorem openPart_eq_zero_iff {G : Matrix n n ℝ} {e : κ → n} (hc : IsPivotChart G e)
    (v : n → ℝ) : openPart G e v = 0 ↔ ∃ u, G *ᵥ u = v := by
  constructor
  · intro h
    refine ⟨spread e (chartCoeff G e v), ?_⟩
    rw [← supported_eq_mulVec]
    rw [openPart, sub_eq_zero] at h
    exact h.symm
  · rintro ⟨u, rfl⟩
    rw [openPart, supported_of_mem_range hc, sub_self]

end Chart

/-! ## 2. The bound for every form, the forms that agree on the cells, and the value in range -/

section Bound

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] A symmetric Gram pairs two vectors in either order. -/
theorem dotProduct_mulVec_comm {G : Matrix n n ℝ} (hsym : Gᵀ = G) (a b : n → ℝ) :
    a ⬝ᵥ (G *ᵥ b) = b ⬝ᵥ (G *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] A real positive semidefinite matrix is symmetric. -/
theorem transpose_eq_of_posSemidef {G : Matrix n n ℝ} (hG : G.PosSemidef) : Gᵀ = G := by
  have h := hG.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] A real positive semidefinite matrix has nonnegative energy. -/
theorem form_nonneg {G : Matrix n n ℝ} (hG : G.PosSemidef) (a : n → ℝ) : 0 ≤ a ⬝ᵥ (G *ᵥ a) := by
  simpa using hG.dotProduct_mulVec_nonneg a

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **Cauchy–Schwarz for a positive semidefinite Gram**:
`(aᵀGb)² ≤ (aᵀGa)(bᵀGb)`, read off the discriminant of `t ↦ (a + tb)ᵀG(a + tb) ≥ 0`. -/
theorem sq_form_le {G : Matrix n n ℝ} (hG : G.PosSemidef) (a b : n → ℝ) :
    (a ⬝ᵥ (G *ᵥ b)) ^ 2 ≤ (a ⬝ᵥ (G *ᵥ a)) * (b ⬝ᵥ (G *ᵥ b)) := by
  have hsym := transpose_eq_of_posSemidef hG
  have hq : ∀ x : ℝ, 0 ≤ (b ⬝ᵥ (G *ᵥ b)) * (x * x) + (2 * (a ⬝ᵥ (G *ᵥ b))) * x +
      (a ⬝ᵥ (G *ᵥ a)) := by
    intro x
    have h := form_nonneg hG (a + x • b)
    have e : (a + x • b) ⬝ᵥ (G *ᵥ (a + x • b)) = (b ⬝ᵥ (G *ᵥ b)) * (x * x) +
        (2 * (a ⬝ᵥ (G *ᵥ b))) * x + (a ⬝ᵥ (G *ᵥ a)) := by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      rw [dotProduct_mulVec_comm hsym b a]
      ring
    linarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

/-- [proved-standard; formal-checked] The form the chart places at the pivots has energy `h_K`. -/
theorem form_spread_chartCoeff {G : Matrix n n ℝ} {e : κ → n} (hK : IsUnit (pivotBlock G e).det)
    (v : n → ℝ) :
    spread e (chartCoeff G e v) ⬝ᵥ (G *ᵥ spread e (chartCoeff G e v)) = chartLeverage G e v := by
  rw [mulVec_spread, dotProduct_comm, dotProduct_spread, chartCol_mulVec_comp, chartCoeff,
    mulVec_mulVec, mul_nonsing_inv _ hK, one_mulVec, chartLeverage, chartCoeff]

/-- [proved-standard; formal-checked] `h_K ≥ 0` on a positive semidefinite Gram. -/
theorem chartLeverage_nonneg {G : Matrix n n ℝ} (hG : G.PosSemidef) {e : κ → n}
    (hK : IsUnit (pivotBlock G e).det) (v : n → ℝ) : 0 ≤ chartLeverage G e v := by
  rw [← form_spread_chartCoeff hK]
  exact form_nonneg hG _

/-- [proved-standard; formal-checked] **The leverage bounds every form**:
`|wᵀ v_s|² ≤ (wᵀ G w) · v_Kᵀ G_KK⁻¹ v_K` for every `w`, with no range assumption on `w`. -/
theorem sq_dotProduct_supported_le {G : Matrix n n ℝ} (hG : G.PosSemidef) {e : κ → n}
    (hK : IsUnit (pivotBlock G e).det) (v w : n → ℝ) :
    (w ⬝ᵥ supported G e v) ^ 2 ≤ (w ⬝ᵥ (G *ᵥ w)) * chartLeverage G e v := by
  rw [supported_eq_mulVec, ← form_spread_chartCoeff hK]
  exact sq_form_le hG _ _

/-- [proved-standard; formal-checked] **The bound is attained** at the form the chart places at the
pivots, `w = spread(G_KK⁻¹ v_K)`: it reads `v_s` at `h_K` with energy `h_K`. -/
theorem supported_bound_attained {G : Matrix n n ℝ} {e : κ → n}
    (hK : IsUnit (pivotBlock G e).det) (v : n → ℝ) :
    spread e (chartCoeff G e v) ⬝ᵥ supported G e v = chartLeverage G e v ∧
      spread e (chartCoeff G e v) ⬝ᵥ (G *ᵥ spread e (chartCoeff G e v)) =
        chartLeverage G e v := by
  refine ⟨?_, form_spread_chartCoeff hK v⟩
  rw [supported_eq_mulVec, form_spread_chartCoeff hK]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **Forms equal on the cells share `wᵀ v_s`.** For the Gram
`G = X Xᵀ` of the encounters (the columns of `X`), two forms that read every cell alike read the
supported part alike. -/
theorem dotProduct_eq_of_cells {ι : Type*} [Fintype ι] {G : Matrix n n ℝ} (X : Matrix n ι ℝ)
    (hX : G = X * Xᵀ) {w w' : n → ℝ} (h : w ᵥ* X = w' ᵥ* X) (u : n → ℝ) :
    w ⬝ᵥ (G *ᵥ u) = w' ⬝ᵥ (G *ᵥ u) := by
  rw [hX, ← mulVec_mulVec, dotProduct_mulVec, h, ← dotProduct_mulVec]

/-- [proved-standard; formal-checked] Forms equal on the cells share `wᵀ v_s`. -/
theorem dotProduct_supported_eq_of_cells {ι : Type*} [Fintype ι] {G : Matrix n n ℝ}
    (X : Matrix n ι ℝ) (hX : G = X * Xᵀ) {w w' : n → ℝ} (h : w ᵥ* X = w' ᵥ* X) (e : κ → n)
    (v : n → ℝ) : w ⬝ᵥ supported G e v = w' ⬝ᵥ supported G e v := by
  rw [supported_eq_mulVec]
  exact dotProduct_eq_of_cells X hX h _

/-- [proved-standard; formal-checked] Two forms equal on the cells differ on a reading only by
their difference paired with the open part: `wᵀv − w′ᵀv = (w − w′)ᵀ ρ`. -/
theorem dotProduct_sub_eq_openPart {ι : Type*} [Fintype ι] {G : Matrix n n ℝ}
    (X : Matrix n ι ℝ) (hX : G = X * Xᵀ) {w w' : n → ℝ} (h : w ᵥ* X = w' ᵥ* X) (e : κ → n)
    (v : n → ℝ) : w ⬝ᵥ v - w' ⬝ᵥ v = (w - w') ⬝ᵥ openPart G e v := by
  have hs := dotProduct_supported_eq_of_cells X hX h e v
  rw [openPart, sub_dotProduct, dotProduct_sub, dotProduct_sub, hs]
  ring

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] Adding a form the encounters do not see (`G n = 0`) leaves
`wᵀ v_s`, for a symmetric `G`. -/
theorem dotProduct_supported_add_ker {G : Matrix n n ℝ} (hsym : Gᵀ = G) {m : n → ℝ}
    (hm : G *ᵥ m = 0) (w u : n → ℝ) : (w + m) ⬝ᵥ (G *ᵥ u) = w ⬝ᵥ (G *ᵥ u) := by
  rw [add_dotProduct, dotProduct_mulVec_comm hsym m u, hm, dotProduct_zero, add_zero]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **In range the value does not depend on the generalized
inverse**: `(Gu)ᵀ G⁻ (Gu) = uᵀGu` for every `G⁻` with `G G⁻ G = G`. -/
theorem ginv_value_eq {G : Matrix n n ℝ} (hsym : Gᵀ = G) {Gm : Matrix n n ℝ}
    (hGm : EffectiveTension.IsGInv G Gm) (u : n → ℝ) :
    (G *ᵥ u) ⬝ᵥ (Gm *ᵥ (G *ᵥ u)) = u ⬝ᵥ (G *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec_comm hsym, mulVec_mulVec, mulVec_mulVec, hGm]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **In range the chart value is the energy**: in a pivot chart
of a symmetric `G`, `h_K(Gu) = uᵀGu`. -/
theorem chartLeverage_of_mem_range {G : Matrix n n ℝ} (hsym : Gᵀ = G) {e : κ → n}
    (hc : IsPivotChart G e) (u : n → ℝ) : chartLeverage G e (G *ᵥ u) = u ⬝ᵥ (G *ᵥ u) := by
  have hcomp : (G *ᵥ u) ∘ e = G.submatrix e id *ᵥ u := by
    funext k
    rfl
  have hC : u ᵥ* chartCol G e = G.submatrix e id *ᵥ u := by
    rw [← mulVec_transpose, chartCol, transpose_submatrix, hsym]
  have hG : G *ᵥ u = chartCol G e *ᵥ ((pivotBlock G e)⁻¹ *ᵥ (G.submatrix e id *ᵥ u)) := by
    conv_lhs => rw [hc.2]
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  rw [chartLeverage, chartCoeff, hcomp]
  conv_rhs => rw [hG, dotProduct_mulVec, hC]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **In range `h_K = vᵀ G⁻ v`** for every generalized inverse,
the Moore–Penrose `G⁺` among them. -/
theorem chartLeverage_eq_ginv {G : Matrix n n ℝ} (hsym : Gᵀ = G) {e : κ → n}
    (hc : IsPivotChart G e) {Gm : Matrix n n ℝ} (hGm : EffectiveTension.IsGInv G Gm)
    {v : n → ℝ} (hv : ∃ u, G *ᵥ u = v) : chartLeverage G e v = v ⬝ᵥ (Gm *ᵥ v) := by
  obtain ⟨u, rfl⟩ := hv
  rw [chartLeverage_of_mem_range hsym hc, ginv_value_eq hsym hGm]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **The chart value is chart-free in range**: two pivot charts
of one symmetric Gram give one leverage. -/
theorem chartLeverage_chart_free {κ' : Type*} [Fintype κ'] [DecidableEq κ'] {G : Matrix n n ℝ}
    (hsym : Gᵀ = G) {e : κ → n} {e' : κ' → n} (hc : IsPivotChart G e) (hc' : IsPivotChart G e')
    {v : n → ℝ} (hv : ∃ u, G *ᵥ u = v) : chartLeverage G e v = chartLeverage G e' v := by
  obtain ⟨u, rfl⟩ := hv
  rw [chartLeverage_of_mem_range hsym hc, chartLeverage_of_mem_range hsym hc']

/-- [proved-standard; formal-checked] An invertible rebase `x ↦ P x` carries a reading in `range G`
to one in `range (P G Pᵀ)`, through `u ↦ (Pᵀ)⁻¹ u`. -/
theorem rebase_reading {G : Matrix n n ℝ} (P : Matrix n n ℝ) (hP : IsUnit P.det) (u : n → ℝ) :
    Pᵀ *ᵥ ((Pᵀ)⁻¹ *ᵥ u) = u ∧ P *ᵥ (G *ᵥ u) = (P * G * Pᵀ) *ᵥ ((Pᵀ)⁻¹ *ᵥ u) := by
  have hPt : IsUnit Pᵀ.det := by rwa [det_transpose]
  have hu : Pᵀ *ᵥ ((Pᵀ)⁻¹ *ᵥ u) = u := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hPt, one_mulVec]
  refine ⟨hu, ?_⟩
  conv_lhs => rw [← hu]
  rw [mulVec_mulVec, mulVec_mulVec]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] The rebased Gram's energy is the Gram's energy at `Pᵀ u′`. -/
theorem rebase_form (G P : Matrix n n ℝ) (u : n → ℝ) :
    u ⬝ᵥ ((P * G * Pᵀ) *ᵥ u) = (Pᵀ *ᵥ u) ⬝ᵥ (G *ᵥ (Pᵀ *ᵥ u)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u P, ← mulVec_transpose]

/-- [proved-standard; formal-checked] **The value is invariant under an invertible rebase**: with
`x ↦ P x`, so `G ↦ P G Pᵀ` and `v ↦ P v`, `(Pv)ᵀ (PGPᵀ)⁻ (Pv) = vᵀ G⁻ v` in range, for every
generalized inverse of each. -/
theorem ginv_value_rebase {G : Matrix n n ℝ} (hsym : Gᵀ = G) (P : Matrix n n ℝ)
    (hP : IsUnit P.det) {Gm Gm' : Matrix n n ℝ} (hGm : EffectiveTension.IsGInv G Gm)
    (hGm' : EffectiveTension.IsGInv (P * G * Pᵀ) Gm') {v : n → ℝ} (hv : ∃ u, G *ᵥ u = v) :
    (P *ᵥ v) ⬝ᵥ (Gm' *ᵥ (P *ᵥ v)) = v ⬝ᵥ (Gm *ᵥ v) := by
  obtain ⟨u, rfl⟩ := hv
  obtain ⟨hu, hv'⟩ := rebase_reading (G := G) P hP u
  have hsym' : (P * G * Pᵀ)ᵀ = P * G * Pᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hsym, Matrix.mul_assoc]
  rw [hv', ginv_value_eq hsym' hGm', ginv_value_eq hsym hGm, rebase_form, hu]

/-- [proved-standard; formal-checked] **The chart value is invariant under an invertible rebase**:
a pivot chart of `G` and one of `P G Pᵀ` read the same leverage at `v` and `P v` in range. -/
theorem chartLeverage_rebase {κ' : Type*} [Fintype κ'] [DecidableEq κ'] {G : Matrix n n ℝ}
    (hsym : Gᵀ = G) (P : Matrix n n ℝ) (hP : IsUnit P.det) {e : κ → n} {e' : κ' → n}
    (hc : IsPivotChart G e) (hc' : IsPivotChart (P * G * Pᵀ) e') {v : n → ℝ}
    (hv : ∃ u, G *ᵥ u = v) : chartLeverage (P * G * Pᵀ) e' (P *ᵥ v) = chartLeverage G e v := by
  obtain ⟨u, rfl⟩ := hv
  obtain ⟨hu, hv'⟩ := rebase_reading (G := G) P hP u
  have hsym' : (P * G * Pᵀ)ᵀ = P * G * Pᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hsym, Matrix.mul_assoc]
  rw [hv', chartLeverage_of_mem_range hsym' hc', chartLeverage_of_mem_range hsym hc, rebase_form,
    hu]

end Bound

/-! ## 3. Readings in sequence: the determinant's product and the prequential identity -/

section Sequence

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] A row, a matrix and a column read as one pairing. -/
theorem replicateRow_mul_mul_replicateCol_apply (u v : n → ℝ) (M : Matrix n n ℝ) (i j : Unit) :
    (replicateRow Unit u * M * replicateCol Unit v) i j = u ⬝ᵥ (M *ᵥ v) := by
  rw [Matrix.mul_assoc, ← replicateCol_mulVec, replicateRow_mul_replicateCol_apply]

/-- [definition] The encounter Gram after `t` readings from the prior `G₀`:
`G_t = G₀ + Σ_(s<t) x_s x_sᵀ`. -/
def gramAfter (G₀ : Matrix n n ℝ) (x : ℕ → n → ℝ) (t : ℕ) : Matrix n n ℝ :=
  G₀ + ∑ s ∈ range t, vecMulVec (x s) (x s)

/-- [definition] The leverage of the `t`-th reading against the Gram it meets,
`h_t = x_tᵀ G_t⁻¹ x_t`. -/
noncomputable def lev (G₀ : Matrix n n ℝ) (x : ℕ → n → ℝ) (t : ℕ) : ℝ :=
  x t ⬝ᵥ ((gramAfter G₀ x t)⁻¹ *ᵥ x t)

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] One reading adds its outer product. -/
theorem gramAfter_succ (G₀ : Matrix n n ℝ) (x : ℕ → n → ℝ) (t : ℕ) :
    gramAfter G₀ x (t + 1) = gramAfter G₀ x t + vecMulVec (x t) (x t) := by
  rw [gramAfter, gramAfter, sum_range_succ, add_assoc]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] From a positive definite prior every Gram is positive
definite. -/
theorem posDef_gramAfter {G₀ : Matrix n n ℝ} (h₀ : G₀.PosDef) (x : ℕ → n → ℝ) :
    ∀ t, (gramAfter G₀ x t).PosDef := by
  intro t
  induction t with
  | zero => simpa [gramAfter] using h₀
  | succ t ih =>
    rw [gramAfter_succ]
    exact ih.add_posSemidef (by simpa using posSemidef_vecMulVec_self_star (x t))

/-- [proved-standard; formal-checked] Every leverage met from a positive definite prior is
nonnegative. -/
theorem lev_nonneg {G₀ : Matrix n n ℝ} (h₀ : G₀.PosDef) (x : ℕ → n → ℝ) (t : ℕ) :
    0 ≤ lev G₀ x t := by
  simpa [lev] using (posDef_gramAfter h₀ x t).inv.posSemidef.dotProduct_mulVec_nonneg (x t)

/-- [proved-standard; formal-checked] **One reading multiplies the determinant by `1 + h`**
(the matrix determinant lemma). -/
theorem det_gramAfter_succ {G₀ : Matrix n n ℝ} (h₀ : G₀.PosDef) (x : ℕ → n → ℝ) (t : ℕ) :
    (gramAfter G₀ x (t + 1)).det = (gramAfter G₀ x t).det * (1 + lev G₀ x t) := by
  have hu : IsUnit (gramAfter G₀ x t).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (posDef_gramAfter h₀ x t).isUnit
  rw [gramAfter_succ, vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow hu,
    det_unique (1 + replicateRow Unit (x t) * (gramAfter G₀ x t)⁻¹ * replicateCol Unit (x t)),
    Matrix.add_apply, one_apply_eq, replicateRow_mul_mul_replicateCol_apply, lev]

/-- [proved-standard; formal-checked] **`det G_N = det G₀ · Π_(t<N) (1 + h_t)`**. -/
theorem det_gramAfter {G₀ : Matrix n n ℝ} (h₀ : G₀.PosDef) (x : ℕ → n → ℝ) (N : ℕ) :
    (gramAfter G₀ x N).det = G₀.det * ∏ t ∈ range N, (1 + lev G₀ x t) := by
  induction N with
  | zero => simp [gramAfter]
  | succ N ih => rw [det_gramAfter_succ h₀, ih, prod_range_succ, mul_assoc]

/-- [proved-standard; formal-checked] **`Π_t (1 + h_t) = det G_N / det G₀`**. -/
theorem prod_one_add_lev {G₀ : Matrix n n ℝ} (h₀ : G₀.PosDef) (x : ℕ → n → ℝ) (N : ℕ) :
    ∏ t ∈ range N, (1 + lev G₀ x t) = (gramAfter G₀ x N).det / G₀.det := by
  rw [det_gramAfter h₀, mul_div_cancel_left₀ _ h₀.det_pos.ne']

/-- [definition] The covector's moment after `t` readings, `b_t = Σ_(s<t) y_s x_s`. -/
def momentAfter (x : ℕ → n → ℝ) (y : ℕ → ℝ) (t : ℕ) : n → ℝ := ∑ s ∈ range t, y s • x s

/-- [definition] The material fitted to the first `t` readings, `ŵ_t = G_t⁻¹ b_t`. -/
noncomputable def fitted (G₀ : Matrix n n ℝ) (x : ℕ → n → ℝ) (y : ℕ → ℝ) (t : ℕ) : n → ℝ :=
  (gramAfter G₀ x t)⁻¹ *ᵥ momentAfter x y t

/-- [definition] The prequential residual `r_t = y_t − x_tᵀ ŵ_t`: the `t`-th reading against the
material fitted before it. -/
noncomputable def prequentialResidual (G₀ : Matrix n n ℝ) (x : ℕ → n → ℝ) (y : ℕ → ℝ) (t : ℕ) :
    ℝ :=
  y t - x t ⬝ᵥ fitted G₀ x y t

/-- [definition] The least penalized residual after `t` readings,
`E_t = Σ_(s<t) y_s² − b_tᵀ ŵ_t`. -/
noncomputable def leastResidual (G₀ : Matrix n n ℝ) (x : ℕ → n → ℝ) (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ range t, y s ^ 2 - momentAfter x y t ⬝ᵥ fitted G₀ x y t

/-- [definition] The penalized residual of a material `w` over the first `N` readings,
`Σ_(t<N) (y_t − x_tᵀ w)² + wᵀ G₀ w`. -/
def penalized (G₀ : Matrix n n ℝ) (x : ℕ → n → ℝ) (y : ℕ → ℝ) (N : ℕ) (w : n → ℝ) : ℝ :=
  ∑ t ∈ range N, (y t - x t ⬝ᵥ w) ^ 2 + w ⬝ᵥ (G₀ *ᵥ w)

/-- [proved-standard; formal-checked] **One reading's step of the quadratic value**: with
`G′ = G + x xᵀ`, `b′ = b + y x`, `b′ᵀ G′⁻¹ b′ = bᵀ G⁻¹ b + y² − (y − xᵀG⁻¹b)² / (1 + xᵀG⁻¹x)`. -/
theorem value_add_reading {G : Matrix n n ℝ} (hG : G.PosDef) (b xv : n → ℝ) (yv : ℝ) :
    (b + yv • xv) ⬝ᵥ ((G + vecMulVec xv xv)⁻¹ *ᵥ (b + yv • xv)) =
      b ⬝ᵥ (G⁻¹ *ᵥ b) + yv ^ 2 -
        (yv - xv ⬝ᵥ (G⁻¹ *ᵥ b)) ^ 2 / (1 + xv ⬝ᵥ (G⁻¹ *ᵥ xv)) := by
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hG' : (G + vecMulVec xv xv).PosDef :=
    hG.add_posSemidef (by simpa using posSemidef_vecMulVec_self_star xv)
  have hG'u : IsUnit (G + vecMulVec xv xv).det := (Matrix.isUnit_iff_isUnit_det _).mp hG'.isUnit
  have hsym : Gᵀ = G := transpose_eq_of_posSemidef hG.posSemidef
  have hsymi : (G⁻¹)ᵀ = G⁻¹ := by rw [transpose_nonsing_inv, hsym]
  set a := G⁻¹ *ᵥ b with ha
  set g := G⁻¹ *ᵥ xv with hg
  set p := xv ⬝ᵥ a with hp
  set h := xv ⬝ᵥ g with hh
  have hh0 : 0 ≤ h := by simpa using hG.inv.posSemidef.dotProduct_mulVec_nonneg xv
  have h1 : 1 + h ≠ 0 := by positivity
  set k := (yv - p) / (1 + h) with hk
  have hGa : G *ᵥ a = b := by rw [ha, mulVec_mulVec, mul_nonsing_inv _ hGu, one_mulVec]
  have hGg : G *ᵥ g = xv := by rw [hg, mulVec_mulVec, mul_nonsing_inv _ hGu, one_mulVec]
  have hbg : b ⬝ᵥ g = p := by rw [hg, hp, ha, dotProduct_mulVec_comm hsymi]
  have hz : (G + vecMulVec xv xv) *ᵥ (a + k • g) = b + yv • xv := by
    rw [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul, mulVec_add, mulVec_smul, hGa, hGg,
      dotProduct_add, dotProduct_smul, smul_eq_mul, ← hp, ← hh, add_assoc, ← add_smul]
    congr 2
    rw [hk]
    field_simp
    ring
  have hzz : (G + vecMulVec xv xv)⁻¹ *ᵥ (b + yv • xv) = a + k • g := by
    rw [← hz, mulVec_mulVec, nonsing_inv_mul _ hG'u, one_mulVec]
  rw [hzz, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, smul_eq_mul, hbg, ← hp, ← hh, hk]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The least residual grows by the prequential share**:
`E_(t+1) = E_t + r_t² / (1 + h_t)`. -/
theorem leastResidual_succ {G₀ : Matrix n n ℝ} (h₀ : G₀.PosDef) (x : ℕ → n → ℝ) (y : ℕ → ℝ)
    (t : ℕ) : leastResidual G₀ x y (t + 1) =
      leastResidual G₀ x y t + prequentialResidual G₀ x y t ^ 2 / (1 + lev G₀ x t) := by
  have hb : momentAfter x y (t + 1) = momentAfter x y t + y t • x t := by
    rw [momentAfter, momentAfter, sum_range_succ]
  rw [leastResidual, leastResidual, fitted, fitted, hb, gramAfter_succ,
    value_add_reading (posDef_gramAfter h₀ x t), sum_range_succ, prequentialResidual, fitted,
    lev]
  ring

/-- [proved-standard; formal-checked] **The prequential sum is the least residual**:
`Σ_(t<N) r_t² / (1 + h_t) = E_N`. -/
theorem sum_prequential_eq {G₀ : Matrix n n ℝ} (h₀ : G₀.PosDef) (x : ℕ → n → ℝ) (y : ℕ → ℝ)
    (N : ℕ) : ∑ t ∈ range N, prequentialResidual G₀ x y t ^ 2 / (1 + lev G₀ x t) =
      leastResidual G₀ x y N := by
  induction N with
  | zero => simp [leastResidual, momentAfter]
  | succ N ih => rw [sum_range_succ, ih, leastResidual_succ h₀]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] The penalized residual expanded on the moments:
`Σ y² − 2 b_Nᵀ w + wᵀ G_N w`. -/
theorem penalized_eq (G₀ : Matrix n n ℝ) (x : ℕ → n → ℝ) (y : ℕ → ℝ) (N : ℕ) (w : n → ℝ) :
    penalized G₀ x y N w = ∑ t ∈ range N, y t ^ 2 - 2 * (momentAfter x y N ⬝ᵥ w) +
      w ⬝ᵥ (gramAfter G₀ x N *ᵥ w) := by
  induction N with
  | zero => simp [penalized, momentAfter, gramAfter]
  | succ N ih =>
    have hb : momentAfter x y (N + 1) = momentAfter x y N + y N • x N := by
      rw [momentAfter, momentAfter, sum_range_succ]
    have hp : penalized G₀ x y (N + 1) w = penalized G₀ x y N w + (y N - x N ⬝ᵥ w) ^ 2 := by
      rw [penalized, penalized, sum_range_succ]
      ring
    rw [hp, ih, hb, gramAfter_succ, add_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_add,
      dotProduct_smul, smul_eq_mul, add_dotProduct, smul_dotProduct, smul_eq_mul, sum_range_succ,
      dotProduct_comm w (x N)]
    ring

/-- [proved-standard; formal-checked] **Completing the square**: the penalized residual of `w`
exceeds the least one by `(w − ŵ_N)ᵀ G_N (w − ŵ_N)`. -/
theorem penalized_sub_leastResidual {G₀ : Matrix n n ℝ} (h₀ : G₀.PosDef) (x : ℕ → n → ℝ)
    (y : ℕ → ℝ) (N : ℕ) (w : n → ℝ) :
    penalized G₀ x y N w - leastResidual G₀ x y N =
      (w - fitted G₀ x y N) ⬝ᵥ (gramAfter G₀ x N *ᵥ (w - fitted G₀ x y N)) := by
  have hG := posDef_gramAfter h₀ x N
  have hGu : IsUnit (gramAfter G₀ x N).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hsym : (gramAfter G₀ x N)ᵀ = gramAfter G₀ x N := transpose_eq_of_posSemidef hG.posSemidef
  have hGa : gramAfter G₀ x N *ᵥ fitted G₀ x y N = momentAfter x y N := by
    rw [fitted, mulVec_mulVec, mul_nonsing_inv _ hGu, one_mulVec]
  rw [penalized_eq, leastResidual, mulVec_sub, hGa, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    dotProduct_mulVec_comm hsym (fitted G₀ x y N) w, hGa, dotProduct_comm w (momentAfter x y N),
    dotProduct_comm (fitted G₀ x y N) (momentAfter x y N)]
  ring

/-- [proved-standard; formal-checked] **The prequential identity**: from a positive definite prior,
`Σ_(t<N) r_t² / (1 + h_t)` is the least penalized residual
`min_w Σ_(t<N) (y_t − x_tᵀ w)² + wᵀ G₀ w`, attained at `ŵ_N`. -/
theorem prequential_isLeast {G₀ : Matrix n n ℝ} (h₀ : G₀.PosDef) (x : ℕ → n → ℝ) (y : ℕ → ℝ)
    (N : ℕ) : IsLeast (Set.range (penalized G₀ x y N))
      (∑ t ∈ range N, prequentialResidual G₀ x y t ^ 2 / (1 + lev G₀ x t)) := by
  rw [sum_prequential_eq h₀]
  refine ⟨⟨fitted G₀ x y N, ?_⟩, ?_⟩
  · have h := penalized_sub_leastResidual h₀ x y N (fitted G₀ x y N)
    rw [sub_self, mulVec_zero, dotProduct_zero, sub_eq_zero] at h
    exact h
  · rintro _ ⟨w, rfl⟩
    have h := penalized_sub_leastResidual h₀ x y N w
    have h' := form_nonneg (posDef_gramAfter h₀ x N).posSemidef (w - fitted G₀ x y N)
    linarith

/-- [proved-standard; formal-checked] **The unit prior**:
`Σ_t r_t² / (1 + h_t) = min_w |y − Xw|² + wᵀw`, and `Π_t (1 + h_t) = det G_N`. -/
theorem prequential_unit_prior (x : ℕ → n → ℝ) (y : ℕ → ℝ) (N : ℕ) :
    IsLeast (Set.range fun w => ∑ t ∈ range N, (y t - x t ⬝ᵥ w) ^ 2 + w ⬝ᵥ w)
        (∑ t ∈ range N, prequentialResidual 1 x y t ^ 2 / (1 + lev 1 x t)) ∧
      ∏ t ∈ range N, (1 + lev 1 x t) = (gramAfter 1 x N).det := by
  refine ⟨?_, ?_⟩
  · have hf : penalized 1 x y N = fun w => ∑ t ∈ range N, (y t - x t ⬝ᵥ w) ^ 2 + w ⬝ᵥ w := by
      funext w
      simp [penalized]
    rw [← hf]
    exact prequential_isLeast PosDef.one x y N
  · rw [prod_one_add_lev PosDef.one, det_one, div_one]

end Sequence

/-! ## 4. The bordered minors a fraction-free elimination stores -/

section Bordered

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] **The bordered corner**:
`det [[G_KK, v_K], [v_Kᵀ, 0]] = −Δ · h_K`, with `Δ = det G_KK`. -/
theorem det_bordered_corner {G : Matrix n n ℝ} {e : κ → n} (hK : IsUnit (pivotBlock G e).det)
    (v : n → ℝ) :
    (fromBlocks (pivotBlock G e) (replicateCol Unit (v ∘ e)) (replicateRow Unit (v ∘ e))
      (0 : Matrix Unit Unit ℝ)).det = -((pivotBlock G e).det * chartLeverage G e v) := by
  let _ := invertibleOfIsUnitDet _ hK
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_unique (n := Unit), Matrix.sub_apply,
    Matrix.zero_apply, replicateRow_mul_mul_replicateCol_apply, chartLeverage, chartCoeff]
  ring

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] **A passed pivot's border entry**:
`det [[G_KK, v_K], [G_(p,K), v_p]] = Δ · ρ_p`, the open part carried whole at `p`. -/
theorem det_bordered_passed {G : Matrix n n ℝ} {e : κ → n} (hK : IsUnit (pivotBlock G e).det)
    (v : n → ℝ) (p : n) :
    (fromBlocks (pivotBlock G e) (replicateCol Unit (v ∘ e))
      (replicateRow Unit fun k => G p (e k)) (of fun _ _ => v p : Matrix Unit Unit ℝ)).det =
      (pivotBlock G e).det * openPart G e v p := by
  let _ := invertibleOfIsUnitDet _ hK
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_unique (n := Unit), Matrix.sub_apply, of_apply,
    replicateRow_mul_mul_replicateCol_apply]
  rfl

end Bordered

/-! ## 5. The witness: the pseudo-inverse bound fails off range, the chart's holds with equality -/

section Witness

/-- [definition] The witness Gram `[[1, 1], [1, 1]]`. -/
def witnessGram : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

/-- [definition] Its Moore–Penrose inverse `G/4`. -/
noncomputable def witnessPinv : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 4, 1 / 4; 1 / 4, 1 / 4]

/-- [proved-derived; formal-checked] `G/4` is the Moore–Penrose inverse of the witness:
`G G⁺ G = G`, `G⁺ G G⁺ = G⁺`, and `G G⁺` is symmetric. -/
theorem witnessPinv_laws : EffectiveTension.IsGInv witnessGram witnessPinv ∧
    witnessPinv * witnessGram * witnessPinv = witnessPinv ∧
    (witnessGram * witnessPinv)ᵀ = witnessGram * witnessPinv := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witnessGram, witnessPinv, Matrix.mul_apply, Fin.sum_univ_two] <;>
      norm_num

/-- [proved-derived; formal-checked] **GPT-6's example.** With `G = [[1, 1], [1, 1]]` and
`w = c = (1, 0)`, outside `range G`: `wᵀc = 1` against the pseudo-inverse bound
`√((wᵀGw)(cᵀG⁺c)) = 1/2`, while the chart on the first cell reads `h_K = 1`, `wᵀ v_s = 1`, and holds
`|wᵀ v_s|² ≤ (wᵀGw) h_K` with equality. -/
theorem witness_bound :
    (![1, 0] ⬝ᵥ (![1, 0] : Fin 2 → ℝ)) ^ 2 = 1 ∧
      (![1, 0] ⬝ᵥ (witnessGram *ᵥ ![1, 0])) * (![1, 0] ⬝ᵥ (witnessPinv *ᵥ ![1, 0])) = 1 / 4 ∧
      chartLeverage witnessGram ![0] ![1, 0] = 1 ∧
      ![1, 0] ⬝ᵥ supported witnessGram ![0] ![1, 0] = 1 ∧
      (![1, 0] ⬝ᵥ supported witnessGram ![0] ![1, 0]) ^ 2 =
        (![1, 0] ⬝ᵥ (witnessGram *ᵥ ![1, 0])) * chartLeverage witnessGram ![0] ![1, 0] := by
  have hP : pivotBlock witnessGram ![0] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [pivotBlock, witnessGram]
  have hL : chartLeverage witnessGram ![0] ![1, 0] = 1 := by
    rw [chartLeverage, chartCoeff, hP, inv_one, one_mulVec]
    simp [dotProduct]
  have hS : ![1, 0] ⬝ᵥ supported witnessGram ![0] ![1, 0] = 1 := by
    rw [supported, chartCoeff, hP, inv_one, one_mulVec]
    simp [chartCol, witnessGram, mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨by simp [dotProduct, Fin.sum_univ_two], ?_, hL, hS, ?_⟩
  · simp [witnessGram, witnessPinv, mulVec, dotProduct, Fin.sum_univ_two]
  · rw [hS, hL]
    simp [witnessGram, mulVec, dotProduct, Fin.sum_univ_two]

end Witness

end Holonics.HNN.ReadingLeverage
