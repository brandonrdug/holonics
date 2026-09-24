import ElementaryHolonics.Millennium.RealizedMillenniumForms
import ElementaryHolonics.Millennium.HodgeIndex
import ElementaryHolonics.Millennium.Aperture

/-!
# Two realizer joints: the height is a Hodge-index complement, and the aperture is a rank bound

`Pivots.theRealizedFormIsDefinite` is the mechanism of the whole coupling: **a form is definite
because it is the pullback of the anchor along an injection** — realization causes placement.
This file exhibits two realizers.

* **Birch–Swinnerton-Dyer ⇐ Hodge.**  The rank-12 Mestre height form of
  `RealizedMillenniumForms` is realized: `realizer v = (√dᵢ · Lᵢ v)ᵢ` with the twelve pivots `dᵢ`
  and elimination forms `Lᵢ` of its exact `LDLᵀ`, and `realizer_preserves` shows
  `⟪realizer x, realizer y⟫ = mestreForm.B x y`.  So `mestreForm_definite_by_realization` derives
  definiteness from `theRealizedFormIsDefinite` instead of the coordinate drain — the height form
  is definite *because* it is realized.  Then `mestreForm_eq_neg_hodge`: embedding the realized
  carrier as the orthogonal complement of an ample direction `e₀` in one more dimension,
  `mestreForm.B v v = −(hodgeForm e₀).B (ι v) (ι v)`.  The height form is literally the negated
  Hodge-index complement form (`HodgeIndex.theComplementIsNegativeDefinite`): Shioda's theorem —
  the Mordell–Weil height is the negative of the intersection form on the complement of the trivial
  lattice — in its linear shell, on an exact rank-12 instance.  BSD's positivity is a pullback of
  Hodge's.

* **P vs NP ⇐ the Gram.**  `Aperture.theFamilyTooSmallCollapses` says `|Y|^{|F|} < |X|` forces two
  members of the population to collapse under every reading.  On the Gram form of
  `RealizedMillenniumForms` the same statement is a rank bound: `n` readings in a carrier of
  dimension `m < n` cannot be linearly independent, so `gramForm w` is not definite and a nonzero
  null circulation exists (`gramForm_not_definite_of_dim_lt`, `gramForm_collapse_of_dim_lt`).  The
  aperture the population demands is the dimension of the carrier, and *definite ⟺ separating* is
  the same theorem on both rows.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.RealizerJoints

open Soma.Holonics.Millennium.MillenniumCoupling
open Soma.Holonics.Millennium.RealizedMillenniumForms
open Soma.Holonics.Millennium.Pivots
open Soma.Holonics.Millennium.HodgeIndex
open Finset

/-! ## Joint 1: the height form is a pullback of the anchor -/

/-- The twelve pivots of the exact `LDLᵀ` of the height Gram. -/
def pivot : Fin 12 → ℝ := ![(3 : ℝ), (11/3 : ℝ), (24/11 : ℝ), (23/8 : ℝ), (45/23 : ℝ), (13/5 : ℝ), (24/13 : ℝ), (59/24 : ℝ), (105/59 : ℝ), (83/35 : ℝ), (144/83 : ℝ), (7/12 : ℝ)]

theorem pivot_pos (i : Fin 12) : 0 < pivot i := by
  fin_cases i <;> norm_num [pivot]

theorem sq_sqrt_pivot (i : Fin 12) : Real.sqrt (pivot i) ^ 2 = pivot i :=
  Real.sq_sqrt (le_of_lt (pivot_pos i))

/-- The unit upper-triangular factor: row `i` carries the coefficients of the elimination form
`Lᵢ`. -/
def U : Fin 12 → Fin 12 → ℝ :=
  ![![(1 : ℝ), (1/3 : ℝ), (2/3 : ℝ), (1/3 : ℝ), (2/3 : ℝ), (1/3 : ℝ), (2/3 : ℝ), (1/3 : ℝ), (2/3 : ℝ), (1/3 : ℝ), (2/3 : ℝ), (1/2 : ℝ)],
    ![(0 : ℝ), (1 : ℝ), (7/11 : ℝ), (5/11 : ℝ), (4/11 : ℝ), (5/11 : ℝ), (4/11 : ℝ), (5/11 : ℝ), (4/11 : ℝ), (5/11 : ℝ), (4/11 : ℝ), (9/22 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (1 : ℝ), (1/8 : ℝ), (3/8 : ℝ), (1/8 : ℝ), (3/8 : ℝ), (1/8 : ℝ), (3/8 : ℝ), (1/8 : ℝ), (3/8 : ℝ), (-5/24 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (13/23 : ℝ), (7/23 : ℝ), (5/23 : ℝ), (7/23 : ℝ), (5/23 : ℝ), (7/23 : ℝ), (5/23 : ℝ), (-1/23 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (1/15 : ℝ), (4/15 : ℝ), (1/15 : ℝ), (4/15 : ℝ), (1/15 : ℝ), (4/15 : ℝ), (1/10 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (7/13 : ℝ), (3/13 : ℝ), (2/13 : ℝ), (3/13 : ℝ), (2/13 : ℝ), (9/26 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (1/24 : ℝ), (5/24 : ℝ), (1/24 : ℝ), (5/24 : ℝ), (1/3 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (31/59 : ℝ), (11/59 : ℝ), (7/59 : ℝ), (-8/59 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (1/35 : ℝ), (6/35 : ℝ), (1/210 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (43/83 : ℝ), (-19/166 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (7/12 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ)]]

/-- The elimination forms as a family. -/
def form : Fin 12 → (Fin 12 → ℝ) → ℝ := ![L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]

set_option maxHeartbeats 4000000 in
theorem U_row (i : Fin 12) (x : Fin 12 → ℝ) : (∑ j, U i j * x j) = form i x := by
  fin_cases i <;> simp [U, form, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, Fin.sum_univ_succ] <;> ring

/-- [definition] **The realizer** `v ↦ (√dᵢ · Lᵢ v)ᵢ`. -/
def realizer : Carrier 12 →L[ℝ] Carrier 12 :=
  LinearMap.toContinuousLinearMap (matrixMap (fun i j => Real.sqrt (pivot i) * U i j))

set_option maxHeartbeats 4000000 in
/-- [proved-derived; formal-checked] The realizer's squared norm is the height. -/
theorem realizer_norm_sq (v : Carrier 12) : ‖realizer v‖ ^ 2 = QR v.ofLp := by
  rw [norm_sq_carrier]
  simp only [realizer, LinearMap.coe_toContinuousLinearMap', matrixMap_apply]
  have hrow : ∀ i, (∑ j, Real.sqrt (pivot i) * U i j * v.ofLp j) ^ 2
      = pivot i * form i v.ofLp ^ 2 := by
    intro i
    have hfactor : (∑ j, Real.sqrt (pivot i) * U i j * v.ofLp j)
        = Real.sqrt (pivot i) * ∑ j, U i j * v.ofLp j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfactor, mul_pow, sq_sqrt_pivot, U_row]
  simp only [hrow]
  rw [QR_sumOfSquares]
  simp [Fin.sum_univ_succ, form, pivot]
  ring

/-- Polarization for a receiver form: the bilinear reading from the diagonal. -/
theorem receiverForm_polar {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (G : ReceiverForm W) (x y : W) :
    G.B (x + y) (x + y) = G.B x x + 2 * G.B x y + G.B y y := by
  simp only [ReceiverForm.B, map_add, inner_add_left, inner_add_right]
  have h : inner ℝ (G.T y) x = inner ℝ (G.T x) y := by
    rw [G.selfAdjoint y x, real_inner_comm]
  rw [h]
  ring

/-- [proved-derived; formal-checked] A map whose squared norm is the diagonal reading preserves
the whole form. -/
theorem realization_of_diagonal {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (G : ReceiverForm W) (f : W →L[ℝ] V) (h : ∀ v, ‖f v‖ ^ 2 = G.B v v) (x y : W) :
    inner ℝ (f x) (f y) = G.B x y := by
  have h1 := h (x + y)
  have h2 := h x
  have h3 := h y
  rw [map_add, norm_add_sq_real, receiverForm_polar] at h1
  linarith

/-- [proved-derived; formal-checked] **The realizer preserves the height form.** -/
theorem realizer_preserves (x y : Carrier 12) :
    inner ℝ (realizer x) (realizer y) = mestreForm.B x y :=
  realization_of_diagonal mestreForm realizer
    (fun v => by rw [realizer_norm_sq, mestreForm_reading]) x y

theorem realizer_injective (x : Carrier 12) (hx : realizer x = 0) : x = 0 := by
  have h : ‖realizer x‖ ^ 2 = 0 := by rw [hx]; simp
  rw [realizer_norm_sq] at h
  have := QR_anisotropic _ h
  ext i
  have := congrFun this i
  simpa using this

/-- [proved-derived; formal-checked] **Realization causes placement, on the BSD row**: the height
form is definite because it is realized. -/
theorem mestreForm_definite_by_realization : mestreForm.IsDefinite :=
  theRealizedFormIsDefinite mestreForm realizer realizer_preserves realizer_injective

theorem mestreForm_positive_by_realization : mestreForm.IsPositive :=
  theRealizedFormIsPositive mestreForm realizer realizer_preserves

/-! ## Joint 1, continued: the height is the negated Hodge-index complement -/

/-- The ample direction in one more dimension. -/
def ample : Carrier 13 := WithLp.toLp 2 (fun i => if i = 0 then 1 else 0)

/-- The realized carrier embedded as the orthogonal complement of the ample direction. -/
def embedMap : Carrier 12 →ₗ[ℝ] Carrier 13 where
  toFun v := WithLp.toLp 2 (fun i => Fin.cases 0 (fun j => (realizer v).ofLp j) i)
  map_add' := by
    intro x y
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' := by
    intro c x
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem embed_orthogonal (v : Carrier 12) : (inner ℝ ample (embedMap v) : ℝ) = 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp [ample, embedMap]

theorem embed_norm_sq (v : Carrier 12) : ‖embedMap v‖ ^ 2 = ‖realizer v‖ ^ 2 := by
  rw [norm_sq_carrier, norm_sq_carrier, Fin.sum_univ_succ]
  simp [embedMap]

/-- [proved-derived; formal-checked] **The height form is the negated Hodge-index complement
form**: `mestreForm.B v v = −(hodgeForm ample).B (ι v) (ι v)`.  Shioda's theorem in its linear
shell — the Mordell–Weil height is minus the intersection form on the complement of the trivial
lattice — and therefore the BSD row's positivity is a pullback of the Hodge row's. -/
theorem mestreForm_eq_neg_hodge (v : Carrier 12) :
    mestreForm.B v v = -(hodgeForm ample).B (embedMap v) (embedMap v) := by
  rw [theComplementIsNegativeDefinite (embed_orthogonal v), embed_norm_sq, realizer_norm_sq,
    mestreForm_reading]
  ring

/-! ## Joint 2: the aperture is a rank bound -/

/-- [proved-derived; formal-checked] **Too many readings for the carrier collapse**: `n` readings
in a carrier of dimension `m < n` cannot be linearly independent, so their Gram form is not
definite — `Aperture.theFamilyTooSmallCollapses` as a rank bound on the same form the other rows
use. -/
theorem gramForm_not_definite_of_dim_lt {n m : ℕ} (w : Fin n → Carrier m) (h : m < n) :
    ¬ (gramForm w).IsDefinite := by
  rw [gramForm_definite_iff_linearIndependent]
  intro hli
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, finrank_euclideanSpace_fin] at hcard
  omega

/-- [proved-derived; formal-checked] The collapse, exhibited: a nonzero circulation the Gram form
reads as nothing. -/
theorem gramForm_collapse_of_dim_lt {n m : ℕ} (w : Fin n → Carrier m) (h : m < n) :
    ∃ c : Carrier n, c ≠ 0 ∧ (gramForm w).B c c = 0 := by
  have hnot := gramForm_not_definite_of_dim_lt w h
  unfold ReceiverForm.IsDefinite at hnot
  push Not at hnot
  obtain ⟨c, hc, hne⟩ := hnot
  exact ⟨c, hne, hc⟩

section Audit

#print axioms realizer_preserves
#print axioms mestreForm_definite_by_realization
#print axioms mestreForm_eq_neg_hodge
#print axioms gramForm_not_definite_of_dim_lt
#print axioms gramForm_collapse_of_dim_lt

end Audit

end Soma.Holonics.Millennium.RealizerJoints
