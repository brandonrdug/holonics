import Holonics.HNN.LatticeDeposit
import Holonics.HNN.Normal
import Holonics.Holon.Cayley

/-!
# HNN.LatticeWord: the word's transients and inverses on declared lattices, certified residuals

[definition; agent-inferred] Decision 24 of the step 4 design (`docs/plans/THE_REBUILD.md`): every
transient and every inverse inside the HNN is carried on a declared lattice with a certified
residual. Exact rational inverses (each ring's Cayley element `2(I − E/2)⁻¹ − I`, written here
with `K = E/2` as `2(I − K)⁻¹ − I`; the contact solve `m⁻¹`; each normal law's `H⁻¹`) compound
their determinant denominators across ticks. CLAUDE.md's exact-representation law says what to do:
"When a value outgrows its carrier, it is rebased, factored or re-represented with its decoder and
residual." The lattice, its nearest-point division and its remainder are `HNN/LatticeDeposit`'s
(`unit`, `OnLattice`, `quot`, `rem`, `div_rem_spec`, `rem_bounds`); nothing is restated.

```text
inverse chart   X̂ ≈ A⁻¹ on 2^(−L)ℤ ,  R = I − A X̂ ,  certificate ‖R‖ ≤ δ
refinement      X' = X̂(2I − A X̂) = X̂(I + R) ,       I − A X' = R²            (exact)
rounding        X'' = X' + Δ ,  |Δ_ij| ≤ 2^(−L)/2 ,   I − A X'' = R² − A Δ
                ‖I − A X''‖∞ ≤ δ² + ‖A‖∞ · n · 2^(−L)/2
transient       x_t + r_(t+1) = y_t + r_t ,  x_t ∈ 2^(−L)ℤ ,  r ∈ [−u/2, u/2)
                Σ_(t<T) x_t + r_T = Σ_(t<T) y_t + r_0          (the word releases r_T)
adjoint         ⟨λ, M̂ x⟩ = ⟨M̂ᵀλ, x⟩ ,  ‖Mᵀλ − M̂ᵀλ‖₁ ≤ ‖M − M̂‖∞ ‖λ‖₁
balance         Ĉ = C + E ,  CᵀC = I :  |Ĉx|² − |x|² = 2⟨Cx, Ex⟩ + |Ex|²
```

In HNN terms: the chart is the executed operator; the residual is released and reported; the
device executes integer products. Every norm here is exact in `ℚ`: the ℓ∞ operator norm
`rowNorm` (the largest absolute row sum), the covector's ℓ1 norm `l1` (its dual), and the squared
Frobenius norm `frobSq`; a certificate is a declared rational bound, never a float.

[proved-derived; formal-checked] What is proved.

1. **Newton–Schulz squares the residual** (`newton_schulz_right`, `newton_schulz_left`), in any
   ring, with no commutation hypothesis: `X' = X(2 − AX) = (2 − XA)X` squares both the right
   residual `1 − AX` and the left residual `1 − XA`. `k` refinements give `R^(2^k)`
   (`newton_schulz_iter_right`, `newton_schulz_iter_left`) and `‖R_k‖∞ ≤ ‖R‖∞^(2^k)`
   (`newton_schulz_iter_rowNorm`). The solve charts (the Cayley element, the contact solve) read
   the right residual, the certificate of the equation `A(X̂b) − b = −Rb`; the prox step reads the
   left one (§6).
2. **The rounded refinement keeps a certified residual** (`rounded_refinement_residual`,
   `rounded_refinement_certificate`, and their left forms): `1 − A(X' + Δ) = R² − AΔ`, so the
   lattice chart of `X'` has `‖1 − AX''‖∞ ≤ ‖R‖∞² + ‖A‖∞·n·u/2`, from `rem_bounds`. The
   certificate does not grow: for `c ≤ 1/2` with twice the rounding term below `c`, a start at
   most `c` stays at most `c` under every rounded refinement (`roundedIter_certificate`). A warm
   start after a deposit `A → A + D` adds `‖D‖∞‖X̂‖∞` (`warm_start_certificate`). A certified chart
   is within `‖X̂‖∞δ/(1 − δ)` of the exact inverse (`inverse_chart_deviation`).
3. **Error feedback** (`feedback_tick`, `feedback_accounting`, `feedback_accounting_zero`): images
   `y_t` split at the nearest lattice point with the carried remainder; the values stay on the
   lattice (`feedback_onLattice`), the remainder in its half-open cell (`feedback_rem_bounds`),
   each tick moves by less than one unit (`feedback_tick_deviation`), and the partial sums track
   the exact images within half a unit however long the word (`feedback_sum_within_half_unit`).
   The carried word, whose images are a tick map applied to the carried state, is the instance
   (`carriedWord_rem_eq`, `carriedWord_state_eq`, `carried_word_accounting`).
4. **The executed adjoint** (`executed_adjoint_pairing`, `executed_adjoint_unique`): `M̂ᵀλ` is the
   only covector that pairs exactly with the executed chart; the exact adjoint leaves the defect
   `⟨λ, (M̂ − M)x⟩` (`exact_adjoint_pairing_defect`). The covector's deviation is
   `‖Mᵀλ − M̂ᵀλ‖₁ ≤ ‖M − M̂‖∞‖λ‖₁` (`executed_adjoint_deviation`); through a certified inverse
   chart, `≤ ‖X̂‖∞δ/(1 − δ)·‖λ‖₁` (`inverse_chart_adjoint_deviation`).
5. **The power balance up to the residual** (`chart_energy_identity`, `chart_energy_deviation`):
   for any `C` with `CᵀC = 1` and chart `Ĉ = C + E`, `|Ĉx|² − |x|² = 2⟨Cx, Ex⟩ + |Ex|²` exactly, and
   `|Ex|² ≤ ε²|x|²` bounds the deviation by `(2ε + ε²)|x|²`. For the Cayley element of a skew `K`,
   `C = 2(1 − K)⁻¹ − 1` is orthogonal over any commutative ring (`cayley_chart_orthogonal`; the
   complex and real owners are `Holon/Cayley.cayley_isometry`, `cayley_isometry_real`), `1 − K` is
   invertible over `ℚ` (`cayley_denominator_det_rat`), the chart error is at most twice the
   residual, `|Ex|² ≤ 4|Rx|²` (`cayley_chart_error_le_residual`), and so the executed element's
   energy deviation is at most `(4δ + 4δ²)|x|²` when `‖R‖_F² ≤ δ²` (`cayley_chart_energy`), or
   `(4nδ∞ + 4(nδ∞)²)|x|²` from the row certificate `‖R‖∞ ≤ δ∞` (`cayley_chart_energy_rowNorm`).
6. **The prox step at an inverse chart** (`prox_chart_residual`, `prox_chart_certificate`): with
   `W' = W + wγ g fᵀ X̂`, `W'H' − B' = −wγ g fᵀ(1 − X̂H')`, the left residual of the chart of
   `H'⁻¹`; with the exact inverse it is `HNN/Normal.normal_prox_step`.

[open] Owed in #62 ("Step 4 (#73) owed"): the balance of the full element with its passive part
and contrast port (`HNN/Word.reaction_stage_balance`) at an executed chart, and the counterfactual
bound of the carried transient against the exact word's trajectory, which needs a sensitivity
bound of the tick map (as `Objects/CommitRebase.commit_chain_residual` does for commits).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.LatticeWord

open Matrix
open Holonics.HNN.LatticeDeposit (unit unit_pos OnLattice quot rem div_rem_spec rem_bounds)

/-! ## 1. Newton–Schulz squares the residual -/

section NewtonSchulz

variable {M : Type*} [Ring M]

/-- [definition] **The Newton–Schulz refinement** of a chart `X` of `A⁻¹`: `X' = X(2 − AX)`. -/
def nsStep (A X : M) : M := X * (2 - A * X)

/-- [proved-derived; formal-checked] **One refinement, read from either side**:
`X(2 − AX) = X(1 + R) = (1 + R_L)X = (2 − XA)X`, with `R = 1 − AX` and `R_L = 1 − XA`. The chart's
refinement needs no commutation of `A` and `X`. -/
theorem nsStep_eq (A X : M) :
    nsStep A X = X * (1 + (1 - A * X)) ∧ nsStep A X = (1 + (1 - X * A)) * X ∧
      nsStep A X = (2 - X * A) * X := by
  unfold nsStep
  exact ⟨by noncomm_ring, by noncomm_ring, by noncomm_ring⟩

/-- [proved-derived; formal-checked] **Newton–Schulz squares the right residual.** With
`R = 1 − AX`, `1 − A·X(2 − AX) = R²` exactly, in any ring. In HNN terms the right residual is the
solve chart's certificate: the executed solve `X̂b` leaves the equation residual `b − A X̂b = Rb`,
reported with the chart. -/
theorem newton_schulz_right (A X : M) : 1 - A * nsStep A X = (1 - A * X) ^ 2 := by
  unfold nsStep
  noncomm_ring

/-- [proved-derived; formal-checked] **Newton–Schulz squares the left residual** with the same
refinement: `1 − X(2 − AX)·A = (1 − XA)²`. The prox step's map update reads this one (§6). -/
theorem newton_schulz_left (A X : M) : 1 - nsStep A X * A = (1 - X * A) ^ 2 := by
  unfold nsStep
  noncomm_ring

/-- [definition] `k` exact refinements. -/
def nsIter (A X : M) (k : ℕ) : M := (nsStep A)^[k] X

/-- [proved-derived; formal-checked] The next refinement refines the last chart (a window's warm
start). -/
theorem nsIter_succ (A X : M) (k : ℕ) : nsIter A X (k + 1) = nsStep A (nsIter A X k) :=
  Function.iterate_succ_apply' _ _ _

/-- [proved-derived; formal-checked] **`k` refinements give `R^(2^k)`** (right residual). -/
theorem newton_schulz_iter_right (A X : M) (k : ℕ) :
    1 - A * nsIter A X k = (1 - A * X) ^ (2 ^ k) := by
  induction k with
  | zero => simp [nsIter]
  | succ k ih => rw [nsIter_succ, newton_schulz_right, ih, ← pow_mul, ← pow_succ]

/-- [proved-derived; formal-checked] **`k` refinements give `R_L^(2^k)`** (left residual). -/
theorem newton_schulz_iter_left (A X : M) (k : ℕ) :
    1 - nsIter A X k * A = (1 - X * A) ^ (2 ^ k) := by
  induction k with
  | zero => simp [nsIter]
  | succ k ih => rw [nsIter_succ, newton_schulz_left, ih, ← pow_mul, ← pow_succ]

/-- [proved-derived; formal-checked] **The rounded refinement's residual** (right form): if the
executed chart is the refinement plus a rounding term, `X'' = X' + Δ`, then
`1 − AX'' = R² − AΔ` exactly. The device evaluates `1 − AX''` as integer products; this identity
splits it into the refinement's square and the rounding's image. -/
theorem rounded_refinement_residual (A X Δ : M) :
    1 - A * (nsStep A X + Δ) = (1 - A * X) ^ 2 - A * Δ := by
  rw [mul_add, ← newton_schulz_right]
  abel

/-- [proved-derived; formal-checked] **The rounded refinement's residual** (left form):
`1 − (X' + Δ)A = R_L² − ΔA`. -/
theorem rounded_refinement_residual_left (A X Δ : M) :
    1 - (nsStep A X + Δ) * A = (1 - X * A) ^ 2 - Δ * A := by
  rw [add_mul, ← newton_schulz_left]
  abel

/-- [proved-derived; formal-checked] **A warm start's residual.** When a deposit moves the
operator `A → A + D`, the last chart's residual is `1 − (A + D)X = R − DX`. -/
theorem warm_start_residual (A D X : M) : 1 - (A + D) * X = (1 - A * X) - D * X := by
  noncomm_ring

end NewtonSchulz

/-! ## 2. Exact norms, the lattice chart, and the certificate -/

section RowNorm

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- [definition] **The ℓ∞ operator norm**, the largest absolute row sum, exact in `ℚ` (zero on an
empty index). -/
def rowNorm (A : Matrix m n ℚ) : ℚ := Finset.univ.fold max 0 fun i => ∑ j, |A i j|

/-- [proved-derived; formal-checked] The certificate norm is nonnegative. -/
theorem rowNorm_nonneg (A : Matrix m n ℚ) : 0 ≤ rowNorm A := by
  unfold rowNorm
  exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

/-- [proved-derived; formal-checked] Every row's absolute sum is at most the norm: the bound a
certificate hands to each output entry. -/
theorem row_sum_le_rowNorm (A : Matrix m n ℚ) (i : m) : ∑ j, |A i j| ≤ rowNorm A := by
  unfold rowNorm
  exact (Finset.le_fold_max _).mpr (Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩)

/-- [proved-derived; formal-checked] A declared bound on every row sum is a certificate. -/
theorem rowNorm_le {A : Matrix m n ℚ} {c : ℚ} (hc : 0 ≤ c) (h : ∀ i, ∑ j, |A i j| ≤ c) :
    rowNorm A ≤ c := by
  unfold rowNorm
  exact (Finset.fold_max_le c).mpr ⟨hc, fun i _ => h i⟩

/-- [proved-derived; formal-checked] The triangle inequality: certificates of summed charts add. -/
theorem rowNorm_add_le (A B : Matrix m n ℚ) : rowNorm (A + B) ≤ rowNorm A + rowNorm B := by
  refine rowNorm_le (add_nonneg (rowNorm_nonneg A) (rowNorm_nonneg B)) fun i => ?_
  calc ∑ j, |(A + B) i j| ≤ ∑ j, (|A i j| + |B i j|) :=
        Finset.sum_le_sum fun j _ => by rw [Matrix.add_apply]; exact abs_add_le _ _
    _ = ∑ j, |A i j| + ∑ j, |B i j| := Finset.sum_add_distrib
    _ ≤ rowNorm A + rowNorm B := add_le_add (row_sum_le_rowNorm A i) (row_sum_le_rowNorm B i)

/-- [proved-derived; formal-checked] A released residual and its negation have one certificate. -/
theorem rowNorm_neg (A : Matrix m n ℚ) : rowNorm (-A) = rowNorm A := by
  simp only [rowNorm, Matrix.neg_apply, abs_neg]

/-- [proved-derived; formal-checked] Certificates of a difference add. -/
theorem rowNorm_sub_le (A B : Matrix m n ℚ) : rowNorm (A - B) ≤ rowNorm A + rowNorm B := by
  rw [sub_eq_add_neg, ← rowNorm_neg B]
  exact rowNorm_add_le A (-B)

/-- [proved-derived; formal-checked] **The ℓ∞ operator norm is submultiplicative.** -/
theorem rowNorm_mul_le (A : Matrix l m ℚ) (B : Matrix m n ℚ) :
    rowNorm (A * B) ≤ rowNorm A * rowNorm B := by
  refine rowNorm_le (mul_nonneg (rowNorm_nonneg A) (rowNorm_nonneg B)) fun i => ?_
  calc ∑ j, |(A * B) i j| ≤ ∑ j, ∑ k, |A i k| * |B k j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp only [abs_mul]
    _ = ∑ k, |A i k| * ∑ j, |B k j| := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ ∑ k, |A i k| * rowNorm B :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (row_sum_le_rowNorm B k) (abs_nonneg _)
    _ = (∑ k, |A i k|) * rowNorm B := by rw [Finset.sum_mul]
    _ ≤ rowNorm A * rowNorm B :=
        mul_le_mul_of_nonneg_right (row_sum_le_rowNorm A i) (rowNorm_nonneg B)

/-- [proved-derived; formal-checked] The identity chart has certificate at most one. -/
theorem rowNorm_one_le [DecidableEq n] : rowNorm (1 : Matrix n n ℚ) ≤ 1 := by
  refine rowNorm_le zero_le_one fun i => ?_
  have habs : ∀ j, |(1 : Matrix n n ℚ) i j| = if i = j then 1 else 0 := fun j => by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => habs j, Finset.sum_ite_eq]
  simp

/-- [proved-derived; formal-checked] `‖A^k‖∞ ≤ ‖A‖∞^k`: a squared residual's certificate is at most
the square of the residual's. -/
theorem rowNorm_pow_le [DecidableEq n] (A : Matrix n n ℚ) (k : ℕ) :
    rowNorm (A ^ k) ≤ rowNorm A ^ k := by
  induction k with
  | zero => simpa using rowNorm_one_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (rowNorm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (rowNorm_nonneg A))

/-- [proved-derived; formal-checked] An entrywise bound `c` gives the row bound `n·c`, `n` the
row width: the dimension factor of a rounding. -/
theorem rowNorm_le_card_mul {A : Matrix m n ℚ} {c : ℚ} (hc : 0 ≤ c) (h : ∀ i j, |A i j| ≤ c) :
    rowNorm A ≤ Fintype.card n * c :=
  rowNorm_le (by positivity) fun i =>
    (Finset.sum_le_sum fun j _ => h i j).trans (by simp)

/-- [proved-derived; formal-checked] **`k` exact refinements contract the certificate to its
`2^k`-th power**: `‖1 − A X_k‖∞ ≤ ‖1 − AX‖∞^(2^k)`. -/
theorem newton_schulz_iter_rowNorm [DecidableEq n] (A X : Matrix n n ℚ) (k : ℕ) :
    rowNorm (1 - A * nsIter A X k) ≤ rowNorm (1 - A * X) ^ (2 ^ k) := by
  rw [newton_schulz_iter_right]
  exact rowNorm_pow_le _ _

/-- [definition] **The lattice chart** of a matrix: every entry at its nearest point of
`2^(−L)ℤ`, ties upward (`LatticeDeposit.quot`). -/
def latticeChart (L : ℕ) (X : Matrix m n ℚ) : Matrix m n ℚ :=
  Matrix.of fun i j => quot L (X i j) * unit L

omit [Fintype m] [Fintype n] in
/-- [proved-derived; formal-checked] Every entry of the lattice chart lies on `2^(−L)ℤ`: the device
holds it as an integer coordinate. -/
theorem latticeChart_onLattice (L : ℕ) (X : Matrix m n ℚ) (i : m) (j : n) :
    OnLattice L (latticeChart L X i j) :=
  ⟨quot L (X i j), rfl⟩

omit [Fintype m] [Fintype n] in
/-- [proved-derived; formal-checked] The lattice chart's rounding term is the negated remainder of
`LatticeDeposit.div_rem_spec`: what the chart drops is exactly what division with remainder
leaves. -/
theorem latticeChart_sub_apply (L : ℕ) (X : Matrix m n ℚ) (i : m) (j : n) :
    (latticeChart L X - X) i j = -rem L (X i j) := by
  simp only [Matrix.sub_apply, latticeChart, Matrix.of_apply, rem]
  ring

omit [Fintype m] [Fintype n] in
/-- [proved-derived; formal-checked] **The rounding bound** `|Δ_ij| ≤ 2^(−L)/2`, from
`LatticeDeposit.rem_bounds`. -/
theorem latticeChart_round (L : ℕ) (X : Matrix m n ℚ) (i : m) (j : n) :
    |(latticeChart L X - X) i j| ≤ unit L / 2 := by
  rw [latticeChart_sub_apply, abs_neg, abs_le]
  have h := rem_bounds L (X i j)
  constructor <;> linarith [h.1, h.2]

/-- [proved-derived; formal-checked] **The rounding's certificate** `‖X̂ − X‖∞ ≤ n·2^(−L)/2`, `n`
the row width: the dimension factor the lattice rule must absorb. -/
theorem rowNorm_latticeChart_sub (L : ℕ) (X : Matrix m n ℚ) :
    rowNorm (latticeChart L X - X) ≤ Fintype.card n * (unit L / 2) :=
  rowNorm_le_card_mul (by have := unit_pos L; positivity) (latticeChart_round L X)

variable [DecidableEq n]

/-- [proved-derived; formal-checked] **The rounded refinement keeps a certified residual** (right
form). The lattice chart `X''` of the refinement `X' = X(2 − AX)` satisfies
`‖1 − AX''‖∞ ≤ ‖1 − AX‖∞² + ‖A‖∞·n·2^(−L)/2`. In HNN terms the executed chart is `X''`, a lattice
matrix whose products the device executes as integers; its certificate is the squared residual
plus the rounding's image, released and reported with the chart. -/
theorem rounded_refinement_certificate (L : ℕ) (A X : Matrix n n ℚ) :
    rowNorm (1 - A * latticeChart L (nsStep A X)) ≤
      rowNorm (1 - A * X) ^ 2 + rowNorm A * (Fintype.card n * (unit L / 2)) := by
  have hid := rounded_refinement_residual A X (latticeChart L (nsStep A X) - nsStep A X)
  rw [add_sub_cancel] at hid
  rw [hid]
  calc rowNorm ((1 - A * X) ^ 2 - A * (latticeChart L (nsStep A X) - nsStep A X))
      ≤ rowNorm ((1 - A * X) ^ 2) + rowNorm (A * (latticeChart L (nsStep A X) - nsStep A X)) :=
        rowNorm_sub_le _ _
    _ ≤ rowNorm (1 - A * X) ^ 2 + rowNorm A * (Fintype.card n * (unit L / 2)) :=
        add_le_add (rowNorm_pow_le _ 2)
          ((rowNorm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left (rowNorm_latticeChart_sub _ _) (rowNorm_nonneg _)))

/-- [proved-derived; formal-checked] **The rounded refinement keeps a certified residual** (left
form): `‖1 − X''A‖∞ ≤ ‖1 − XA‖∞² + n·2^(−L)/2·‖A‖∞`. -/
theorem rounded_refinement_certificate_left (L : ℕ) (A X : Matrix n n ℚ) :
    rowNorm (1 - latticeChart L (nsStep A X) * A) ≤
      rowNorm (1 - X * A) ^ 2 + Fintype.card n * (unit L / 2) * rowNorm A := by
  have hid := rounded_refinement_residual_left A X (latticeChart L (nsStep A X) - nsStep A X)
  rw [add_sub_cancel] at hid
  rw [hid]
  calc rowNorm ((1 - X * A) ^ 2 - (latticeChart L (nsStep A X) - nsStep A X) * A)
      ≤ rowNorm ((1 - X * A) ^ 2) + rowNorm ((latticeChart L (nsStep A X) - nsStep A X) * A) :=
        rowNorm_sub_le _ _
    _ ≤ rowNorm (1 - X * A) ^ 2 + Fintype.card n * (unit L / 2) * rowNorm A :=
        add_le_add (rowNorm_pow_le _ 2)
          ((rowNorm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (rowNorm_latticeChart_sub _ _) (rowNorm_nonneg _)))

/-- [definition] **The rounded refinements**: each refines the last chart and rounds it onto the
lattice. -/
def roundedIter (L : ℕ) (A X : Matrix n n ℚ) : ℕ → Matrix n n ℚ
  | 0 => X
  | k + 1 => latticeChart L (nsStep A (roundedIter L A X k))

/-- [proved-derived; formal-checked] **The certificate does not grow.** If `c ≤ 1/2`, twice the
rounding term `‖A‖∞·n·2^(−L)/2` is at most `c`, and the starting chart's residual is at most `c`,
then every rounded refinement's residual is at most `c`: `δ² + ε ≤ c² + c/2 ≤ c`. In HNN terms, a
precision `L` declared by rule holds each inverse chart's certificate below its declared bound for
the whole window, with every chart on the lattice. -/
theorem roundedIter_certificate (L : ℕ) (A X : Matrix n n ℚ) {c : ℚ} (hc : c ≤ 1 / 2)
    (hε : 2 * (rowNorm A * (Fintype.card n * (unit L / 2))) ≤ c)
    (h0 : rowNorm (1 - A * X) ≤ c) (k : ℕ) :
    rowNorm (1 - A * roundedIter L A X k) ≤ c := by
  have hc0 : 0 ≤ c := (rowNorm_nonneg _).trans h0
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hstep := rounded_refinement_certificate L A (roundedIter L A X k)
    have hδ0 := rowNorm_nonneg (1 - A * roundedIter L A X k)
    have hsq : rowNorm (1 - A * roundedIter L A X k) ^ 2 ≤ c ^ 2 :=
      pow_le_pow_left₀ hδ0 ih 2
    show rowNorm (1 - A * latticeChart L (nsStep A (roundedIter L A X k))) ≤ c
    nlinarith

/-- [proved-derived; formal-checked] **A warm start's certificate**: after a deposit moves
`A → A + D`, the last chart's residual is at most `‖1 − AX‖∞ + ‖D‖∞‖X‖∞`, so one deposit's
movement bounds what the window's first refinement must square away. -/
theorem warm_start_certificate (A D X : Matrix n n ℚ) :
    rowNorm (1 - (A + D) * X) ≤ rowNorm (1 - A * X) + rowNorm D * rowNorm X := by
  rw [warm_start_residual]
  exact (rowNorm_sub_le _ _).trans (add_le_add le_rfl (rowNorm_mul_le _ _))

/-- [proved-derived; formal-checked] **A certified chart is near the exact inverse.** If
`AY = 1` and `‖1 − AX̂‖∞ ≤ δ < 1`, then `‖Y − X̂‖∞ ≤ ‖X̂‖∞δ/(1 − δ)`: `Y − X̂ = YR`, so
`‖Y‖∞ ≤ ‖X̂‖∞ + ‖Y‖∞δ`. The bound reads only the executed chart and its certificate. -/
theorem inverse_chart_deviation {A X Y : Matrix n n ℚ} (hY : A * Y = 1) {δ : ℚ}
    (hR : rowNorm (1 - A * X) ≤ δ) (hδ : δ < 1) :
    rowNorm (Y - X) ≤ rowNorm X * δ / (1 - δ) := by
  have hYA : Y * A = 1 := mul_eq_one_comm.mp hY
  have hYX : Y - X = Y * (1 - A * X) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hYA, Matrix.one_mul]
  have hδ0 : 0 ≤ δ := (rowNorm_nonneg _).trans hR
  have hdev : rowNorm (Y - X) ≤ rowNorm Y * δ := by
    rw [hYX]
    exact (rowNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hR (rowNorm_nonneg Y))
  have hY' : rowNorm Y ≤ rowNorm X + rowNorm Y * δ := by
    calc rowNorm Y = rowNorm (X + (Y - X)) := by rw [add_sub_cancel]
      _ ≤ rowNorm X + rowNorm (Y - X) := rowNorm_add_le _ _
      _ ≤ rowNorm X + rowNorm Y * δ := add_le_add le_rfl hdev
  have h1 : 0 < 1 - δ := sub_pos.mpr hδ
  rw [le_div_iff₀ h1]
  have hYn := rowNorm_nonneg Y
  nlinarith

end RowNorm

/-! ## 3. Error feedback: the carried transient -/

section Feedback

variable {E : Type*}

/-- [definition] **The carried remainder** `r_t` of images `y_t` fed back at the lattice
`2^(−L)ℤ`, from a starting remainder `r_0` (zero when the word opens). -/
def fbRem (L : ℕ) (y : ℕ → E → ℚ) (r₀ : E → ℚ) : ℕ → E → ℚ
  | 0 => r₀
  | t + 1 => fun i => rem L (y t i + fbRem L y r₀ t i)

/-- [definition] **The carried value** `x_t`: the nearest lattice point of `y_t + r_t`. -/
def fbOut (L : ℕ) (y : ℕ → E → ℚ) (r₀ : E → ℚ) (t : ℕ) : E → ℚ :=
  fun i => quot L (y t i + fbRem L y r₀ t i) * unit L

/-- [proved-derived; formal-checked] **One tick of error feedback**: `x_t + r_(t+1) = y_t + r_t`. -/
theorem feedback_tick (L : ℕ) (y : ℕ → E → ℚ) (r₀ : E → ℚ) (t : ℕ) (i : E) :
    fbOut L y r₀ t i + fbRem L y r₀ (t + 1) i = y t i + fbRem L y r₀ t i := by
  simp only [fbOut, fbRem]
  exact (div_rem_spec L _).symm

/-- [proved-derived; formal-checked] The carried values lie on the lattice. -/
theorem feedback_onLattice (L : ℕ) (y : ℕ → E → ℚ) (r₀ : E → ℚ) (t : ℕ) (i : E) :
    OnLattice L (fbOut L y r₀ t i) :=
  ⟨_, rfl⟩

/-- [proved-derived; formal-checked] **The carried remainder stays in its half-open cell**
`−2^(−L)/2 ≤ r_t < 2^(−L)/2`, from a starting remainder in it. -/
theorem feedback_rem_bounds (L : ℕ) (y : ℕ → E → ℚ) {r₀ : E → ℚ}
    (h₀ : ∀ i, -(unit L / 2) ≤ r₀ i ∧ r₀ i < unit L / 2) (t : ℕ) (i : E) :
    -(unit L / 2) ≤ fbRem L y r₀ t i ∧ fbRem L y r₀ t i < unit L / 2 := by
  cases t with
  | zero => exact h₀ i
  | succ t => exact rem_bounds L _

/-- [proved-derived; formal-checked] A word opens at zero remainder, which lies in the cell. -/
theorem zero_rem_bounds (L : ℕ) (i : E) :
    -(unit L / 2) ≤ (0 : E → ℚ) i ∧ (0 : E → ℚ) i < unit L / 2 := by
  have := unit_pos L
  simp only [Pi.zero_apply]
  constructor <;> linarith

/-- [proved-derived; formal-checked] **`feedback_accounting`: the telescoping.** Over `T` ticks the
carried values plus the final remainder equal the exact images plus the starting remainder:
`Σ_(t<T) x_t + r_T = Σ_(t<T) y_t + r_0`, entry by entry. Nothing is rounded away unreported. -/
theorem feedback_accounting (L : ℕ) (y : ℕ → E → ℚ) (r₀ : E → ℚ) (T : ℕ) (i : E) :
    ∑ t ∈ Finset.range T, fbOut L y r₀ t i + fbRem L y r₀ T i =
      ∑ t ∈ Finset.range T, y t i + r₀ i := by
  induction T with
  | zero => simp [fbRem]
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have := feedback_tick L y r₀ T i
    linarith

/-- [proved-derived; formal-checked] **The word's accounting**: opened at zero remainder,
`Σ_(t<T) x_t + r_T = Σ_(t<T) y_t`; the word releases `r_T` at its end and reports it. -/
theorem feedback_accounting_zero (L : ℕ) (y : ℕ → E → ℚ) (T : ℕ) (i : E) :
    ∑ t ∈ Finset.range T, fbOut L y 0 t i + fbRem L y 0 T i = ∑ t ∈ Finset.range T, y t i := by
  simpa using feedback_accounting L y 0 T i

/-- [proved-derived; formal-checked] **Each tick deviates by less than one unit**:
`x_t − y_t = r_t − r_(t+1)`, a difference of two remainders in the half-open cell. -/
theorem feedback_tick_deviation (L : ℕ) (y : ℕ → E → ℚ) {r₀ : E → ℚ}
    (h₀ : ∀ i, -(unit L / 2) ≤ r₀ i ∧ r₀ i < unit L / 2) (t : ℕ) (i : E) :
    |fbOut L y r₀ t i - y t i| < unit L := by
  have htick := feedback_tick L y r₀ t i
  have h1 := feedback_rem_bounds L y h₀ t i
  have h2 := feedback_rem_bounds L y h₀ (t + 1) i
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- [proved-derived; formal-checked] **The partial sums track within half a unit**, however long
the word: opened at zero remainder, `|Σ_(t<T) x_t − Σ_(t<T) y_t| = |r_T| ≤ 2^(−L)/2`. This is what
error feedback buys over rounding each tick alone, whose errors add. -/
theorem feedback_sum_within_half_unit (L : ℕ) (y : ℕ → E → ℚ) (T : ℕ) (i : E) :
    |∑ t ∈ Finset.range T, fbOut L y 0 t i - ∑ t ∈ Finset.range T, y t i| ≤ unit L / 2 := by
  have hacc := feedback_accounting_zero L y T i
  have hb := feedback_rem_bounds L y (zero_rem_bounds L) T i
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- [definition] **The carried word** of a tick map `T` from a lattice state `s₀`: at each tick the
exact image of the carried state plus the carried remainder is split at the nearest lattice point
(state, remainder). -/
def carriedWord (L : ℕ) (T : (E → ℚ) → E → ℚ) (s₀ : E → ℚ) : ℕ → (E → ℚ) × (E → ℚ)
  | 0 => (s₀, 0)
  | t + 1 =>
    (fun i => quot L (T (carriedWord L T s₀ t).1 i + (carriedWord L T s₀ t).2 i) * unit L,
      fun i => rem L (T (carriedWord L T s₀ t).1 i + (carriedWord L T s₀ t).2 i))

/-- [definition] The carried word's images: the tick map at the carried state. -/
def wordImages (L : ℕ) (T : (E → ℚ) → E → ℚ) (s₀ : E → ℚ) : ℕ → E → ℚ :=
  fun t => T (carriedWord L T s₀ t).1

/-- [proved-derived; formal-checked] The carried word's remainder is the error feedback of its
images. -/
theorem carriedWord_rem_eq (L : ℕ) (T : (E → ℚ) → E → ℚ) (s₀ : E → ℚ) (t : ℕ) :
    (carriedWord L T s₀ t).2 = fbRem L (wordImages L T s₀) 0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext i
    simp only [carriedWord, fbRem, wordImages]
    rw [ih]

/-- [proved-derived; formal-checked] The carried word's next state is the error feedback's carried
value. -/
theorem carriedWord_state_eq (L : ℕ) (T : (E → ℚ) → E → ℚ) (s₀ : E → ℚ) (t : ℕ) :
    (carriedWord L T s₀ (t + 1)).1 = fbOut L (wordImages L T s₀) 0 t := by
  funext i
  simp only [carriedWord, fbOut, wordImages]
  rw [carriedWord_rem_eq]

/-- [proved-derived; formal-checked] **`carried_word_accounting`.** Over `N` ticks of the carried
word, `Σ_(t<N) s_(t+1) + r_N = Σ_(t<N) T(s_t)`: the carried states account exactly for the tick
map's images at them, the final remainder released at the word's end. -/
theorem carried_word_accounting (L : ℕ) (T : (E → ℚ) → E → ℚ) (s₀ : E → ℚ) (N : ℕ) (i : E) :
    ∑ t ∈ Finset.range N, (carriedWord L T s₀ (t + 1)).1 i + (carriedWord L T s₀ N).2 i =
      ∑ t ∈ Finset.range N, T (carriedWord L T s₀ t).1 i := by
  simp only [carriedWord_state_eq, carriedWord_rem_eq]
  exact feedback_accounting_zero L (wordImages L T s₀) N i

end Feedback

/-! ## 4. The executed adjoint -/

section Adjoint

variable {m n : Type*} [Fintype m] [Fintype n]

/-- [proved-derived; formal-checked] **The executed adjoint pairs exactly with the executed
chart**: `⟨λ, M̂x⟩ = ⟨M̂ᵀλ, x⟩`. In HNN terms the chart `M̂` is the linear map the word actually
executed (a lattice matrix); pulling the covector back through `M̂ᵀ` keeps the paired adjoint's
operands, so rounding enters only as released residuals. -/
theorem executed_adjoint_pairing {R : Type*} [CommSemiring R] (Mh : Matrix m n R) (lam : m → R)
    (x : n → R) : lam ⬝ᵥ (Mh *ᵥ x) = (Mhᵀ *ᵥ lam) ⬝ᵥ x := by
  rw [dotProduct_mulVec, mulVec_transpose]

/-- [proved-derived; formal-checked] **The law the adjoint must use**: `M̂ᵀλ` is the only covector
`μ` with `⟨λ, M̂x⟩ = ⟨μ, x⟩` for every `x`. -/
theorem executed_adjoint_unique [DecidableEq n] {R : Type*} [CommSemiring R] (Mh : Matrix m n R)
    (lam : m → R) (mu : n → R) :
    (∀ x, lam ⬝ᵥ (Mh *ᵥ x) = mu ⬝ᵥ x) ↔ mu = Mhᵀ *ᵥ lam := by
  constructor
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    rw [executed_adjoint_pairing, dotProduct_single, dotProduct_single, mul_one, mul_one] at hj
    exact hj.symm
  · rintro rfl x
    exact executed_adjoint_pairing Mh lam x

/-- [proved-derived; formal-checked] **The exact adjoint against the executed chart leaves a
defect**: `⟨λ, M̂x⟩ − ⟨Mᵀλ, x⟩ = ⟨λ, (M̂ − M)x⟩`. -/
theorem exact_adjoint_pairing_defect {R : Type*} [CommRing R] (M Mh : Matrix m n R) (lam : m → R)
    (x : n → R) : lam ⬝ᵥ (Mh *ᵥ x) - (Mᵀ *ᵥ lam) ⬝ᵥ x = lam ⬝ᵥ ((Mh - M) *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, executed_adjoint_pairing M lam x]

/-- [definition] The ℓ1 norm of a covector, dual to the ℓ∞ norm of the states. -/
def l1 (v : n → ℚ) : ℚ := ∑ j, |v j|

/-- [proved-derived; formal-checked] `‖Eᵀλ‖₁ ≤ ‖E‖∞‖λ‖₁`: the ℓ∞ operator norm of `E` is the ℓ1
operator norm of `Eᵀ`. -/
theorem l1_transpose_mulVec_le (E : Matrix m n ℚ) (lam : m → ℚ) :
    l1 (Eᵀ *ᵥ lam) ≤ rowNorm E * l1 lam := by
  unfold l1
  calc ∑ j, |(Eᵀ *ᵥ lam) j| ≤ ∑ j, ∑ i, |E i j| * |lam i| := by
        refine Finset.sum_le_sum fun j _ => ?_
        simp only [mulVec, dotProduct, transpose_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp only [abs_mul]
    _ = ∑ i, |lam i| * ∑ j, |E i j| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ ∑ i, |lam i| * rowNorm E :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (row_sum_le_rowNorm E i) (abs_nonneg _)
    _ = rowNorm E * ∑ i, |lam i| := by rw [← Finset.sum_mul, mul_comm]

/-- [proved-derived; formal-checked] **The executed covector's deviation from the exact adjoint**:
`‖Mᵀλ − M̂ᵀλ‖₁ ≤ ‖M − M̂‖∞‖λ‖₁`. -/
theorem executed_adjoint_deviation (M Mh : Matrix m n ℚ) (lam : m → ℚ) :
    l1 (Mᵀ *ᵥ lam - Mhᵀ *ᵥ lam) ≤ rowNorm (M - Mh) * l1 lam := by
  rw [← sub_mulVec, ← transpose_sub]
  exact l1_transpose_mulVec_le _ _

/-- [proved-derived; formal-checked] **Through a certified inverse chart**: if `AY = 1` and
`‖1 − AX̂‖∞ ≤ δ < 1`, the executed covector `X̂ᵀλ` is within `‖X̂‖∞δ/(1 − δ)·‖λ‖₁` of the exact
adjoint `Yᵀλ = A⁻ᵀλ`, a bound read from the executed chart and its certificate alone. -/
theorem inverse_chart_adjoint_deviation [DecidableEq n] {A X Y : Matrix n n ℚ} (hY : A * Y = 1)
    {δ : ℚ} (hR : rowNorm (1 - A * X) ≤ δ) (hδ : δ < 1) (lam : n → ℚ) :
    l1 (Yᵀ *ᵥ lam - Xᵀ *ᵥ lam) ≤ rowNorm X * δ / (1 - δ) * l1 lam :=
  (executed_adjoint_deviation Y X lam).trans
    (mul_le_mul_of_nonneg_right (inverse_chart_deviation hY hR hδ)
      (Finset.sum_nonneg fun i _ => abs_nonneg (lam i)))

end Adjoint

/-! ## 5. The power balance up to the residual -/

section Energy

variable {m n : Type*} [Fintype m] [Fintype n]

/-- [proved-derived; formal-checked] The Euclidean energy `|u|²` is nonnegative over `ℚ`. -/
theorem dot_self_nonneg (u : n → ℚ) : 0 ≤ u ⬝ᵥ u :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)

/-- [proved-derived; formal-checked] Cauchy–Schwarz for the Euclidean dot product over `ℚ`, with
no square root: `⟨u, v⟩² ≤ |u|²|v|²`. -/
theorem dot_sq_le (u v : n → ℚ) : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  simpa only [dotProduct, sq] using h

/-- [definition] The squared Frobenius norm, exact in `ℚ`. -/
def frobSq (E : Matrix m n ℚ) : ℚ := ∑ i, ∑ j, E i j ^ 2

/-- [proved-derived; formal-checked] `|Ex|² ≤ ‖E‖_F²|x|²`, row by row by Cauchy–Schwarz. -/
theorem mulVec_dot_le_frobSq (E : Matrix m n ℚ) (x : n → ℚ) :
    (E *ᵥ x) ⬝ᵥ (E *ᵥ x) ≤ frobSq E * (x ⬝ᵥ x) := by
  have hrow : ∀ i, (E *ᵥ x) i * (E *ᵥ x) i ≤ (∑ j, E i j ^ 2) * (x ⬝ᵥ x) := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (E i) x
    simp only [mulVec, dotProduct, sq] at h ⊢
    exact h
  calc (E *ᵥ x) ⬝ᵥ (E *ᵥ x) = ∑ i, (E *ᵥ x) i * (E *ᵥ x) i := rfl
    _ ≤ ∑ i, (∑ j, E i j ^ 2) * (x ⬝ᵥ x) := Finset.sum_le_sum fun i _ => hrow i
    _ = frobSq E * (x ⬝ᵥ x) := by rw [← Finset.sum_mul]; rfl

/-- [proved-derived; formal-checked] **The row certificate bounds the Frobenius one**:
`‖E‖_F² ≤ m·‖E‖∞²`, `m` the number of rows. -/
theorem frobSq_le_card_mul_rowNorm_sq (E : Matrix m n ℚ) :
    frobSq E ≤ Fintype.card m * rowNorm E ^ 2 := by
  have hrow : ∀ i, ∑ j, E i j ^ 2 ≤ rowNorm E ^ 2 := by
    intro i
    have hS := row_sum_le_rowNorm E i
    have hS0 : 0 ≤ ∑ j, |E i j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    calc ∑ j, E i j ^ 2 = ∑ j, |E i j| * |E i j| :=
          Finset.sum_congr rfl fun j _ => by rw [← sq, sq_abs]
      _ ≤ ∑ j, |E i j| * ∑ k, |E i k| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun k _ => abs_nonneg (E i k)) (Finset.mem_univ j))
            (abs_nonneg _)
      _ = (∑ j, |E i j|) ^ 2 := by rw [sq, Finset.sum_mul]
      _ ≤ rowNorm E ^ 2 := pow_le_pow_left₀ hS0 hS 2
  calc frobSq E = ∑ i, ∑ j, E i j ^ 2 := rfl
    _ ≤ ∑ _i : m, rowNorm E ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = Fintype.card m * rowNorm E ^ 2 := by simp

variable [DecidableEq n]

/-- [proved-derived; formal-checked] An orthogonal `C` (`CᵀC = 1`) preserves the energy:
`|Cx|² = |x|²`. -/
theorem isometry_dot {R : Type*} [CommRing R] {C : Matrix n n R} (hC : Cᵀ * C = 1) (x : n → R) :
    (C *ᵥ x) ⬝ᵥ (C *ᵥ x) = x ⬝ᵥ x := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hC, one_mulVec, dotProduct_comm]

/-- [proved-derived; formal-checked] **The executed element's energy identity.** For any `C`
with `CᵀC = 1` and executed chart `Ĉ = C + E`,
`|Ĉx|² − |x|² = 2⟨Cx, Ex⟩ + |Ex|²` exactly. In HNN terms the lossless element is exactly
power-neutral, and the executed chart's power change is the chart error's, reported per word. -/
theorem chart_energy_identity {R : Type*} [CommRing R] {C : Matrix n n R} (hC : Cᵀ * C = 1)
    (E : Matrix n n R) (x : n → R) :
    ((C + E) *ᵥ x) ⬝ᵥ ((C + E) *ᵥ x) - x ⬝ᵥ x =
      2 * ((C *ᵥ x) ⬝ᵥ (E *ᵥ x)) + (E *ᵥ x) ⬝ᵥ (E *ᵥ x) := by
  rw [add_mulVec, add_dotProduct, dotProduct_add, dotProduct_add, isometry_dot hC,
    dotProduct_comm (E *ᵥ x) (C *ᵥ x)]
  ring

/-- [proved-derived; formal-checked] **The energy deviation is bounded by the chart error.** If
`|Ex|² ≤ ε²|x|²`, then `||Ĉx|² − |x|²| ≤ (2ε + ε²)|x|²` (Cauchy–Schwarz on the cross term, with
`|Cx| = |x|`). -/
theorem chart_energy_deviation {C E : Matrix n n ℚ} (hC : Cᵀ * C = 1) {ε : ℚ} (hε : 0 ≤ ε)
    (x : n → ℚ) (hE : (E *ᵥ x) ⬝ᵥ (E *ᵥ x) ≤ ε ^ 2 * (x ⬝ᵥ x)) :
    |((C + E) *ᵥ x) ⬝ᵥ ((C + E) *ᵥ x) - x ⬝ᵥ x| ≤ (2 * ε + ε ^ 2) * (x ⬝ᵥ x) := by
  rw [chart_energy_identity hC]
  have hs := dot_self_nonneg x
  have he := dot_self_nonneg (E *ᵥ x)
  have hcs := dot_sq_le (C *ᵥ x) (E *ᵥ x)
  rw [isometry_dot hC] at hcs
  have hse := mul_le_mul_of_nonneg_left hE hs
  have ha : |(C *ᵥ x) ⬝ᵥ (E *ᵥ x)| ≤ ε * (x ⬝ᵥ x) :=
    abs_le_of_sq_le_sq (by nlinarith) (mul_nonneg hε hs)
  calc |2 * ((C *ᵥ x) ⬝ᵥ (E *ᵥ x)) + (E *ᵥ x) ⬝ᵥ (E *ᵥ x)|
      ≤ |2 * ((C *ᵥ x) ⬝ᵥ (E *ᵥ x))| + |(E *ᵥ x) ⬝ᵥ (E *ᵥ x)| := abs_add_le _ _
    _ = 2 * |(C *ᵥ x) ⬝ᵥ (E *ᵥ x)| + (E *ᵥ x) ⬝ᵥ (E *ᵥ x) := by
        rw [abs_mul, abs_two, abs_of_nonneg he]
    _ ≤ (2 * ε + ε ^ 2) * (x ⬝ᵥ x) := by nlinarith

omit [Fintype n] in
/-- [proved-derived; formal-checked] The Cayley denominator of a skew `K` has
`(1 − K)ᵀ = 1 + K = 2 − (1 − K)`: the hypothesis of `cayley_chart_orthogonal`. -/
theorem cayley_denominator_transpose {R : Type*} [CommRing R] {K : Matrix n n R}
    (hK : Kᵀ = -K) : (1 - K)ᵀ = 2 - (1 - K) := by
  rw [transpose_sub, transpose_one, hK, ← one_add_one_eq_two]
  abel

/-- [proved-derived; formal-checked] **The Cayley element is orthogonal**, over any commutative
ring: if `Aᵀ = 2 − A` (so `A = 1 − K` with `K` skew) and `AX = 1`, then `C = 2X − 1` satisfies
`CᵀC = 1`. `CA = 2 − A = Aᵀ`, so `Aᵀ(CᵀC)A = AAᵀ = AᵀA`. This is the matrix form over `ℚ` of the
owner's `Holon/Cayley.cayley_isometry` (complex) and `cayley_isometry_real` (real). -/
theorem cayley_chart_orthogonal {R : Type*} [CommRing R] {A X : Matrix n n R}
    (hA : Aᵀ = 2 - A) (hAX : A * X = 1) : (2 * X - 1)ᵀ * (2 * X - 1) = 1 := by
  have hXA : X * A = 1 := mul_eq_one_comm.mp hAX
  have hCA : (2 * X - 1) * A = Aᵀ := by
    rw [sub_mul, Matrix.mul_assoc, hXA, mul_one, one_mul, hA]
  have hXt : Xᵀ * Aᵀ = 1 := by rw [← transpose_mul, hAX, transpose_one]
  have hcomm : A * Aᵀ = Aᵀ * A := by
    rw [hA]
    noncomm_ring
  calc (2 * X - 1)ᵀ * (2 * X - 1)
      = (Xᵀ * Aᵀ) * ((2 * X - 1)ᵀ * (2 * X - 1)) * (A * X) := by
        rw [hXt, hAX, Matrix.one_mul, Matrix.mul_one]
    _ = Xᵀ * (((2 * X - 1) * A)ᵀ * ((2 * X - 1) * A)) * X := by
        rw [transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = Xᵀ * (Aᵀ * A) * X := by rw [hCA, transpose_transpose, hcomm]
    _ = (Xᵀ * Aᵀ) * (A * X) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hXt, hAX, Matrix.mul_one]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] A skew `K` does no work: `⟨v, Kv⟩ = 0` over `ℚ`
(`Holon/Dirac.skew_dot`). -/
theorem skew_dot_self_rat {K : Matrix n n ℚ} (hK : Kᵀ = -K) (v : n → ℚ) :
    v ⬝ᵥ (K *ᵥ v) = 0 := by
  have := Holonics.HolonCore.skew_dot hK v v
  linarith

/-- [proved-derived; formal-checked] **The Cayley denominator is invertible over `ℚ`**: for skew
`K`, `det(1 − K) ≠ 0` (`(1 − K)v = 0` gives `|v|² = ⟨v, Kv⟩ = 0`), so the exact element exists and
the chart has a target. The `ℚ` form of `Holon/Cayley.cayley_denominator_det`. -/
theorem cayley_denominator_det_rat {K : Matrix n n ℚ} (hK : Kᵀ = -K) : (1 - K).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have hvK : v = K *ᵥ v := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hker
    exact hker
  have hvv : v ⬝ᵥ v = 0 := by
    calc v ⬝ᵥ v = v ⬝ᵥ (K *ᵥ v) := by rw [← hvK]
      _ = 0 := skew_dot_self_rat hK v
  exact hv (dotProduct_self_eq_zero.mp hvv)

/-- [proved-derived; formal-checked] **The Cayley denominator expands**: `|y|² ≤ |(1 − K)y|²` for
skew `K`, since `|(1 − K)y|² = |y|² + |Ky|²`. -/
theorem cayley_denominator_expands {K : Matrix n n ℚ} (hK : Kᵀ = -K) (y : n → ℚ) :
    y ⬝ᵥ y ≤ ((1 - K) *ᵥ y) ⬝ᵥ ((1 - K) *ᵥ y) := by
  have hskew := skew_dot_self_rat hK y
  have hexp : ((1 - K) *ᵥ y) ⬝ᵥ ((1 - K) *ᵥ y) = y ⬝ᵥ y + (K *ᵥ y) ⬝ᵥ (K *ᵥ y) := by
    rw [sub_mulVec, one_mulVec, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_comm (K *ᵥ y) y, hskew]
    ring
  rw [hexp]
  linarith [dot_self_nonneg (K *ᵥ y)]

/-- [proved-derived; formal-checked] **The Cayley chart's error is at most twice its residual.**
For skew `K`, the exact inverse `X` of `1 − K`, and any chart `X̂` with residual
`R = 1 − (1 − K)X̂`, the executed element `Ĉ = 2X̂ − 1` differs from `C = 2X − 1` by `E` with
`|Ex|² ≤ 4|Rx|²`: `(1 − K)(X̂ − X)x = −Rx` and `1 − K` expands. -/
theorem cayley_chart_error_le_residual {K X Xh : Matrix n n ℚ} (hK : Kᵀ = -K)
    (hX : (1 - K) * X = 1) (x : n → ℚ) :
    ((2 * Xh - 1 - (2 * X - 1)) *ᵥ x) ⬝ᵥ ((2 * Xh - 1 - (2 * X - 1)) *ᵥ x) ≤
      4 * (((1 - (1 - K) * Xh) *ᵥ x) ⬝ᵥ ((1 - (1 - K) * Xh) *ᵥ x)) := by
  have hE : 2 * Xh - 1 - (2 * X - 1) = (Xh - X) + (Xh - X) := by
    rw [two_mul, two_mul]
    abel
  have hy : (1 - K) *ᵥ ((Xh - X) *ᵥ x) = -((1 - (1 - K) * Xh) *ᵥ x) := by
    rw [mulVec_mulVec, Matrix.mul_sub, hX, ← neg_mulVec, neg_sub]
  have hexp := cayley_denominator_expands hK ((Xh - X) *ᵥ x)
  rw [hy, neg_dotProduct, dotProduct_neg, neg_neg] at hexp
  rw [hE, add_mulVec, add_dotProduct, dotProduct_add]
  linarith

/-- [proved-derived; formal-checked] **The executed Cayley element's power balance up to its
residual.** For skew `K`, the exact inverse `X` of `1 − K`, and a chart `X̂` whose residual
`R = 1 − (1 − K)X̂` has `‖R‖_F² ≤ δ²`, the executed element `Ĉ = 2X̂ − 1` changes the energy by
at most `(4δ + 4δ²)|x|²`. In HNN terms the ring's lossless element, executed through its lattice
chart, is power-neutral up to a deviation its certificate bounds, released and reported per
word. -/
theorem cayley_chart_energy {K X Xh : Matrix n n ℚ} (hK : Kᵀ = -K) (hX : (1 - K) * X = 1)
    {δ : ℚ} (hδ : 0 ≤ δ) (hR : frobSq (1 - (1 - K) * Xh) ≤ δ ^ 2) (x : n → ℚ) :
    |((2 * Xh - 1) *ᵥ x) ⬝ᵥ ((2 * Xh - 1) *ᵥ x) - x ⬝ᵥ x| ≤ (4 * δ + 4 * δ ^ 2) * (x ⬝ᵥ x) := by
  have hC := cayley_chart_orthogonal (cayley_denominator_transpose hK) hX
  have hsplit : 2 * Xh - 1 = (2 * X - 1) + (2 * Xh - 1 - (2 * X - 1)) := by abel
  have herr := cayley_chart_error_le_residual hK hX (Xh := Xh) x
  have hfrob := mulVec_dot_le_frobSq (1 - (1 - K) * Xh) x
  have hs := dot_self_nonneg x
  have hbound : ((2 * Xh - 1 - (2 * X - 1)) *ᵥ x) ⬝ᵥ ((2 * Xh - 1 - (2 * X - 1)) *ᵥ x) ≤
      (2 * δ) ^ 2 * (x ⬝ᵥ x) := by
    have := mul_le_mul_of_nonneg_right hR hs
    nlinarith
  have h := chart_energy_deviation hC (by positivity : (0 : ℚ) ≤ 2 * δ) x hbound
  rw [← hsplit] at h
  calc _ ≤ (2 * (2 * δ) + (2 * δ) ^ 2) * (x ⬝ᵥ x) := h
    _ = (4 * δ + 4 * δ ^ 2) * (x ⬝ᵥ x) := by ring

/-- [proved-derived; formal-checked] **The same balance from the row certificate** `‖R‖∞ ≤ δ∞`:
the energy deviation is at most `(4nδ∞ + 4(nδ∞)²)|x|²`, `n` the ring's width, since
`‖R‖_F² ≤ n‖R‖∞² ≤ (nδ∞)²`. -/
theorem cayley_chart_energy_rowNorm {K X Xh : Matrix n n ℚ} (hK : Kᵀ = -K)
    (hX : (1 - K) * X = 1) {δ : ℚ} (hR : rowNorm (1 - (1 - K) * Xh) ≤ δ) (x : n → ℚ) :
    |((2 * Xh - 1) *ᵥ x) ⬝ᵥ ((2 * Xh - 1) *ᵥ x) - x ⬝ᵥ x| ≤
      (4 * (Fintype.card n * δ) + 4 * (Fintype.card n * δ) ^ 2) * (x ⬝ᵥ x) := by
  have hδ0 : 0 ≤ δ := (rowNorm_nonneg _).trans hR
  have hn : (Fintype.card n : ℚ) ≤ (Fintype.card n : ℚ) ^ 2 := by
    exact_mod_cast Nat.le_self_pow two_ne_zero (Fintype.card n)
  have hsq : rowNorm (1 - (1 - K) * Xh) ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ (rowNorm_nonneg _) hR 2
  have hfrob := frobSq_le_card_mul_rowNorm_sq (1 - (1 - K) * Xh)
  have hnδ : frobSq (1 - (1 - K) * Xh) ≤ (Fintype.card n * δ) ^ 2 := by
    have hc : (0 : ℚ) ≤ Fintype.card n := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hsq hc
    have h2 := mul_le_mul_of_nonneg_right hn (sq_nonneg δ)
    nlinarith
  exact cayley_chart_energy hK hX (by positivity) hnδ x

end Energy

/-! ## 6. The prox step at an inverse chart -/

section Prox

variable {𝕜 : Type*} [Field 𝕜] {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ]

omit [Fintype τ] in
/-- [proved-derived; formal-checked] **The prox identity up to the chart's left residual.** At a
solved locus `WH = B`, after one return (`H' = H + w f fᵀ`, `B' = B + w(Wf + γg)fᵀ`), the map
updated through an executed chart `X̂` of `H'⁻¹`, `W' = W + wγ g fᵀ X̂`, leaves
`W'H' − B' = −wγ g fᵀ(1 − X̂H')`: the left residual of the chart, released and reported with the
deposit. With the exact inverse it vanishes (`HNN/Normal.normal_prox_step`). -/
theorem prox_chart_residual {W : Matrix τ σ 𝕜} {H : Matrix σ σ 𝕜} {B : Matrix τ σ 𝕜}
    (hsolve : W * H = B) (w γ : 𝕜) (f : σ → 𝕜) (g : τ → 𝕜) (Xh : Matrix σ σ 𝕜) :
    (W + (w * γ) • vecMulVec g f * Xh) * (H + w • vecMulVec f f) -
        (B + w • vecMulVec (W *ᵥ f + γ • g) f) =
      -((w * γ) • vecMulVec g f * (1 - Xh * (H + w • vecMulVec f f))) := by
  rw [Holonics.HNN.Normal.proxCross_eq W w γ f g, ← hsolve]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- [proved-derived; formal-checked] **The prox step's certificate**: over `ℚ`,
`‖W'H' − B'‖∞ ≤ ‖wγ g fᵀ‖∞ · ‖1 − X̂H'‖∞`. -/
theorem prox_chart_certificate {W : Matrix τ σ ℚ} {H : Matrix σ σ ℚ} {B : Matrix τ σ ℚ}
    (hsolve : W * H = B) (w γ : ℚ) (f : σ → ℚ) (g : τ → ℚ) (Xh : Matrix σ σ ℚ) :
    rowNorm ((W + (w * γ) • vecMulVec g f * Xh) * (H + w • vecMulVec f f) -
        (B + w • vecMulVec (W *ᵥ f + γ • g) f)) ≤
      rowNorm ((w * γ) • vecMulVec g f) * rowNorm (1 - Xh * (H + w • vecMulVec f f)) := by
  rw [prox_chart_residual hsolve, rowNorm_neg]
  exact rowNorm_mul_le _ _

end Prox

section Audit

#print axioms newton_schulz_right
#print axioms newton_schulz_left
#print axioms newton_schulz_iter_right
#print axioms newton_schulz_iter_left
#print axioms rounded_refinement_residual
#print axioms rounded_refinement_residual_left
#print axioms warm_start_residual
#print axioms rowNorm_mul_le
#print axioms newton_schulz_iter_rowNorm
#print axioms latticeChart_round
#print axioms rounded_refinement_certificate
#print axioms rounded_refinement_certificate_left
#print axioms roundedIter_certificate
#print axioms warm_start_certificate
#print axioms inverse_chart_deviation
#print axioms feedback_tick
#print axioms feedback_onLattice
#print axioms feedback_rem_bounds
#print axioms feedback_accounting
#print axioms feedback_accounting_zero
#print axioms feedback_tick_deviation
#print axioms feedback_sum_within_half_unit
#print axioms carried_word_accounting
#print axioms executed_adjoint_pairing
#print axioms executed_adjoint_unique
#print axioms exact_adjoint_pairing_defect
#print axioms executed_adjoint_deviation
#print axioms inverse_chart_adjoint_deviation
#print axioms mulVec_dot_le_frobSq
#print axioms frobSq_le_card_mul_rowNorm_sq
#print axioms chart_energy_identity
#print axioms chart_energy_deviation
#print axioms cayley_chart_orthogonal
#print axioms cayley_denominator_det_rat
#print axioms cayley_denominator_expands
#print axioms cayley_chart_error_le_residual
#print axioms cayley_chart_energy
#print axioms cayley_chart_energy_rowNorm
#print axioms prox_chart_residual
#print axioms prox_chart_certificate

end Audit

end Holonics.HNN.LatticeWord
