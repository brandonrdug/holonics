import Mathlib

/-!
# The half from a reversal and a contraction, in the line chart and the circle chart

[definition] Record of November 18 (the half is the positivity of the reversal's own form). A chart
carries a reversal that fixes a section and exchanges its two sides: `z ↦ conj z` fixes the real
axis and exchanges the half-planes; `z ↦ 1 / conj z` fixes the unit circle and exchanges the disc
with its outside. Each side carries a quantity that is positive on it and changes sign across the
section: `Im z` on the line, `1 − ‖z‖²` on the circle. A factor whose pivot `a` stands on one side
is a contraction against its reversed factor at every place on the other side, and the gap of the
two squared lengths is the product of the two places' signed quantities:

* line: `‖z − a‖² − ‖z − conj a‖² = −4 · Im z · Im a` (`line_gap`);
* circle: `‖z − a‖² − ‖1 − conj a · z‖² = −(1 − ‖z‖²)(1 − ‖a‖²)` (`circle_gap`).

A product `P` of factors with every pivot on one side and its reversal (`Pstar`, `Psharp`) then
never have equal length off the section, so the symmetrized sum `P + ε · P*` with `‖ε‖ = 1` has
every zero on the section. The functional equation of the sum is the reversal; the place of its
zeros is the contraction.

[proved-standard; formal-checked] What is proved, on finite products `P z = c · ∏ (z − a j)` over
any nonempty finite index type.

1. **The line (Hermite–Biehler, the direction used).** With every `Im (a j) < 0`:
   `Pstar z = conj (P (conj z))` (`Pstar_eq_conj`); `Im z > 0 → ‖Pstar z‖ < ‖P z‖` and
   `Im z < 0 → ‖P z‖ < ‖Pstar z‖` (`norm_Pstar_lt_norm_P`, `norm_P_lt_norm_Pstar`); and
   `P z + ε · Pstar z = 0 → Im z = 0` (`im_eq_zero_of_symmetrized_zero`). The same on a
   `Polynomial ℂ` of positive degree whose roots all have negative imaginary part
   (`polynomial_im_eq_zero_of_symmetrized_zero`).
2. **Pólya's shift, the universal factor of the heat clock's family.** For a real product
   `F z = c · ∏ (z − r j)` and `h > 0`, both `F (z + i h) + F (z − i h)` and
   `F (z + i h) − F (z − i h)` vanish only at real `z` (`polya_shift_sum`, `polya_shift_diff`):
   `F (· + i h)` is a product with every pivot at height `−h`, and `F (· − i h)` is its reversal.
3. **The circle (the mechanism of the circle theorems of Schur and Cohn).** With every
   `‖a j‖ < 1` and `Psharp z = conj c · ∏ (1 − conj (a j) · z)`:
   `Psharp z = z ^ n · conj (P (1 / conj z))` for `z ≠ 0` (`Psharp_eq`);
   `‖z‖ < 1 → ‖P z‖ < ‖Psharp z‖` and `1 < ‖z‖ → ‖Psharp z‖ < ‖P z‖`
   (`norm_P_lt_norm_Psharp`, `norm_Psharp_lt_norm_P`); and `P z + ε · Psharp z = 0 → ‖z‖ = 1`
   (`norm_eq_one_of_symmetrized_zero`). The same on a `Polynomial ℂ` of positive degree whose roots
   all lie inside the disc, at `z ≠ 0` (`polynomial_norm_eq_one_of_symmetrized_zero`).

[proved-derived; formal-checked] Instances.

4. **Two coupled locks** (atlas `parametron.coupled-locks-lee-yang`): for real `y` with `|y| < 1`,
   `a² + 2ya + 1 = 0 → ‖a‖ = 1` (`two_locks_on_circle`), the circle statement at
   `P z = z (z + y)`, whose pivots `0` and `−y` stand inside the disc.
5. **One cell of a regular complex** (atlas `trace.prime-cycle-half-rank`): for `q > 0` and
   `l² < 4q`, `1 − l u + q u² = 0 → ‖u‖² = 1 / q` (`cell_zero_on_circle`), the circle statement in
   the chart `w = √q · u` at `P w = w (w − l / (2√q))`; the pivot `l / (2√q)` stands inside the disc
   iff `l² < 4q`. Past the edge, `4q < l²`, the cell has a real zero off the circle (`cell_boost`):
   the turn has become a boost.

[counterexample; formal-checked] **One side is load-bearing.** With one pivot above the axis and
one below, `P z = (z − i)(z + 4i)`, the symmetrized sum `P + Pstar = 2z² + 8` vanishes at `2i`
(`mixed_sides_zero_off_axis`).

**What this does not state.** Every statement is about a finite product. No limit to an entire
function is taken (the Laguerre–Pólya class, by which Pólya's shift reaches the approximants of
`ξ`, is not formalized), and nothing here is a statement about `ζ` or `ξ`. The converse of
Hermite–Biehler (real interlacing zeros of the two parts place the pivots on one side), the
simplicity and interlacing of the zeros, Cohn's criterion through the derivative, and the Lee–Yang
theorem for more than two locks are not stated. The count of zeros on the section is not stated
either (the sum's degree can drop when `c + ε · conj c = 0`).

No `axiom`, no `sorry`.
-/

namespace Holonics.Zeta.HermiteBiehlerHalf

open Complex
open scoped ComplexConjugate

noncomputable section

/-! ## A strict comparison of two products -/

/-- [proved-standard; formal-checked] Two products over a nonempty finite type compare strictly
when every factor does and the smaller factors are nonnegative. A smaller factor may vanish. -/
theorem prod_lt_prod_of_nonneg_of_lt {ι : Type*} [Fintype ι] [Nonempty ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i < g i) : ∏ i, f i < ∏ i, g i := by
  by_cases h : ∀ i, 0 < f i
  · exact Finset.prod_lt_prod_of_nonempty (fun i _ => h i) (fun i _ => hfg i)
      Finset.univ_nonempty
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hi0 : f i = 0 := le_antisymm (not_lt.mp hi) (hf i)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi0]
    exact Finset.prod_pos (fun j _ => lt_of_le_of_lt (hf j) (hfg j))

/-! ## The line chart: reversal `z ↦ conj z`, positive quantity `Im` -/

section Line

/-- [proved-standard; formal-checked] **L1, the gap of one factor on the line.** The squared
lengths from a place `z` to a pivot `a` and to its reversal `conj a` differ by `−4 · Im z · Im a`. -/
theorem line_gap (z a : ℂ) :
    ‖z - a‖ ^ 2 - ‖z - conj a‖ ^ 2 = -4 * z.im * a.im := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

/-- [proved-standard; formal-checked] A pivot below the axis is nearer to a place above the axis
through its reversal. -/
theorem line_factor_lt_of_im_pos {z a : ℂ} (ha : a.im < 0) (hz : 0 < z.im) :
    ‖z - conj a‖ < ‖z - a‖ := by
  have h := line_gap z a
  have hprod : z.im * a.im < 0 := mul_neg_of_pos_of_neg hz ha
  have h2 : ‖z - conj a‖ ^ 2 < ‖z - a‖ ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

/-- [proved-standard; formal-checked] A pivot below the axis is nearer to a place below the axis
than its reversal is. -/
theorem line_factor_lt_of_im_neg {z a : ℂ} (ha : a.im < 0) (hz : z.im < 0) :
    ‖z - a‖ < ‖z - conj a‖ := by
  have h := line_gap z a
  have hprod : 0 < z.im * a.im := mul_pos_of_neg_of_neg hz ha
  have h2 : ‖z - a‖ ^ 2 < ‖z - conj a‖ ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

variable {ι : Type*} [Fintype ι]

/-- [definition] A finite product with leading coefficient `c` and pivots `a`. -/
def P (c : ℂ) (a : ι → ℂ) (z : ℂ) : ℂ := c * ∏ j, (z - a j)

/-- [definition] The line reversal of `P`: every pivot and the coefficient conjugated. -/
def Pstar (c : ℂ) (a : ι → ℂ) (z : ℂ) : ℂ := conj c * ∏ j, (z - conj (a j))

/-- [proved-standard; formal-checked] The line reversal is `z ↦ conj (P (conj z))`. -/
theorem Pstar_eq_conj (c : ℂ) (a : ι → ℂ) (z : ℂ) :
    Pstar c a z = conj (P c a (conj z)) := by
  simp [P, Pstar, map_prod]

/-- [proved-standard; formal-checked] **L2, above the axis.** With every pivot below the axis the
reversal is strictly shorter at every place above it. -/
theorem norm_Pstar_lt_norm_P [Nonempty ι] {c : ℂ} (hc : c ≠ 0) {a : ι → ℂ}
    (ha : ∀ j, (a j).im < 0) {z : ℂ} (hz : 0 < z.im) : ‖Pstar c a z‖ < ‖P c a z‖ := by
  simp only [P, Pstar, norm_mul, norm_prod, Complex.norm_conj]
  exact mul_lt_mul_of_pos_left
    (prod_lt_prod_of_nonneg_of_lt _ _ (fun j => norm_nonneg _)
      (fun j => line_factor_lt_of_im_pos (ha j) hz)) (norm_pos_iff.mpr hc)

/-- [proved-standard; formal-checked] **L2, below the axis.** With every pivot below the axis the
product is strictly shorter than its reversal at every place below it. -/
theorem norm_P_lt_norm_Pstar [Nonempty ι] {c : ℂ} (hc : c ≠ 0) {a : ι → ℂ}
    (ha : ∀ j, (a j).im < 0) {z : ℂ} (hz : z.im < 0) : ‖P c a z‖ < ‖Pstar c a z‖ := by
  simp only [P, Pstar, norm_mul, norm_prod, Complex.norm_conj]
  exact mul_lt_mul_of_pos_left
    (prod_lt_prod_of_nonneg_of_lt _ _ (fun j => norm_nonneg _)
      (fun j => line_factor_lt_of_im_neg (ha j) hz)) (norm_pos_iff.mpr hc)

/-- [proved-standard; formal-checked] **L3, Hermite–Biehler (the direction used).** With every pivot
below the axis, the symmetrized sum `P + ε · Pstar`, `‖ε‖ = 1`, vanishes only on the real axis. -/
theorem im_eq_zero_of_symmetrized_zero [Nonempty ι] {c : ℂ} (hc : c ≠ 0) {a : ι → ℂ}
    (ha : ∀ j, (a j).im < 0) {ε : ℂ} (hε : ‖ε‖ = 1) {z : ℂ}
    (h : P c a z + ε * Pstar c a z = 0) : z.im = 0 := by
  have hnorm : ‖P c a z‖ = ‖Pstar c a z‖ := by
    have h' : P c a z = -(ε * Pstar c a z) := eq_neg_of_add_eq_zero_left h
    rw [h', norm_neg, norm_mul, hε, one_mul]
  rcases lt_trichotomy z.im 0 with hlt | heq | hgt
  · exact absurd hnorm (ne_of_lt (norm_P_lt_norm_Pstar hc ha hlt))
  · exact heq
  · exact absurd hnorm.symm (ne_of_lt (norm_Pstar_lt_norm_P hc ha hgt))

/-! ### Pólya's shift -/

/-- [definition] A real finite product: real coefficient `c`, real pivots `r`. -/
def F (c : ℝ) (r : ι → ℝ) (z : ℂ) : ℂ := (c : ℂ) * ∏ j, (z - (r j : ℂ))

/-- [proved-standard; formal-checked] A real product shifted up by `i h` is a product whose pivots
all stand at height `−h`. -/
theorem F_shift_up (c : ℝ) (r : ι → ℝ) (h : ℝ) (z : ℂ) :
    F c r (z + I * h) = P (c : ℂ) (fun j => (r j : ℂ) - I * h) z := by
  simp only [F, P]
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  ring

/-- [proved-standard; formal-checked] A real product shifted down by `i h` is the reversal of the
product shifted up. -/
theorem F_shift_down (c : ℝ) (r : ι → ℝ) (h : ℝ) (z : ℂ) :
    F c r (z - I * h) = Pstar (c : ℂ) (fun j => (r j : ℂ) - I * h) z := by
  simp only [F, Pstar, Complex.conj_ofReal, map_sub, map_mul, Complex.conj_I]
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  ring

/-- [proved-standard; formal-checked] **L4, Pólya's shift (sum).** For a real product `F` and
`h > 0`, `F (z + i h) + F (z − i h)` vanishes only at real `z`. -/
theorem polya_shift_sum [Nonempty ι] {c : ℝ} (hc : c ≠ 0) (r : ι → ℝ) {h : ℝ} (hh : 0 < h)
    {z : ℂ} (hz : F c r (z + I * h) + F c r (z - I * h) = 0) : z.im = 0 := by
  rw [F_shift_up, F_shift_down] at hz
  refine im_eq_zero_of_symmetrized_zero (ε := 1) (Complex.ofReal_ne_zero.mpr hc) (fun j => ?_)
    (by simp) (by simpa using hz)
  simpa using hh

/-- [proved-standard; formal-checked] **L4, Pólya's shift (difference).** For a real product `F`
and `h > 0`, `F (z + i h) − F (z − i h)` vanishes only at real `z`. -/
theorem polya_shift_diff [Nonempty ι] {c : ℝ} (hc : c ≠ 0) (r : ι → ℝ) {h : ℝ} (hh : 0 < h)
    {z : ℂ} (hz : F c r (z + I * h) - F c r (z - I * h) = 0) : z.im = 0 := by
  rw [F_shift_up, F_shift_down] at hz
  refine im_eq_zero_of_symmetrized_zero (ε := -1) (Complex.ofReal_ne_zero.mpr hc) (fun j => ?_)
    (by simp) (by linear_combination hz)
  simpa using hh

/-! ### The counter-specimen -/

/-- [counterexample; formal-checked] **L5, one side is load-bearing.** With one pivot above the
axis (`i`) and one below (`−4i`), the symmetrized sum `P + Pstar = 2z² + 8` vanishes at `2i`, off
the axis. -/
theorem mixed_sides_zero_off_axis :
    (0 < (![I, -4 * I] (0 : Fin 2)).im ∧ (![I, -4 * I] (1 : Fin 2)).im < 0) ∧
      ∃ z : ℂ, P (1 : ℂ) ![I, -4 * I] z + Pstar (1 : ℂ) ![I, -4 * I] z = 0 ∧ z.im ≠ 0 := by
  refine ⟨⟨by simp, by simp⟩, 2 * I, ?_, by simp⟩
  simp only [P, Pstar, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_one,
    map_mul, map_neg, Complex.conj_I, one_mul, Complex.conj_ofNat]
  ring

end Line

/-! ### The line statement on a polynomial -/

section LinePolynomial

/-- [proved-standard; formal-checked] A complex polynomial evaluates as the finite product `P` over
its roots, listed with multiplicity. -/
theorem exists_eval_eq_P (p : Polynomial ℂ) :
    ∃ (n : ℕ) (a : Fin n → ℂ), n = p.natDegree ∧ (∀ j, a j ∈ p.roots) ∧
      ∀ z, p.eval z = P p.leadingCoeff a z := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  refine ⟨p.roots.toList.length, fun j => p.roots.toList.get j, ?_, ?_, ?_⟩
  · rw [Multiset.length_toList]
    exact (Polynomial.splits_iff_card_roots.mp hsplit)
  · intro j
    exact Multiset.mem_toList.mp (List.get_mem _ j)
  · intro z
    rw [hsplit.eval_eq_prod_roots z, P]
    congr 1
    conv_lhs => rw [← Multiset.coe_toList p.roots]
    rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    rw [← List.ofFn_get (List.map (fun a => z - a) p.roots.toList)]
    simp

/-- [proved-standard; formal-checked] **Hermite–Biehler on a polynomial (the direction used).** A
complex polynomial of positive degree whose roots all lie below the axis: the symmetrized sum
`p(z) + ε · conj (p (conj z))`, `‖ε‖ = 1`, vanishes only at real `z`. -/
theorem polynomial_im_eq_zero_of_symmetrized_zero (p : Polynomial ℂ) (hdeg : 0 < p.natDegree)
    (hroots : ∀ a ∈ p.roots, a.im < 0) {ε : ℂ} (hε : ‖ε‖ = 1) {z : ℂ}
    (h : p.eval z + ε * conj (p.eval (conj z)) = 0) : z.im = 0 := by
  obtain ⟨n, a, hn, ha, hP⟩ := exists_eval_eq_P p
  subst hn
  have hne : Nonempty (Fin p.natDegree) := ⟨⟨0, hdeg⟩⟩
  have hc : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hdeg)
  refine im_eq_zero_of_symmetrized_zero hc (fun j => hroots _ (ha j)) hε ?_
  rw [Pstar_eq_conj, ← hP, ← hP]
  exact h

end LinePolynomial

/-! ## The circle chart: reversal `z ↦ 1 / conj z`, positive quantity `1 − ‖z‖²` -/

section Circle

/-- [proved-standard; formal-checked] **C1, the gap of one factor on the circle.** -/
theorem circle_gap (z a : ℂ) :
    ‖z - a‖ ^ 2 - ‖1 - conj a * z‖ ^ 2 = -((1 - ‖z‖ ^ 2) * (1 - ‖a‖ ^ 2)) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im]
  ring

/-- [proved-standard; formal-checked] A pivot inside the disc: at a place inside, the factor is
shorter than its reversal. -/
theorem circle_factor_lt_of_norm_lt {z a : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖z - a‖ < ‖1 - conj a * z‖ := by
  have h := circle_gap z a
  have h1 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have h3 : ‖z - a‖ ^ 2 < ‖1 - conj a * z‖ ^ 2 := by nlinarith [mul_pos h1 h2]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h3

/-- [proved-standard; formal-checked] A pivot inside the disc: at a place outside, the reversal is
shorter than the factor. -/
theorem circle_factor_lt_of_norm_gt {z a : ℂ} (ha : ‖a‖ < 1) (hz : 1 < ‖z‖) :
    ‖1 - conj a * z‖ < ‖z - a‖ := by
  have h := circle_gap z a
  have h1 : 1 - ‖z‖ ^ 2 < 0 := by nlinarith
  have h2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have h3 : ‖1 - conj a * z‖ ^ 2 < ‖z - a‖ ^ 2 := by nlinarith [mul_neg_of_neg_of_pos h1 h2]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h3

variable {ι : Type*} [Fintype ι]

/-- [definition] The circle reversal of `P`: every factor `z − a` becomes `1 − conj a · z`. -/
def Psharp (c : ℂ) (a : ι → ℂ) (z : ℂ) : ℂ := conj c * ∏ j, (1 - conj (a j) * z)

/-- [proved-standard; formal-checked] The circle reversal is `z ↦ zⁿ · conj (P (1 / conj z))`. -/
theorem Psharp_eq (c : ℂ) (a : ι → ℂ) {z : ℂ} (hz : z ≠ 0) :
    Psharp c a z = z ^ Fintype.card ι * conj (P c a (1 / conj z)) := by
  simp only [P, Psharp, map_mul, map_prod, map_sub, map_div₀, map_one, Complex.conj_conj]
  rw [← Finset.card_univ, ← Finset.prod_const, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  field_simp

/-- [proved-standard; formal-checked] **C2, inside the disc.** With every pivot inside the disc the
product is strictly shorter than its reversal at every place inside. -/
theorem norm_P_lt_norm_Psharp [Nonempty ι] {c : ℂ} (hc : c ≠ 0) {a : ι → ℂ}
    (ha : ∀ j, ‖a j‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) : ‖P c a z‖ < ‖Psharp c a z‖ := by
  simp only [P, Psharp, norm_mul, norm_prod, Complex.norm_conj]
  exact mul_lt_mul_of_pos_left
    (prod_lt_prod_of_nonneg_of_lt _ _ (fun j => norm_nonneg _)
      (fun j => circle_factor_lt_of_norm_lt (ha j) hz)) (norm_pos_iff.mpr hc)

/-- [proved-standard; formal-checked] **C2, outside the disc.** With every pivot inside the disc the
reversal is strictly shorter than the product at every place outside. -/
theorem norm_Psharp_lt_norm_P [Nonempty ι] {c : ℂ} (hc : c ≠ 0) {a : ι → ℂ}
    (ha : ∀ j, ‖a j‖ < 1) {z : ℂ} (hz : 1 < ‖z‖) : ‖Psharp c a z‖ < ‖P c a z‖ := by
  simp only [P, Psharp, norm_mul, norm_prod, Complex.norm_conj]
  exact mul_lt_mul_of_pos_left
    (prod_lt_prod_of_nonneg_of_lt _ _ (fun j => norm_nonneg _)
      (fun j => circle_factor_lt_of_norm_gt (ha j) hz)) (norm_pos_iff.mpr hc)

/-- [proved-standard; formal-checked] **C3, the circle theorem's mechanism.** With every pivot
inside the disc, the symmetrized sum `P + ε · Psharp`, `‖ε‖ = 1`, vanishes only on the unit
circle. -/
theorem norm_eq_one_of_symmetrized_zero [Nonempty ι] {c : ℂ} (hc : c ≠ 0) {a : ι → ℂ}
    (ha : ∀ j, ‖a j‖ < 1) {ε : ℂ} (hε : ‖ε‖ = 1) {z : ℂ}
    (h : P c a z + ε * Psharp c a z = 0) : ‖z‖ = 1 := by
  have hnorm : ‖P c a z‖ = ‖Psharp c a z‖ := by
    have h' : P c a z = -(ε * Psharp c a z) := eq_neg_of_add_eq_zero_left h
    rw [h', norm_neg, norm_mul, hε, one_mul]
  rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
  · exact absurd hnorm (ne_of_lt (norm_P_lt_norm_Psharp hc ha hlt))
  · exact heq
  · exact absurd hnorm.symm (ne_of_lt (norm_Psharp_lt_norm_P hc ha hgt))

/-- [proved-standard; formal-checked] **The circle statement on a polynomial.** A complex
polynomial of positive degree `n` whose roots all lie inside the disc: the symmetrized sum
`p(z) + ε · zⁿ · conj (p (1 / conj z))`, `‖ε‖ = 1`, vanishes at `z ≠ 0` only on the unit circle. -/
theorem polynomial_norm_eq_one_of_symmetrized_zero (p : Polynomial ℂ) (hdeg : 0 < p.natDegree)
    (hroots : ∀ a ∈ p.roots, ‖a‖ < 1) {ε : ℂ} (hε : ‖ε‖ = 1) {z : ℂ} (hz : z ≠ 0)
    (h : p.eval z + ε * (z ^ p.natDegree * conj (p.eval (1 / conj z))) = 0) : ‖z‖ = 1 := by
  obtain ⟨n, a, hn, ha, hP⟩ := exists_eval_eq_P p
  subst hn
  have hne : Nonempty (Fin p.natDegree) := ⟨⟨0, hdeg⟩⟩
  have hc : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hdeg)
  refine norm_eq_one_of_symmetrized_zero hc (fun j => hroots _ (ha j)) hε ?_
  rw [Psharp_eq _ _ hz, Fintype.card_fin, ← hP, ← hP]
  exact h

/-! ### Instances -/

/-- [proved-derived; formal-checked] **C4, two coupled locks** (atlas
`parametron.coupled-locks-lee-yang`). For real `y` with `|y| < 1`, every zero of `a² + 2ya + 1` is
on the unit circle: the circle statement at `P z = z (z + y)`, pivots `0` and `−y`. -/
theorem two_locks_on_circle {y : ℝ} (hy : |y| < 1) {a : ℂ}
    (h : a ^ 2 + 2 * (y : ℂ) * a + 1 = 0) : ‖a‖ = 1 := by
  refine norm_eq_one_of_symmetrized_zero (ι := Fin 2) (c := 1) (a := ![0, -(y : ℂ)])
    one_ne_zero ?_ (ε := 1) (by simp) ?_
  · intro j
    fin_cases j
    · simp
    · simpa [Complex.norm_real] using hy
  · simp only [P, Psharp, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_one,
      map_zero, map_neg, Complex.conj_ofReal, one_mul]
    linear_combination h

/-- [proved-derived; formal-checked] **C5, one cell of a regular complex** (atlas
`trace.prime-cycle-half-rank`). For `q > 0` and `l² < 4q`, every zero of `1 − l u + q u²` has
`‖u‖² = 1 / q`: the circle statement in the chart `w = √q · u` at `P w = w (w − l / (2√q))`. -/
theorem cell_zero_on_circle {q l : ℝ} (hq : 0 < q) (hl : l ^ 2 < 4 * q) {u : ℂ}
    (h : 1 - (l : ℂ) * u + (q : ℂ) * u ^ 2 = 0) : ‖u‖ ^ 2 = 1 / q := by
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = q :=
    ⟨Real.sqrt q, Real.sqrt_pos.mpr hq, Real.sq_sqrt hq.le⟩
  obtain ⟨t, ht, htlt⟩ : ∃ t : ℝ, 2 * s * t = l ∧ |t| < 1 := by
    refine ⟨l / (2 * s), by field_simp, ?_⟩
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * s), div_lt_one (by positivity)]
    apply abs_lt_of_sq_lt_sq
    · nlinarith
    · positivity
  have hssc : (s : ℂ) ^ 2 = (q : ℂ) := by exact_mod_cast hss
  have htc : 2 * (s : ℂ) * (t : ℂ) = (l : ℂ) := by exact_mod_cast ht
  have hw : ‖(s : ℂ) * u‖ = 1 := by
    refine norm_eq_one_of_symmetrized_zero (ι := Fin 2) (c := 1) (a := ![0, (t : ℂ)])
      one_ne_zero ?_ (ε := 1) (by simp) ?_
    · intro j
      fin_cases j
      · simp
      · simpa [Complex.norm_real] using htlt
    · simp only [P, Psharp, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_one, map_zero, Complex.conj_ofReal, one_mul]
      linear_combination h + u ^ 2 * hssc - u * htc
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at hw
  rw [eq_div_iff hq.ne']
  calc ‖u‖ ^ 2 * q = (s * ‖u‖) ^ 2 := by rw [← hss]; ring
    _ = 1 := by rw [hw]; norm_num

/-- [proved-derived; formal-checked] **C5, past the edge.** For `q > 0` and `4q < l²` the cell
`1 − l u + q u²` has a real zero off the circle `u² = 1 / q`: the turn has become a boost. -/
theorem cell_boost {q l : ℝ} (hq : 0 < q) (hl : 4 * q < l ^ 2) :
    ∃ u : ℝ, 1 - l * u + q * u ^ 2 = 0 ∧ u ^ 2 ≠ 1 / q := by
  obtain ⟨d, hd2⟩ : ∃ d : ℝ, d ^ 2 = l ^ 2 - 4 * q :=
    ⟨Real.sqrt (l ^ 2 - 4 * q), Real.sq_sqrt (by linarith)⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, 2 * q * u = l + d := ⟨(l + d) / (2 * q), by field_simp⟩
  have hroot : 1 - l * u + q * u ^ 2 = 0 := by
    have h4 : 4 * q * (1 - l * u + q * u ^ 2) = 0 := by
      linear_combination (2 * q * u + d - l) * hu + hd2
    rcases mul_eq_zero.mp h4 with h0 | h0
    · exact absurd h0 (by positivity)
    · exact h0
  refine ⟨u, hroot, fun hu2 => ?_⟩
  have h1 : q * u ^ 2 = 1 := by rw [hu2]; field_simp
  have h2 : l * u = 2 := by linarith
  have h3 : l ^ 2 = 4 * q := by
    calc l ^ 2 = l ^ 2 * (q * u ^ 2) := by rw [h1, mul_one]
      _ = q * (l * u) ^ 2 := by ring
      _ = 4 * q := by rw [h2]; ring
  linarith

end Circle

end

section Audit

#print axioms line_gap
#print axioms norm_Pstar_lt_norm_P
#print axioms norm_P_lt_norm_Pstar
#print axioms Pstar_eq_conj
#print axioms im_eq_zero_of_symmetrized_zero
#print axioms polya_shift_sum
#print axioms polya_shift_diff
#print axioms mixed_sides_zero_off_axis
#print axioms exists_eval_eq_P
#print axioms polynomial_im_eq_zero_of_symmetrized_zero
#print axioms circle_gap
#print axioms Psharp_eq
#print axioms norm_P_lt_norm_Psharp
#print axioms norm_Psharp_lt_norm_P
#print axioms norm_eq_one_of_symmetrized_zero
#print axioms polynomial_norm_eq_one_of_symmetrized_zero
#print axioms two_locks_on_circle
#print axioms cell_zero_on_circle
#print axioms cell_boost

end Audit

end Holonics.Zeta.HermiteBiehlerHalf
