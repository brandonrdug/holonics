import Mathlib
import HolonicsResearch.Landmarks.IharaBass
import HolonicsResearch.Landmarks.RegularGraphNormForm
import HolonicsResearch.Zeta.HermiteBiehlerHalf

/-!
# A regular complex: the zeros of its dart determinant and the count of its closed walks

[proved-derived; formal-checked] `Landmarks/IharaBass` proves the determinant formula of a finite
complex of contacts in every commutative ring and stops before the spectrum.
`Zeta/HermiteBiehlerHalf` and `Landmarks/RegularGraphNormForm` place one cell `1 − λ u + q u²`.
This module joins them on a complex with `q + 1` darts at every cell.  There the cell operator
`A = adjacency ℝ a b` is symmetric, so it has real modes `λ i` (`eigen a b i`, one for each index
of `V`; `exists_eigen_eq_count`: one of them is `q + 1`), and the dart operator `B = hashimoto` is
read cell by cell.  It is the Lean owner of the box of #410 "on a finite complex with `q + 1`
contacts a cell, the closed-walk count within `2(n − 1)q^(l/2)` of its smooth part when every other
eigenvalue has `λ² ≤ 4q`", and it serves the atlas rows `trace.ihara-zeta` and
`trace.prime-cycle-half-rank`.

What is proved.

* **Z1, the factorization** (`det_cell`, `ihara_bass_spectral`):
  `det ((1 + q u²) − u A) = ∏ i, (1 − λ i u + q u²)`, hence
  `(1 − u²)^|V| · det (1 − u B) = (1 − u²)^|E| · ∏ i, (1 − λ i u + q u²)` for every complex `u`.
* **Z2, the zeros** (`det_hashimoto_eq_zero_iff_cell`, `zeros_tempered`,
  `exists_real_zero_off_circle`).  Away from `u² = 1` the determinant vanishes at `u` exactly when
  one cell does.  If every mode is in the gap `λ² < 4q` or is a count `λ² = (q + 1)²`, every zero
  with `u² ≠ 1` has `‖u‖² = 1/q` or is `±1/q`: the half, with the counts at zero delay.  A mode
  with `4q < λ² ≠ (q + 1)²` gives a real zero with `u² ≠ 1/q` (`q ≥ 1`): the hypothesis is
  load-bearing.
* **Z3, the characteristic polynomial** (`hashimoto_charpoly`, `hashimoto_charpoly_linear`): with
  `|V| ≤ |E|` (`card_le_card_of_regular`: it holds once `q ≥ 1`, from `2|E| = (q + 1)|V|`),
  `charpoly B = (X² − 1)^(|E| − |V|) · ∏ i, (X² − λ i X + q)`.
* **Z4, the count** (`trace_hashimoto_pow`): for any roots `α i`, `β i` of the cells
  (`α i + β i = λ i`, `α i · β i = q`; `exists_cell_root_families`),
  `tr (B ^ l) = (|E| − |V|)(1 + (−1)^l) + ∑ i, (α i ^ l + β i ^ l)`.
* **Z5, the bound** (`walkCount_bound`, `walkCount_bound_of_one_le`): with a mode
  `λ i₀ = q + 1` and every other mode in the closed gap `λ² ≤ 4q`, for every `l` (zero included)
  `|N l − (q^l + 1) − (|E| − |V|)(1 + (−1)^l)| ≤ 2 (|V| − 1) (√q)^l`, where
  `N l = walkCount a b l` is the trace of `B ^ l` read in `ℝ`.
* **Z6, the bound is the half** (`cell_contribution_exceeds`): a cell with `4q < λ²` has real roots
  `r`, `s` and contributes `r^(2k) + s^(2k) > 2 (√q)^(2k)` at every even length `2k ≥ 2`, more
  than a tempered cell is allowed.

[proved-standard; formal-checked] One general statement was missing from the library at this pin
and is proved here: over an algebraically closed field `tr (M ^ l)` is the sum of the `l`-th powers
of the characteristic roots with multiplicity (`trace_pow_eq_sum_roots_charpoly`; Mathlib holds
`l = 1` as `Matrix.trace_eq_sum_roots_charpoly`).  The proof splits the space into the generalized
eigenspaces, on each of which the map is its root plus a commuting nilpotent
(`trace_pow_restrict_maxGenEigenspace`), and reads their dimensions as root multiplicities.

## What this does not state

* That `tr (B ^ l)` counts closed walks of `l` darts without backtracking.  `walkCount` is defined
  as that trace; the reading of a power's diagonal entry as a count of dart sequences is the
  standard one and is not formalized here.
* The Euler product over primitive closed walks, the dynamical side of `trace.ihara-zeta`.
* Anything about which complexes are tempered.  The hypothesis `λ² ≤ 4q` on the modes other than the
  count is taken, never derived; a second mode at `q + 1` (two components) or one at `−(q + 1)`
  (two sides, `q ≥ 2`) fails it, and Z5 is silent there.
* A converse of Z5 for the whole count.  Z6 bounds one cell's contribution from below; it does not
  show that the sum over all cells leaves the bound.
* Anything about the integers.  A regular complex is a finite specimen of the half; nothing here is
  a statement about `ζ`.

Every theorem is discharged and none depends on `sorryAx`.
-/

open Matrix Module

namespace Holonics.Landmarks.RegularComplexZeros

open Polynomial

/-! ## The trace of a power is the power sum of the characteristic roots -/

section TracePower

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- [proved-standard; formal-checked] On one generalized eigenspace the trace of the `l`-th power is
`μ ^ l` times the space's dimension: there the map is `μ` plus a nilpotent that commutes with it. -/
theorem trace_pow_restrict_maxGenEigenspace (f : End K W) (μ : K) (l : ℕ) :
    LinearMap.trace K (f.maxGenEigenspace μ)
        ((f.restrict (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ)) ^ l) =
      μ ^ l * (finrank K (f.maxGenEigenspace μ) : K) := by
  set g := f.restrict (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ) with hg
  have hnil : IsNilpotent (g - algebraMap K (End K (f.maxGenEigenspace μ)) μ) :=
    f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  induction l with
  | zero => simp [LinearMap.trace_one]
  | succ l ih =>
    have hcomm : Commute (g ^ l) g := (Commute.refl g).pow_left l
    have h := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ hcomm hnil
    rw [pow_succ, Module.End.mul_eq_comp, h, ih]
    ring

/-- [proved-standard; formal-checked] Over an algebraically closed field the trace of `f ^ l` is the
sum of the `l`-th powers of the characteristic roots, each with its multiplicity. -/
theorem linearMap_trace_pow_eq_sum_roots [IsAlgClosed K] (f : End K W) (l : ℕ) :
    LinearMap.trace K W (f ^ l) = (f.charpoly.roots.map (· ^ l)).sum := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hmaps : ∀ μ, Set.MapsTo (f ^ l) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right l) μ
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hmaps]
  have hrestrict : ∀ μ, (f ^ l).restrict (hmaps μ) =
      (f.restrict (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ)) ^ l := by
    intro μ
    exact (Module.End.pow_restrict l _ _).symm
  simp_rw [hrestrict, trace_pow_restrict_maxGenEigenspace, LinearMap.finrank_maxGenEigenspace_eq]
  rw [Finset.sum_multiset_map_count]
  have hset : h_fin.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    have hne : f.charpoly ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
    have h1 : f.maxGenEigenspace μ = ⊥ ↔ f.charpoly.rootMultiplicity μ = 0 := by
      rw [← Submodule.finrank_eq_zero (R := K), LinearMap.finrank_maxGenEigenspace_eq]
    have h2 : μ ∈ f.charpoly.roots ↔ 0 < f.charpoly.rootMultiplicity μ := by
      rw [Polynomial.mem_roots hne, Polynomial.rootMultiplicity_pos hne]
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Multiset.mem_toFinset, Ne, h1, h2]
    omega
  rw [hset]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Polynomial.count_roots, nsmul_eq_mul, mul_comm]

end TracePower

/-- [proved-standard; formal-checked] **The trace of a power.**  For a square matrix over an
algebraically closed field, `tr (M ^ l)` is the sum of the `l`-th powers of the roots of the
characteristic polynomial, each with its multiplicity. -/
theorem trace_pow_eq_sum_roots_charpoly {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    [IsAlgClosed K] (M : Matrix n n K) (l : ℕ) :
    (M ^ l).trace = (M.charpoly.roots.map (· ^ l)).sum := by
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow, linearMap_trace_pow_eq_sum_roots,
    Matrix.charpoly_toLin']

/-! ## Power sums of the roots of a product -/

section PowerSum

variable {K : Type*} [Field K]

/-- [definition] The `l`-th power sum of the roots of a polynomial, with multiplicity. -/
noncomputable def psum (l : ℕ) (p : K[X]) : K := (p.roots.map (· ^ l)).sum

/-- [proved-derived; formal-checked] A linear factor contributes its root's power. -/
theorem psum_X_sub_C (l : ℕ) (r : K) : psum l (X - C r) = r ^ l := by
  simp [psum]

/-- [proved-derived; formal-checked] The power sum is additive over a nonzero product. -/
theorem psum_mul (l : ℕ) {p q : K[X]} (h : p * q ≠ 0) :
    psum l (p * q) = psum l p + psum l q := by
  simp [psum, roots_mul h]

/-- [proved-derived; formal-checked] A `k`-th power contributes `k` times. -/
theorem psum_pow (l : ℕ) (p : K[X]) (k : ℕ) : psum l (p ^ k) = k * psum l p := by
  simp [psum, Multiset.map_nsmul, Multiset.sum_nsmul]

/-- [proved-derived; formal-checked] The power sum is additive over a finite product of nonzero
factors. -/
theorem psum_prod (l : ℕ) {ι : Type*} (s : Finset ι) (f : ι → K[X]) (h : ∀ i ∈ s, f i ≠ 0) :
    psum l (∏ i ∈ s, f i) = ∑ i ∈ s, psum l (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [psum]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, f j ≠ 0 := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hprod : ∏ j ∈ s, f j ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      psum_mul l (mul_ne_zero (h i (Finset.mem_insert_self i s)) hprod), ih hs]

end PowerSum

/-! ## A determinant read from a split characteristic polynomial -/

/-- [proved-derived; formal-checked] If `M`'s characteristic polynomial is `∏ (X − μ i)`, then
`det (c − u M) = ∏ (c − u μ i)` for every `c`, `u` of the field, `u = 0` included. -/
theorem det_smul_one_sub_smul {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (M : Matrix n n K) (μ : n → K) (h : M.charpoly = ∏ i, (X - C (μ i))) (c u : K) :
    (c • (1 : Matrix n n K) - u • M).det = ∏ i, (c - u * μ i) := by
  by_cases hu : u = 0
  · subst hu
    simp
  · have h1 : c • (1 : Matrix n n K) - u • M = u • (Matrix.scalar n (c / u) - M) := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_sub, smul_smul,
        mul_div_cancel₀ c hu]
    rw [h1, Matrix.det_smul, ← Matrix.eval_charpoly, h, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    field_simp

/-- [proved-standard; formal-checked] Two numbers with a given sum and product exist in `ℂ`. -/
theorem exists_cell_roots (l q : ℂ) : ∃ α β : ℂ, α + β = l ∧ α * β = q := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (l ^ 2 - 4 * q) (by norm_num : 0 < 2)
  exact ⟨(l + s) / 2, (l - s) / 2, by ring, by linear_combination (-1 / 4 : ℂ) * hs⟩

/-! ## The cell operator's spectrum -/

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (a b : E → V)

omit [Fintype V] in
/-- [proved-derived; formal-checked] The cell operator of a finite complex is Hermitian over `ℝ`. -/
theorem adjacency_isHermitian : (IharaBass.adjacency ℝ a b).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact IharaBass.adjacency_transpose ℝ a b

/-- [definition] The modes of the cell operator: its real eigenvalues, one for each cell's index. -/
noncomputable def eigen : V → ℝ := (adjacency_isHermitian a b).eigenvalues

/-- [proved-standard; formal-checked] The cell operator's characteristic polynomial splits over `ℝ`
at its modes. -/
theorem adjacency_charpoly :
    (IharaBass.adjacency ℝ a b).charpoly = ∏ i, (X - C (eigen a b i)) := by
  have h := (adjacency_isHermitian a b).charpoly_eq
  simpa [eigen] using h

/-- [proved-derived; formal-checked] The same splitting read over `ℂ`. -/
theorem adjacency_charpoly_complex :
    (IharaBass.adjacency ℂ a b).charpoly = ∏ i, (X - C ((eigen a b i : ℝ) : ℂ)) := by
  rw [← IharaBass.adjacency_map a b (algebraMap ℝ ℂ), Matrix.charpoly_map, adjacency_charpoly,
    Polynomial.map_prod]
  simp

omit [DecidableEq E] in
/-- [proved-derived; formal-checked] On a complex with `q + 1` darts at every cell the constant
reading is a mode of the cell operator at `q + 1`: `A 1 = (q + 1) 1`. -/
theorem adjacency_mulVec_one {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1) :
    IharaBass.adjacency ℝ a b *ᵥ (fun _ => (1 : ℝ)) = fun _ => (q : ℝ) + 1 := by
  funext v
  simp only [Matrix.mulVec, dotProduct, mul_one]
  simp_rw [IharaBass.adjacency_apply]
  rw [← Nat.cast_sum]
  have hfib : ∑ w, (Finset.univ.filter fun d : E ⊕ E =>
      IharaBass.src a b d = v ∧ IharaBass.tgt a b d = w).card =
      (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := IharaBass.tgt a b) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.filter_filter]
  rw [hfib, hreg v]
  push_cast
  ring

/-- [proved-derived; formal-checked] **The count's mode exists.**  On a nonempty complex with
`q + 1` darts at every cell some mode is `q + 1`. -/
theorem exists_eigen_eq_count [Nonempty V] {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1) :
    ∃ i₀, eigen a b i₀ = (q : ℝ) + 1 := by
  have hdet : (Matrix.scalar V ((q : ℝ) + 1) - IharaBass.adjacency ℝ a b).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have := congrFun h (Classical.arbitrary V)
      simp at this
    · rw [Matrix.sub_mulVec, adjacency_mulVec_one a b hreg]
      funext v
      simp [Matrix.scalar_apply]
  rw [← Matrix.eval_charpoly, adjacency_charpoly, eval_prod] at hdet
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hdet
  simp only [eval_sub, eval_X, eval_C] at hi
  exact ⟨i, by linarith⟩

/-! ## Z1. The factorization over the modes -/

/-- [proved-derived; formal-checked] **The cell determinant splits over the modes.**
`det ((1 + q u²) − u A) = ∏ i, (1 − λ i u + q u²)` for every complex `u`. -/
theorem det_cell (q : ℕ) (u : ℂ) :
    ((1 + (q : ℂ) * u ^ 2) • (1 : Matrix V V ℂ) - u • IharaBass.adjacency ℂ a b).det =
      ∏ i, (1 - ((eigen a b i : ℝ) : ℂ) * u + (q : ℂ) * u ^ 2) := by
  rw [det_smul_one_sub_smul _ _ (adjacency_charpoly_complex a b)]
  exact Finset.prod_congr rfl fun i _ => by ring

/-- [proved-derived; formal-checked] **Ihara–Bass on a regular complex, in its modes.**  With `q + 1`
darts at every cell,
`(1 − u²)^|V| · det (1 − u B) = (1 − u²)^|E| · ∏ i, (1 − λ i u + q u²)`. -/
theorem ihara_bass_spectral {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (u : ℂ) :
    (1 - u ^ 2) ^ Fintype.card V * (1 - u • IharaBass.hashimoto ℂ a b).det =
      (1 - u ^ 2) ^ Fintype.card E *
        ∏ i, (1 - ((eigen a b i : ℝ) : ℂ) * u + (q : ℂ) * u ^ 2) := by
  rw [IharaBass.ihara_bass_regular ℂ a b hreg u, det_cell, mul_comm]

/-! ## Z2. The zeros -/

/-- [proved-derived; formal-checked] **The zeros are the cells' zeros.**  Away from `u² = 1`, the
dart determinant vanishes at `u` exactly when one mode's cell `1 − λ u + q u²` does. -/
theorem det_hashimoto_eq_zero_iff_cell {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    {u : ℂ} (hu : u ^ 2 ≠ 1) :
    (1 - u • IharaBass.hashimoto ℂ a b).det = 0 ↔
      ∃ i, 1 - ((eigen a b i : ℝ) : ℂ) * u + (q : ℂ) * u ^ 2 = 0 := by
  rw [IharaBass.det_hashimoto_eq_zero_iff_regular ℂ a b hreg hu, det_cell,
    Finset.prod_eq_zero_iff]
  simp

/-- [proved-derived; formal-checked] A zero of a cell inside the gap `λ² < 4q` is on the circle
`‖u‖² = 1/q` (`HermiteBiehlerHalf.cell_zero_on_circle`). -/
theorem norm_sq_of_cell_zero {q : ℕ} {lam : ℝ} (hlam : lam ^ 2 < 4 * (q : ℝ)) {u : ℂ}
    (h : 1 - (lam : ℂ) * u + (q : ℂ) * u ^ 2 = 0) : ‖u‖ ^ 2 = 1 / (q : ℝ) := by
  have hq : (0 : ℝ) < q := by nlinarith [sq_nonneg lam]
  have h' : 1 - (lam : ℂ) * u + (((q : ℝ)) : ℂ) * u ^ 2 = 0 := by
    simpa using h
  exact Holonics.Zeta.HermiteBiehlerHalf.cell_zero_on_circle hq hlam h'

/-- [proved-derived; formal-checked] The cell of a count, `λ = ±(q + 1)`, is
`(1 ∓ u)(1 ∓ q u)`: away from `u² = 1` its zero is `u = ±1/q`. -/
theorem trivial_cell_zero {q : ℕ} {lam : ℝ} (hlam : lam ^ 2 = ((q : ℝ) + 1) ^ 2) {u : ℂ}
    (hu : u ^ 2 ≠ 1) (h : 1 - (lam : ℂ) * u + (q : ℂ) * u ^ 2 = 0) :
    u = 1 / (q : ℂ) ∨ u = -(1 / (q : ℂ)) := by
  have hu1 : u ≠ 1 := fun h1 => hu (by rw [h1]; norm_num)
  have hu2 : u ≠ -1 := fun h1 => hu (by rw [h1]; norm_num)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hlam with rfl | rfl
  · have hfac : (1 - u) * (1 - (q : ℂ) * u) = 0 := by
      push_cast at h ⊢
      linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd (sub_eq_zero.mp h1).symm hu1
    · left
      have hqu : (q : ℂ) * u = 1 := (sub_eq_zero.mp h1).symm
      have hq0 : (q : ℂ) ≠ 0 := fun h0 => by
        rw [h0, zero_mul] at hqu
        exact zero_ne_one hqu
      rw [eq_div_iff hq0]
      linear_combination hqu
  · have hfac : (1 + u) * (1 + (q : ℂ) * u) = 0 := by
      push_cast at h ⊢
      linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd (eq_neg_of_add_eq_zero_right h1) hu2
    · right
      have hqu : (q : ℂ) * u = -1 := by linear_combination h1
      have hq0 : (q : ℂ) ≠ 0 := fun h0 => by
        rw [h0, zero_mul] at hqu
        exact one_ne_zero (neg_eq_zero.mp hqu.symm)
      rw [eq_neg_iff_add_eq_zero, eq_comm, ← sub_eq_zero]
      field_simp
      linear_combination -hqu

/-- [proved-derived; formal-checked] **The tempered complex: every zero on the circle or at a
count.**  If every mode is in the gap, `λ² < 4q`, or is a count, `λ² = (q + 1)²`, then every zero `u`
of the dart determinant with `u² ≠ 1` has `‖u‖² = 1/q`, or is `1/q`, or is `−1/q`. -/
theorem zeros_tempered {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (htemp : ∀ i, (eigen a b i) ^ 2 < 4 * (q : ℝ) ∨ (eigen a b i) ^ 2 = ((q : ℝ) + 1) ^ 2)
    {u : ℂ} (hu : u ^ 2 ≠ 1) (h0 : (1 - u • IharaBass.hashimoto ℂ a b).det = 0) :
    ‖u‖ ^ 2 = 1 / (q : ℝ) ∨ u = 1 / (q : ℂ) ∨ u = -(1 / (q : ℂ)) := by
  obtain ⟨i, hi⟩ := (det_hashimoto_eq_zero_iff_cell a b hreg hu).mp h0
  rcases htemp i with hlt | heq
  · exact Or.inl (norm_sq_of_cell_zero hlt hi)
  · exact Or.inr (trivial_cell_zero heq hu hi)

/-- [proved-derived; formal-checked] **The converse specimen.**  A mode outside the gap that is not
a count, `4q < λ² ≠ (q + 1)²`, gives the dart determinant a real zero off the circle. -/
theorem exists_real_zero_off_circle {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hq : 1 ≤ q) {i : V} (h1 : 4 * (q : ℝ) < (eigen a b i) ^ 2)
    (h2 : (eigen a b i) ^ 2 ≠ ((q : ℝ) + 1) ^ 2) :
    ∃ u : ℝ, (1 - (u : ℂ) • IharaBass.hashimoto ℂ a b).det = 0 ∧ u ^ 2 ≠ 1 / (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨u, hu, hne⟩ := Holonics.Zeta.HermiteBiehlerHalf.cell_boost hq0 h1
  refine ⟨u, ?_, hne⟩
  have hu1 : (u : ℂ) ^ 2 ≠ 1 := by
    intro h
    have hr : u ^ 2 = 1 := by exact_mod_cast h
    apply h2
    have hr' : u ^ 2 = 1 ^ 2 := by rw [hr]; norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hr' with rfl | rfl
    · have hl : eigen a b i = (q : ℝ) + 1 := by linarith
      rw [hl]
    · have hl : eigen a b i = -((q : ℝ) + 1) := by linarith
      rw [hl]
      ring
  rw [det_hashimoto_eq_zero_iff_cell a b hreg hu1]
  refine ⟨i, ?_⟩
  have := congrArg (fun x : ℝ => (x : ℂ)) hu
  simpa using this

/-! ## Z3. The characteristic polynomial of the dart operator -/

omit [DecidableEq E] in
/-- [proved-derived; formal-checked] Counting darts by their start: `2 |E| = (q + 1) |V|`. -/
theorem two_mul_card_contacts {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1) :
    2 * Fintype.card E = (q + 1) * Fintype.card V := by
  have h := Finset.card_eq_sum_card_fiberwise (f := IharaBass.src a b)
    (s := (Finset.univ : Finset (E ⊕ E))) (t := (Finset.univ : Finset V))
    (fun _ _ => Finset.mem_univ _)
  simp only [hreg, Finset.sum_const, Finset.card_univ, Fintype.card_sum, smul_eq_mul] at h
  rw [two_mul, h, mul_comm]

omit [DecidableEq E] in
/-- [proved-derived; formal-checked] With at least two darts at every cell there are at least as
many contacts as cells. -/
theorem card_le_card_of_regular {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hq : 1 ≤ q) : Fintype.card V ≤ Fintype.card E := by
  have h := two_mul_card_contacts a b hreg
  nlinarith

/-- [proved-derived; formal-checked] **The dart operator's characteristic polynomial.**  On a
regular complex with `|V| ≤ |E|`,
`charpoly B = (X² − 1)^(|E| − |V|) · ∏ i, (X² − λ i X + q)`. -/
theorem hashimoto_charpoly {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) :
    (IharaBass.hashimoto ℂ a b).charpoly =
      (X ^ 2 - 1) ^ (Fintype.card E - Fintype.card V) *
        ∏ i, (X ^ 2 - C ((eigen a b i : ℝ) : ℂ) * X + C (q : ℂ)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hfin : ({0, 1, -1} : Set ℂ).Finite := Set.toFinite _
  refine hfin.infinite_compl.mono fun x hx => ?_
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  obtain ⟨hx0, hx1, hx2⟩ := hx
  have hxsq : x ^ 2 ≠ 1 := by
    intro h
    have h' : x ^ 2 = 1 ^ 2 := by rw [h]; norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h' with h1 | h1
    · exact hx1 h1
    · exact hx2 h1
  show eval x _ = eval x _
  rw [Matrix.eval_charpoly, eval_mul, eval_pow, eval_prod]
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, eval_C, eval_add]
  have h1 : Matrix.scalar (E ⊕ E) x - IharaBass.hashimoto ℂ a b =
      x • (1 - x⁻¹ • IharaBass.hashimoto ℂ a b) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_sub, smul_smul,
      mul_inv_cancel₀ hx0, one_smul]
  rw [h1, Matrix.det_smul, Fintype.card_sum]
  have hsp := ihara_bass_spectral a b hreg x⁻¹
  have hne : (1 - x⁻¹ ^ 2) ≠ 0 := by
    intro h
    apply hxsq
    have h2 : x⁻¹ ^ 2 = 1 := (sub_eq_zero.mp h).symm
    rw [inv_pow] at h2
    exact inv_eq_one.mp h2
  have hdet : (1 - x⁻¹ • IharaBass.hashimoto ℂ a b).det =
      (1 - x⁻¹ ^ 2) ^ (Fintype.card E - Fintype.card V) *
        ∏ i, (1 - ((eigen a b i : ℝ) : ℂ) * x⁻¹ + (q : ℂ) * x⁻¹ ^ 2) := by
    refine mul_left_cancel₀ (pow_ne_zero (Fintype.card V) hne) ?_
    rw [hsp, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hVE]
  rw [hdet]
  have hpow : x ^ (Fintype.card E + Fintype.card E) =
      (x ^ 2) ^ (Fintype.card E - Fintype.card V) * (x ^ 2) ^ Fintype.card V := by
    rw [← pow_add, Nat.sub_add_cancel hVE, ← pow_mul]
    congr 1
    ring
  have hA : (x ^ 2) ^ (Fintype.card E - Fintype.card V) *
      (1 - x⁻¹ ^ 2) ^ (Fintype.card E - Fintype.card V) =
      (x ^ 2 - 1) ^ (Fintype.card E - Fintype.card V) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hB : (x ^ 2) ^ Fintype.card V *
      ∏ i, (1 - ((eigen a b i : ℝ) : ℂ) * x⁻¹ + (q : ℂ) * x⁻¹ ^ 2) =
      ∏ i, (x ^ 2 - ((eigen a b i : ℝ) : ℂ) * x + (q : ℂ)) := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    field_simp
  rw [hpow, ← hA, ← hB]
  ring

/-- [proved-derived; formal-checked] The same polynomial in linear factors: for any `α i`, `β i`
with `α i + β i = λ i` and `α i · β i = q`,
`charpoly B = ((X − 1)(X + 1))^(|E| − |V|) · ∏ i, (X − α i)(X − β i)`. -/
theorem hashimoto_charpoly_linear {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) {α β : V → ℂ}
    (hsum : ∀ i, α i + β i = ((eigen a b i : ℝ) : ℂ)) (hprod : ∀ i, α i * β i = (q : ℂ)) :
    (IharaBass.hashimoto ℂ a b).charpoly =
      ((X - C 1) * (X - C (-1))) ^ (Fintype.card E - Fintype.card V) *
        ∏ i, ((X - C (α i)) * (X - C (β i))) := by
  rw [hashimoto_charpoly a b hreg hVE]
  congr 1
  · congr 1
    simp only [map_one, map_neg]
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hsum i, ← hprod i]
    simp only [C_add, C_mul]
    ring

/-! ## Z4. The count of closed walks -/

/-- [proved-standard; formal-checked] For each mode a pair `α i`, `β i` with `α i + β i = λ i` and
`α i · β i = q` exists over `ℂ`: the two roots of the cell `X² − λ i X + q`. -/
theorem exists_cell_root_families (q : ℕ) :
    ∃ α β : V → ℂ, (∀ i, α i + β i = ((eigen a b i : ℝ) : ℂ)) ∧ (∀ i, α i * β i = (q : ℂ)) := by
  choose α β h1 h2 using fun i : V => exists_cell_roots ((eigen a b i : ℝ) : ℂ) (q : ℂ)
  exact ⟨α, β, h1, h2⟩

/-- [proved-derived; formal-checked] **The count as a sum over the modes.**  On a regular complex
with `|V| ≤ |E|`, for any roots `α i`, `β i` of the cells,
`tr (B ^ l) = (|E| − |V|)(1 + (−1)^l) + ∑ i, (α i ^ l + β i ^ l)`. -/
theorem trace_hashimoto_pow {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) {α β : V → ℂ}
    (hsum : ∀ i, α i + β i = ((eigen a b i : ℝ) : ℂ)) (hprod : ∀ i, α i * β i = (q : ℂ))
    (l : ℕ) :
    ((IharaBass.hashimoto ℂ a b) ^ l).trace =
      ((Fintype.card E - Fintype.card V : ℕ) : ℂ) * (1 + (-1) ^ l) +
        ∑ i, (α i ^ l + β i ^ l) := by
  have hlin : ∀ r : ℂ, (X - C r : ℂ[X]) ≠ 0 := fun r => X_sub_C_ne_zero r
  have hpair : ∀ i, (X - C (α i)) * (X - C (β i)) ≠ (0 : ℂ[X]) :=
    fun i => mul_ne_zero (hlin _) (hlin _)
  have hprodne : ∏ i, ((X - C (α i)) * (X - C (β i))) ≠ (0 : ℂ[X]) :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hpair i
  have hunit : ((X - C 1) * (X - C (-1)) : ℂ[X]) ≠ 0 := mul_ne_zero (hlin _) (hlin _)
  rw [trace_pow_eq_sum_roots_charpoly, hashimoto_charpoly_linear a b hreg hVE hsum hprod]
  change psum l _ = _
  rw [psum_mul l (mul_ne_zero (pow_ne_zero _ hunit) hprodne), psum_pow, psum_mul l hunit,
    psum_X_sub_C, psum_X_sub_C, psum_prod l _ _ (fun i _ => hpair i), one_pow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [psum_mul l (hpair i), psum_X_sub_C, psum_X_sub_C]

/-- [definition] The count of closed walks of `l` darts without backtracking, with a marked start:
the trace of the `l`-th power of the dart operator, read in `ℝ`. -/
noncomputable def walkCount (l : ℕ) : ℝ := ((IharaBass.hashimoto ℝ a b) ^ l).trace

omit [Fintype V] in
/-- [proved-derived; formal-checked] The count read in `ℂ` is the complex dart operator's trace. -/
theorem walkCount_cast (l : ℕ) :
    ((walkCount a b l : ℝ) : ℂ) = ((IharaBass.hashimoto ℂ a b) ^ l).trace := by
  have h : ∀ M : Matrix (E ⊕ E) (E ⊕ E) ℝ,
      (M.map (algebraMap ℝ ℂ)).trace = ((M.trace : ℝ) : ℂ) := by
    intro M
    simp [Matrix.trace]
  rw [walkCount, ← h, ← IharaBass.hashimoto_map a b (algebraMap ℝ ℂ), ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, map_pow]

/-! ## Z5. The bound on the count -/

/-- [proved-derived; formal-checked] **The count is within `2 (n − 1) q^(l/2)` of its smooth part.**
On a regular complex with `|V| ≤ |E|`, a mode `λ i₀ = q + 1` (the count) and every other mode in the
closed gap `λ² ≤ 4q`: for every `l`,
`|N l − (q^l + 1) − (|E| − |V|)(1 + (−1)^l)| ≤ 2 (|V| − 1) (√q)^l`. -/
theorem walkCount_bound {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (l : ℕ) :
    |walkCount a b l - ((q : ℝ) ^ l + 1) -
        ((Fintype.card E : ℝ) - Fintype.card V) * (1 + (-1) ^ l)| ≤
      2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ l := by
  obtain ⟨α, β, hsum, hprod⟩ := exists_cell_root_families a b q
  have htr := trace_hashimoto_pow a b hreg hVE hsum hprod l
  rw [← walkCount_cast] at htr
  -- the count's own cell: its roots are `q` and `1`
  have htriv : α i₀ ^ l + β i₀ ^ l = (q : ℂ) ^ l + 1 := by
    have hs := hsum i₀
    have hp := hprod i₀
    rw [h0] at hs
    push_cast at hs
    have hfac : (α i₀ - 1) * (α i₀ - (q : ℂ)) = 0 := by
      linear_combination α i₀ * hs - hp
    rcases mul_eq_zero.mp hfac with h | h
    · have ha : α i₀ = 1 := sub_eq_zero.mp h
      have hb : β i₀ = (q : ℂ) := by
        rw [ha] at hs
        linear_combination hs
      rw [ha, hb]
      ring
    · have ha : α i₀ = (q : ℂ) := sub_eq_zero.mp h
      have hb : β i₀ = 1 := by
        rw [ha] at hs
        linear_combination hs
      rw [ha, hb]
      ring
  -- every other cell: both roots of modulus `√q`
  have hnorm : ∀ i, i ≠ i₀ → ‖α i‖ = Real.sqrt q ∧ ‖β i‖ = Real.sqrt q := by
    intro i hi
    have hα : α i ^ 2 - ((eigen a b i : ℝ) : ℂ) * α i + (((q : ℝ)) : ℂ) = 0 := by
      rw [← hsum i]
      push_cast
      linear_combination (-1 : ℂ) * hprod i
    have hβ : β i ^ 2 - ((eigen a b i : ℝ) : ℂ) * β i + (((q : ℝ)) : ℂ) = 0 := by
      rw [← hsum i]
      push_cast
      linear_combination (-1 : ℂ) * hprod i
    have h1 := RegularGraphNormForm.cell_normSq_of_le hα (htemp i hi)
    have h2 := RegularGraphNormForm.cell_normSq_of_le hβ (htemp i hi)
    rw [Complex.normSq_eq_norm_sq] at h1 h2
    constructor
    · rw [← h1, Real.sqrt_sq (norm_nonneg _)]
    · rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  -- the remainder is the sum over the other cells
  have hrem : ((walkCount a b l - ((q : ℝ) ^ l + 1) -
      ((Fintype.card E : ℝ) - Fintype.card V) * (1 + (-1) ^ l) : ℝ) : ℂ) =
      ∑ i ∈ Finset.univ.erase i₀, (α i ^ l + β i ^ l) := by
    push_cast
    rw [htr, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), htriv, Nat.cast_sub hVE]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hrem]
  calc ‖∑ i ∈ Finset.univ.erase i₀, (α i ^ l + β i ^ l)‖
      ≤ ∑ i ∈ Finset.univ.erase i₀, ‖α i ^ l + β i ^ l‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.univ.erase i₀, 2 * Real.sqrt q ^ l := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨h1, h2⟩ := hnorm i (Finset.ne_of_mem_erase hi)
        calc ‖α i ^ l + β i ^ l‖ ≤ ‖α i ^ l‖ + ‖β i ^ l‖ := norm_add_le _ _
          _ = 2 * Real.sqrt q ^ l := by
              rw [norm_pow, norm_pow, h1, h2]
              ring
    _ = 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ l := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          nsmul_eq_mul, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨i₀⟩), Nat.cast_one]
        ring

/-- [proved-derived; formal-checked] The same bound with the count of contacts read from the
complex: `1 ≤ q` gives `|V| ≤ |E|`. -/
theorem walkCount_bound_of_one_le {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hq : 1 ≤ q) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (l : ℕ) :
    |walkCount a b l - ((q : ℝ) ^ l + 1) -
        ((Fintype.card E : ℝ) - Fintype.card V) * (1 + (-1) ^ l)| ≤
      2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ l :=
  walkCount_bound a b hreg (card_le_card_of_regular a b hreg hq) h0 htemp l

/-! ## Z6. The bound is the half: a cell outside the gap -/

/-- [proved-derived; formal-checked] **A cell outside the gap is louder than the half.**  For
`0 < q` and `4q < λ²` the cell `X² − λ X + q` has real roots `r`, `s` with `r + s = λ`, `r s = q`,
and at every even length `2k ≥ 2` its contribution alone exceeds a tempered cell's bound:
`2 (√q)^(2k) < r^(2k) + s^(2k)`. -/
theorem cell_contribution_exceeds {lam q : ℝ} (hq : 0 < q) (h : 4 * q < lam ^ 2) :
    ∃ r s : ℝ, r + s = lam ∧ r * s = q ∧
      ∀ k : ℕ, 1 ≤ k → 2 * Real.sqrt q ^ (2 * k) < r ^ (2 * k) + s ^ (2 * k) := by
  have hd : 0 < lam ^ 2 - 4 * q := by linarith
  set d := Real.sqrt (lam ^ 2 - 4 * q) with hd_def
  have hdsq : d ^ 2 = lam ^ 2 - 4 * q := Real.sq_sqrt hd.le
  have hdpos : 0 < d := Real.sqrt_pos.mpr hd
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0] at h
    nlinarith
  refine ⟨(lam + d) / 2, (lam - d) / 2, by ring, by nlinarith, ?_⟩
  intro k hk
  set r := (lam + d) / 2 with hr
  set s := (lam - d) / 2 with hs
  have hrs : r * s = q := by
    rw [hr, hs]
    nlinarith
  have hsq : Real.sqrt q ^ (2 * k) = (r * s) ^ k := by
    rw [pow_mul, Real.sq_sqrt hq.le, hrs]
  have hne : r ^ k ≠ s ^ k := by
    intro heq
    have habs : |r| ^ k = |s| ^ k := by rw [← abs_pow, ← abs_pow, heq]
    have habs' : |r| = |s| :=
      (pow_left_inj₀ (abs_nonneg r) (abs_nonneg s) (by omega : k ≠ 0)).mp habs
    rcases abs_eq_abs.mp habs' with h1 | h1
    · have : d = 0 := by
        rw [hr, hs] at h1
        linarith
      exact hdpos.ne' this
    · have : lam = 0 := by
        rw [hr, hs] at h1
        linarith
      exact hlam this
  have hpos : 0 < (r ^ k - s ^ k) ^ 2 := by
    have : r ^ k - s ^ k ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have e1 : r ^ (2 * k) = (r ^ k) ^ 2 := by rw [mul_comm, pow_mul]
  have e2 : s ^ (2 * k) = (s ^ k) ^ 2 := by rw [mul_comm, pow_mul]
  rw [hsq, mul_pow, e1, e2]
  nlinarith [hpos]

section Audit

#print axioms trace_pow_eq_sum_roots_charpoly
#print axioms det_smul_one_sub_smul
#print axioms adjacency_charpoly_complex
#print axioms exists_eigen_eq_count
#print axioms det_cell
#print axioms ihara_bass_spectral
#print axioms det_hashimoto_eq_zero_iff_cell
#print axioms zeros_tempered
#print axioms exists_real_zero_off_circle
#print axioms card_le_card_of_regular
#print axioms hashimoto_charpoly
#print axioms hashimoto_charpoly_linear
#print axioms trace_hashimoto_pow
#print axioms walkCount_cast
#print axioms walkCount_bound
#print axioms walkCount_bound_of_one_le
#print axioms cell_contribution_exceeds

end Audit

end Holonics.Landmarks.RegularComplexZeros
