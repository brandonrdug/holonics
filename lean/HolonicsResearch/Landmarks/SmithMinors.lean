import HolonicsResearch.Landmarks.ClosureKeyTorsion
import HolonicsResearch.Landmarks.SmithCokernel

/-!
# Smith minors: Cauchy–Binet, and the rank falls at the primes of the invariants' product

[proved-standard; formal-checked] Formal obligations (#410), the box "The closure key's torsion (#405)", its owed
clause: the Smith-invariant form of `Landmarks/ClosureKeyTorsion`'s item 2. Sources: the box; the record of
October 25 on the newline closure (`research/records/2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_PLUS_ONE_*`,
§§2, 5); atlas `hnn.tower-ring-closure` (`p` is torsion iff `rank_p < rank_ℚ` iff `p` divides every maximal minor)
and `linalg.smith-normal-form`; `Landmarks/ClosureKeyTorsion` (`ratRank`, `modRank`, `modRank_lt_ratRank_iff`,
`finrank_ker_lt_iff`) and `Landmarks/SmithCokernel` (Mathlib's Smith form of an integral image, `smith`).

A `k × k` minor of `A : Matrix m o R` is `det A[f, g]` for any `f : Fin k → m` and `g : Fin k → o`, the indexing of
`ClosureKeyTorsion`: a repeated row or column reads `0`, a reordering a sign. A maximal minor of an integer system
is a `rank_ℚ × rank_ℚ` minor, as there.

What is proved.

1. **Cauchy–Binet** (`det_mul_eq_sum_fun`, `cauchyBinet`). For `A : Matrix (Fin k) n R` and `B : Matrix n (Fin k) R`
   over a commutative ring, `det (A B)` expands by multilinearity in the rows as `Σ_φ (Π_i A i (φ i)) det B[φ, ·]`
   over every `φ : Fin k → n`. A term with `φ` not injective vanishes (`det_submatrix_eq_zero_of_not_injective`),
   and an injective `φ` is one sorted embedding of its image after one permutation, so
   `det (A B) = Σ_S det A[·, S] · det B[S, ·]` over the `k`-subsets `S` of `n`, each read through
   `S.orderEmbOfFin`. Every `k × k` minor of a product is that sum over the inner index (`det_submatrix_mul`).
2. **Minors under a unimodular change.** An element dividing every `k × k` minor of `A` divides every `k × k` minor
   of `U A` and of `A V`, for any `U` and `V` (`dvd_minor_mul_left`, `dvd_minor_mul_right`). So where `A = X C` and
   `X = A W` (`dvd_minors_iff_of_right_factor`), or `A = P X` and `X = Q A` (`dvd_minors_iff_of_left_factor`), the
   two systems have the same divisors of their `k × k` minors, and with `IsUnit (det U)` and `IsUnit (det V)` so do
   `U A V` and `A` (`dvd_minors_unimodular_iff`). Read at `c = 0`, every `k × k` minor vanishes for both or for
   neither, so the rank over ℚ is shared (`ratRank_eq_of_minors_eq_zero_iff`, `ratRank_unimodular`).
3. **The diagonal case.** `rectDiag m k r d` holds `d i` at `(i, i)` for `i < r` and `0` elsewhere. Each of its
   minors is a `0/1` incidence times the diagonal of the columns it reads (`rectDiag_submatrix`): the `r × r` minor
   on the leading rows and columns is `Π_(i<r) d i` (`minor_leading`), every `r × r` minor is a multiple of it
   (`prod_dvd_minor`), and every larger minor is `0` (`minor_eq_zero_of_lt`). So `c` divides every `r × r` minor iff
   `c ∣ Π_(i<r) d i` (`dvd_minors_rectDiag_iff`), and with each `d i ≠ 0` the rank over ℚ is `r`
   (`ratRank_rectDiag`). `embDiag e a`, the diagonal `a` placed on an embedding `e` of the columns into the rows, is
   read the same way (`prod_dvd_minor_embDiag`, `minor_embDiag_self`, `dvd_minors_embDiag_iff`, `ratRank_embDiag`).
4. **The Smith-invariant form.** For `A = U D V` over ℤ with `U`, `V` unimodular and `D = rectDiag m k r d`, each
   `d i ≠ 0` (any diagonal form: no divisibility chain is used), `rank_ℚ A = r` (`ratRank_smith`); `c` divides every
   `r × r` minor iff `c ∣ Π d i` (`dvd_maxMinors_smith_iff`); the gcd of the `r × r` minors is `|Π d i|`
   (`gcd_maxMinors_smith`, through `gcd_minors_eq_abs`); a prime `p` drops the rank iff `p ∣ Π d i`
   (`modRank_lt_ratRank_smith_iff`), iff the kernel modulo `p` is wider than the rational kernel
   (`finrank_ker_lt_smith_iff`).
5. **Mathlib's Smith form.** For `A : Matrix (Fin m) (Fin k) ℤ` and any `Basis.SmithNormalForm` of the range of
   `A.mulVecLin` (bases `bM` and `bN`, embedding `f`, entries `a`), `A` factors through the columns of `bN` with a
   section (`eq_imageCols_mul_coords`, `imageCols_eq_mul_sectionCols`), and those columns are `bM`'s columns times
   the diagonal `a` on `f` (`imageCols_eq_basisCols_mul`), `bM`'s columns inverted by `bM.toMatrix` of the
   standard basis (`flip_mul_basisCols`). So `rank_ℚ A = n` (`ratRank_eq_of_smith`), `c` divides every `n × n`
   minor iff `c ∣ Π a i` (`dvd_maxMinors_of_smith_iff`), the gcd of the maximal minors is `|Π a i|`
   (`gcd_maxMinors_of_smith`), and `p` drops the rank iff `p ∣ Π a i` (`modRank_lt_ratRank_of_smith_iff`,
   `finrank_ker_lt_of_smith_iff`). On `SmithCokernel.smith A.mulVecLin`, whose nonzero invariants multiply to
   `Π a i` (`prod_a_eq_prod_invariant`, through `SmithCokernel.invariant_f` and `invariant_eq_zero_iff`): `rank_ℚ A`
   is its rank
   (`ratRank_eq_smith_rank`), **`p` drops the rank iff it divides the product of the nonzero invariants**
   (`modRank_lt_ratRank_iff_smith`), and the maximal minors' gcd is that product's absolute value
   (`gcd_maxMinors_smith_eq`).

What is not claimed.
- The divisibility chain `d₁ ∣ d₂ ∣ ⋯` and the uniqueness of the invariants up to units: nothing here uses them,
  and Mathlib's form carries no chain. The determinantal divisors of the smaller sizes (the gcd of the `j × j`
  minors as `Π_(i<j) d i`) need the chain and are not stated; only the maximal size is.
- That every integer system has a factorization `A = U D V` with `D` on the leading diagonal: item 4 takes one as
  given. Item 5 reads Mathlib's form, which Mathlib constructs for a submodule of a finite free module over a
  principal ideal domain (`Submodule.smithNormalForm`), its diagonal on the embedding `f`.
- The reduction of the rational kernel as a subspace: as in `ClosureKeyTorsion`, the kernels are compared by width.

The computational object is the helical pair interaction read on a closure's menu. The loop-closure rows, each
counting the (seam, arriving class) pair contacts on a loop between two arrivals of the origin, form an integer
system whose torsion the invariants carry: a prime at which the system's rank falls, so that the kernel modulo the
prime, where the closure's keys are read, is wider than the rational kernel, is a prime dividing the product of the
system's nonzero Smith invariants, which is the gcd of its maximal minors; Cauchy–Binet is why a unimodular change
of the rows or of the pair coordinates leaves that gcd as it was. Of the winding guide's six general objects this
touches the pair (the contacts whose counts are the rows), the helix (a ring of prime period on which the loops
close) and faces and placement (a minor as a face of the system on chosen rows and columns, the sorted subsets as
its placements); the cell holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix Module

namespace Holonics.Landmarks.SmithMinors

open Holonics.Landmarks.ClosureKeyTorsion

/-! ## 1. Cauchy–Binet -/

section CauchyBinet

variable {R : Type*} [CommRing R] {n : Type*} {k : ℕ}

/-- [proved-standard; formal-checked] `det (A B)` by multilinearity in the rows: a sum over every `φ : Fin k → n`. -/
theorem det_mul_eq_sum_fun [Fintype n] (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) :
    (A * B).det = ∑ φ : Fin k → n, (∏ i, A i (φ i)) * (B.submatrix φ id).det := by
  have h : (A * B : Matrix (Fin k) (Fin k) R) = fun i => ∑ j, A i j • B j := by
    ext i l
    simp [Matrix.mul_apply, Finset.sum_apply]
  have hs := (detRowAlternating : (Fin k → R) [⋀^Fin k]→ₗ[R] R).toMultilinearMap.map_sum
    (fun i j => A i j • B j)
  simp only [AlternatingMap.coe_multilinearMap] at hs
  rw [det, h, hs]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [AlternatingMap.map_smul_univ, smul_eq_mul]
  rfl

/-- [proved-standard; formal-checked] Rows read through a non-injective `φ` repeat, so their determinant is `0`. -/
theorem det_submatrix_eq_zero_of_not_injective (B : Matrix n (Fin k) R) {φ : Fin k → n}
    (hφ : ¬ Function.Injective φ) : (B.submatrix φ id).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, φ i = φ j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hφ
    obtain ⟨i, j, h, hne⟩ := hφ
    exact ⟨i, j, h, hne⟩
  exact det_zero_of_row_eq hne (by ext l; simp [hij])

/-- [proved-standard; formal-checked] **Cauchy–Binet**: `det (A B) = Σ_S det A[·, S] · det B[S, ·]`, `|S| = k`. -/
theorem cauchyBinet [Fintype n] [LinearOrder n] (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) :
    (A * B).det = ∑ S : {S : Finset n // S.card = k},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  set F : (Fin k → n) → R := fun φ => (∏ i, A i (φ i)) * (B.submatrix φ id).det with hF
  have hR : ∀ S : {S : Finset n // S.card = k},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det =
        ∑ σ : Equiv.Perm (Fin k), F ((S.1.orderEmbOfFin S.2) ∘ σ) := by
    intro S
    rw [← det_transpose, det_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hB : B.submatrix ((S.1.orderEmbOfFin S.2) ∘ σ) id =
        (B.submatrix (S.1.orderEmbOfFin S.2) id).submatrix σ id := rfl
    rw [hF]
    dsimp only
    rw [hB, det_permute, Units.smul_def, zsmul_eq_mul]
    simp only [transpose_apply, submatrix_apply, id_eq, Function.comp_apply]
    ring
  rw [det_mul_eq_sum_fun, Finset.sum_congr rfl fun S _ => hR S, ← Fintype.sum_prod_type',
    ← Finset.sum_filter_of_ne (p := Function.Injective)
      (fun φ _ hφ => by_contra fun h => hφ (by simp [det_submatrix_eq_zero_of_not_injective B h]))]
  symm
  refine Finset.sum_bij (fun p _ => (p.1.1.orderEmbOfFin p.1.2 : Fin k → n) ∘ p.2) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (EmbeddingLike.injective _).comp p.2.injective
  · rintro ⟨S, σ⟩ _ ⟨T, τ⟩ _ h
    have hST : S = T := by
      apply Subtype.ext
      apply Finset.coe_injective
      dsimp only at h
      have h1 := congrArg Set.range h
      simp only [EquivLike.range_comp, Finset.range_orderEmbOfFin] at h1
      exact h1
    subst hST
    have hστ : σ = τ := by
      ext i
      exact congrArg Fin.val ((EmbeddingLike.injective _) (congrFun h i))
    rw [hστ]
  · intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    have hS : (Finset.univ.image φ).card = k := by
      rw [Finset.card_image_of_injective _ hφ, Finset.card_univ, Fintype.card_fin]
    set e := (Finset.univ.image φ).orderEmbOfFin hS with he
    have hmem : ∀ i, ∃ j, e j = φ i := by
      intro i
      have : φ i ∈ Set.range e := by
        rw [he, Finset.range_orderEmbOfFin]
        simp
      exact this
    choose σ' hσ' using hmem
    have hinj : Function.Injective σ' := fun i i' h => hφ (by rw [← hσ', ← hσ', h])
    have hbij : Function.Bijective σ' := Finite.injective_iff_bijective.mp hinj
    refine ⟨(⟨Finset.univ.image φ, hS⟩, Equiv.ofBijective σ' hbij), Finset.mem_univ _, ?_⟩
    funext i
    exact hσ' i
  · intro p _
    rfl

/-- [proved-standard; formal-checked] Every `k × k` minor of `A B` is Cauchy–Binet's sum over the inner index. -/
theorem det_submatrix_mul {l m o : Type*} [Fintype l] [LinearOrder l] (A : Matrix m l R)
    (B : Matrix l o R) (f : Fin k → m) (g : Fin k → o) :
    ((A * B).submatrix f g).det = ∑ S : {S : Finset l // S.card = k},
      (A.submatrix f (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) g).det := by
  rw [submatrix_mul A B f id g Function.bijective_id]
  exact cauchyBinet (A.submatrix f id) (B.submatrix id g)

end CauchyBinet

/-! ## 2. Minors under a unimodular change -/

section Unimodular

variable {R : Type*} [CommRing R] {k : ℕ}

/-- [proved-standard; formal-checked] A common divisor of the `k × k` minors of `A` divides those of `U A`. -/
theorem dvd_minor_mul_left {l m o : Type*} [Fintype m] (U : Matrix l m R) (A : Matrix m o R) (c : R)
    (h : ∀ (f : Fin k → m) (g : Fin k → o), c ∣ (A.submatrix f g).det) (f : Fin k → l)
    (g : Fin k → o) : c ∣ ((U * A).submatrix f g).det := by
  let _ : LinearOrder m := LinearOrder.lift' (Fintype.equivFin m) (Fintype.equivFin m).injective
  rw [det_submatrix_mul]
  exact Finset.dvd_sum fun S _ => Dvd.dvd.mul_left (h _ _) _

/-- [proved-standard; formal-checked] A common divisor of the `k × k` minors of `A` divides those of `A V`. -/
theorem dvd_minor_mul_right {l m o : Type*} [Fintype o] (A : Matrix l o R) (V : Matrix o m R) (c : R)
    (h : ∀ (f : Fin k → l) (g : Fin k → o), c ∣ (A.submatrix f g).det) (f : Fin k → l)
    (g : Fin k → m) : c ∣ ((A * V).submatrix f g).det := by
  let _ : LinearOrder o := LinearOrder.lift' (Fintype.equivFin o) (Fintype.equivFin o).injective
  rw [det_submatrix_mul]
  exact Finset.dvd_sum fun S _ => Dvd.dvd.mul_right (h _ _) _

/-- [proved-standard; formal-checked] Where `A = X C` and `X = A W`, `A` and `X` share the divisors of their minors. -/
theorem dvd_minors_iff_of_right_factor {l m o : Type*} [Fintype l] [Fintype o] (A : Matrix m o R)
    (X : Matrix m l R) (C : Matrix l o R) (W : Matrix o l R) (hA : A = X * C) (hX : X = A * W) (c : R) :
    (∀ (f : Fin k → m) (g : Fin k → o), c ∣ (A.submatrix f g).det) ↔
      ∀ (f : Fin k → m) (g : Fin k → l), c ∣ (X.submatrix f g).det := by
  constructor
  · intro h f g
    rw [hX]
    exact dvd_minor_mul_right A W c h f g
  · intro h f g
    rw [hA]
    exact dvd_minor_mul_right X C c h f g

/-- [proved-standard; formal-checked] Where `A = P X` and `X = Q A`, `A` and `X` share the divisors of their minors. -/
theorem dvd_minors_iff_of_left_factor {l m o : Type*} [Fintype l] [Fintype m] (A : Matrix m o R)
    (X : Matrix l o R) (P : Matrix m l R) (Q : Matrix l m R) (hA : A = P * X) (hX : X = Q * A) (c : R) :
    (∀ (f : Fin k → m) (g : Fin k → o), c ∣ (A.submatrix f g).det) ↔
      ∀ (f : Fin k → l) (g : Fin k → o), c ∣ (X.submatrix f g).det := by
  constructor
  · intro h f g
    rw [hX]
    exact dvd_minor_mul_left Q A c h f g
  · intro h f g
    rw [hA]
    exact dvd_minor_mul_left P X c h f g

/-- [proved-standard; formal-checked] For `U`, `V` unimodular, `U A V` and `A` share the divisors of their minors. -/
theorem dvd_minors_unimodular_iff {m o : Type*} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]
    (U : Matrix m m R) (A : Matrix m o R) (V : Matrix o o R) (hU : IsUnit U.det) (hV : IsUnit V.det)
    (c : R) :
    (∀ (f : Fin k → m) (g : Fin k → o), c ∣ ((U * A * V).submatrix f g).det) ↔
      ∀ (f : Fin k → m) (g : Fin k → o), c ∣ (A.submatrix f g).det := by
  rw [dvd_minors_iff_of_right_factor (U * A * V) (U * A) V V⁻¹ rfl
      (by rw [Matrix.mul_assoc, mul_nonsing_inv V hV, Matrix.mul_one]),
    dvd_minors_iff_of_left_factor (U * A) A U U⁻¹ rfl
      (by rw [← Matrix.mul_assoc, nonsing_inv_mul U hU, Matrix.one_mul])]

end Unimodular

section Rank

variable {m o m' o' : Type*} [Fintype m] [Fintype o] [Fintype m'] [Fintype o']

/-- [proved-standard; formal-checked] Two integer systems whose minors of each size vanish together share `rank_ℚ`. -/
theorem ratRank_eq_of_minors_eq_zero_iff (A : Matrix m o ℤ) (B : Matrix m' o' ℤ)
    (h : ∀ s : ℕ, (∀ (f : Fin s → m) (g : Fin s → o), (A.submatrix f g).det = 0) ↔
      ∀ (f : Fin s → m') (g : Fin s → o'), (B.submatrix f g).det = 0) :
    ratRank A = ratRank B := by
  have key : ∀ s, s ≤ ratRank A ↔ s ≤ ratRank B := by
    intro s
    rw [le_ratRank_iff, le_ratRank_iff]
    constructor
    · rintro ⟨f, g, hfg⟩
      by_contra hcon
      push Not at hcon
      exact hfg ((h s).mpr hcon f g)
    · rintro ⟨f, g, hfg⟩
      by_contra hcon
      push Not at hcon
      exact hfg ((h s).mp hcon f g)
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

/-- [proved-standard; formal-checked] A unimodular change of rows and columns keeps the rank over ℚ. -/
theorem ratRank_unimodular [DecidableEq m] [DecidableEq o] (U : Matrix m m ℤ) (A : Matrix m o ℤ)
    (V : Matrix o o ℤ) (hU : IsUnit U.det) (hV : IsUnit V.det) : ratRank (U * A * V) = ratRank A :=
  ratRank_eq_of_minors_eq_zero_iff _ _ fun s => by
    simpa only [zero_dvd_iff] using dvd_minors_unimodular_iff (k := s) U A V hU hV 0

/-- [proved-standard; formal-checked] Where the divisors of the `s × s` minors are those of `P`, their gcd is `|P|`. -/
theorem gcd_minors_eq_abs [DecidableEq m] [DecidableEq o] (A : Matrix m o ℤ) (s : ℕ) (P : ℤ)
    (h : ∀ c : ℤ, (∀ (f : Fin s → m) (g : Fin s → o), c ∣ (A.submatrix f g).det) ↔ c ∣ P) :
    Finset.univ.gcd (fun fg : (Fin s → m) × (Fin s → o) => (A.submatrix fg.1 fg.2).det) = |P| := by
  have key : ∀ c : ℤ, c ∣ Finset.univ.gcd
      (fun fg : (Fin s → m) × (Fin s → o) => (A.submatrix fg.1 fg.2).det) ↔ c ∣ P := by
    intro c
    rw [Finset.dvd_gcd_iff, ← h]
    simp only [Finset.mem_univ, true_implies, Prod.forall]
  rw [Int.abs_eq_normalize]
  exact dvd_antisymm_of_normalize_eq Finset.normalize_gcd (normalize_idem P)
    (dvd_normalize_iff.mpr ((key _).mp dvd_rfl)) ((key _).mpr (normalize_dvd_iff.mpr dvd_rfl))

end Rank

/-! ## 3. The diagonal case -/

section Diagonal

variable {R : Type*} [CommRing R]

/-- [definition] The `0/1` incidence of two index maps: `1` where `u x = v i`. -/
def incidence {α : Type*} [DecidableEq α] {s : ℕ} (u v : Fin s → α) : Matrix (Fin s) (Fin s) R :=
  Matrix.of fun x i => if u x = v i then 1 else 0

/-- [proved-standard; formal-checked] Where `v` repeats a value, the incidence has two equal columns: `det = 0`. -/
theorem det_incidence_eq_zero {α : Type*} [DecidableEq α] {s : ℕ} (u : Fin s → α) {v : Fin s → α}
    (hv : ¬ Function.Injective v) : (incidence u v : Matrix (Fin s) (Fin s) R).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, v i = v j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hv
    obtain ⟨i, j, h, hne⟩ := hv
    exact ⟨i, j, h, hne⟩
  exact det_zero_of_column_eq hne fun x => by simp [incidence, hij]

/-- [definition] The rectangular diagonal: `d i` at `(i, i)` for `i < r`, `0` elsewhere. -/
def rectDiag (m k r : ℕ) (d : ℕ → R) : Matrix (Fin m) (Fin k) R :=
  Matrix.of fun i j => if (i : ℕ) = j ∧ (i : ℕ) < r then d i else 0

/-- [definition] The diagonal cut at `r`: `d j` for `j < r`, `0` from `r` on. -/
def cut (r : ℕ) (d : ℕ → R) (j : ℕ) : R := if j < r then d j else 0

/-- [proved-standard; formal-checked] A minor of `rectDiag` is an incidence times the diagonal of its columns. -/
theorem rectDiag_submatrix {m k r s : ℕ} (d : ℕ → R) (f : Fin s → Fin m) (g : Fin s → Fin k) :
    (rectDiag m k r d).submatrix f g =
      incidence (fun x => (f x : ℕ)) (fun i => (g i : ℕ)) * diagonal fun i => cut r d (g i) := by
  ext x i
  simp only [rectDiag, incidence, cut, submatrix_apply, of_apply, mul_diagonal]
  by_cases h : (f x : ℕ) = g i
  · simp [h]
  · simp [h]

/-- [proved-standard; formal-checked] Its determinant is the incidence's times the product of the cut diagonal. -/
theorem det_rectDiag_submatrix {m k r s : ℕ} (d : ℕ → R) (f : Fin s → Fin m) (g : Fin s → Fin k) :
    ((rectDiag m k r d).submatrix f g).det =
      (incidence (fun x => (f x : ℕ)) (fun i => (g i : ℕ)) : Matrix (Fin s) (Fin s) R).det *
        ∏ i, cut r d (g i) := by
  rw [rectDiag_submatrix, det_mul, det_diagonal]

/-- [proved-standard; formal-checked] On distinct columns below `r`, the cut diagonal's product is `Π_(j<r) d j`. -/
theorem prod_cut_eq {k r : ℕ} (d : ℕ → R) {g : Fin r → Fin k} (hg : Function.Injective g)
    (hlt : ∀ i, (g i : ℕ) < r) : ∏ i, cut r d (g i) = ∏ j ∈ Finset.range r, d j := by
  have hinj : Function.Injective fun i => (g i : ℕ) := fun i j h => hg (Fin.ext h)
  have himg : Finset.univ.image (fun i => (g i : ℕ)) = Finset.range r := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
      obtain ⟨i, rfl⟩ := hj
      exact Finset.mem_range.mpr (hlt i)
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_range, Finset.card_univ, Fintype.card_fin]
  rw [← himg, Finset.prod_image fun i _ j _ h => hinj h]
  exact Finset.prod_congr rfl fun i _ => if_pos (hlt i)

/-- [proved-standard; formal-checked] Every `r × r` minor of `rectDiag` is a multiple of `Π_(j<r) d j`. -/
theorem prod_dvd_minor {m k r : ℕ} (d : ℕ → R) (f : Fin r → Fin m) (g : Fin r → Fin k) :
    (∏ j ∈ Finset.range r, d j) ∣ ((rectDiag m k r d).submatrix f g).det := by
  rw [det_rectDiag_submatrix]
  by_cases hg : Function.Injective g
  · by_cases hlt : ∀ i, (g i : ℕ) < r
    · rw [prod_cut_eq d hg hlt]
      exact dvd_mul_left _ _
    · push Not at hlt
      obtain ⟨i, hi⟩ := hlt
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (not_lt.mpr hi)), mul_zero]
      exact dvd_zero _
  · rw [det_incidence_eq_zero _ fun h => hg fun i j hij => h (congrArg Fin.val hij), zero_mul]
    exact dvd_zero _

/-- [proved-standard; formal-checked] Every minor of `rectDiag` larger than `r × r` is `0`. -/
theorem minor_eq_zero_of_lt {m k r s : ℕ} (d : ℕ → R) (hrs : r < s) (f : Fin s → Fin m)
    (g : Fin s → Fin k) : ((rectDiag m k r d).submatrix f g).det = 0 := by
  rw [det_rectDiag_submatrix]
  by_cases hg : Function.Injective g
  · have : ∃ i, r ≤ (g i : ℕ) := by
      by_contra hcon
      push Not at hcon
      have hinj : Function.Injective fun i => (⟨g i, hcon i⟩ : Fin r) :=
        fun i j h => hg (Fin.ext (by simpa using congrArg Fin.val h))
      have := Fintype.card_le_of_injective _ hinj
      simp only [Fintype.card_fin] at this
      omega
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (not_lt.mpr hi)), mul_zero]
  · rw [det_incidence_eq_zero _ fun h => hg fun i j hij => h (congrArg Fin.val hij), zero_mul]

/-- [proved-standard; formal-checked] The leading `r × r` minor of `rectDiag` is `Π_(j<r) d j`. -/
theorem minor_leading {m k r : ℕ} (d : ℕ → R) (hm : r ≤ m) (hk : r ≤ k) :
    ((rectDiag m k r d).submatrix (Fin.castLE hm) (Fin.castLE hk)).det = ∏ j ∈ Finset.range r, d j := by
  have h : (rectDiag m k r d).submatrix (Fin.castLE hm) (Fin.castLE hk) = diagonal fun i : Fin r => d i := by
    ext i j
    simp only [rectDiag, submatrix_apply, of_apply, Fin.val_castLE, diagonal_apply, Fin.ext_iff]
    by_cases h : (i : ℕ) = j
    · simp [h, j.2]
    · simp [h]
  rw [h, det_diagonal, Fin.prod_univ_eq_prod_range (fun j => d j) r]

/-- [proved-standard; formal-checked] `c` divides every `r × r` minor of `rectDiag` iff `c ∣ Π_(j<r) d j`. -/
theorem dvd_minors_rectDiag_iff {m k r : ℕ} (d : ℕ → R) (hm : r ≤ m) (hk : r ≤ k) (c : R) :
    (∀ (f : Fin r → Fin m) (g : Fin r → Fin k), c ∣ ((rectDiag m k r d).submatrix f g).det) ↔
      c ∣ ∏ j ∈ Finset.range r, d j :=
  ⟨fun h => minor_leading d hm hk ▸ h _ _, fun h f g => h.trans (prod_dvd_minor d f g)⟩

/-- [definition] The diagonal `a` placed on an embedding `e` of the columns into the rows. -/
def embDiag {ι : Type*} [DecidableEq ι] {n : ℕ} (e : Fin n ↪ ι) (a : Fin n → R) : Matrix ι (Fin n) R :=
  Matrix.of fun x i => if x = e i then a i else 0

/-- [proved-standard; formal-checked] A square minor of `embDiag` is an incidence times the diagonal it reads. -/
theorem embDiag_submatrix {ι : Type*} [DecidableEq ι] {n : ℕ} (e : Fin n ↪ ι) (a : Fin n → R)
    (u : Fin n → ι) (v : Fin n → Fin n) :
    (embDiag e a).submatrix u v = incidence u (e ∘ v) * diagonal fun i => a (v i) := by
  ext x i
  simp only [embDiag, incidence, submatrix_apply, of_apply, mul_diagonal, Function.comp_apply]
  by_cases h : u x = e (v i)
  · simp [h]
  · simp [h]

/-- [proved-standard; formal-checked] Every `n × n` minor of `embDiag e a` is a multiple of `Π a i`. -/
theorem prod_dvd_minor_embDiag {ι : Type*} [DecidableEq ι] {n : ℕ} (e : Fin n ↪ ι) (a : Fin n → R)
    (u : Fin n → ι) (v : Fin n → Fin n) : (∏ i, a i) ∣ ((embDiag e a).submatrix u v).det := by
  rw [embDiag_submatrix, det_mul, det_diagonal]
  by_cases hv : Function.Injective v
  · rw [Fintype.prod_bijective v (Finite.injective_iff_bijective.mp hv) (fun i => a (v i)) a fun _ => rfl]
    exact dvd_mul_left _ _
  · rw [det_incidence_eq_zero u fun h => hv h.of_comp, zero_mul]
    exact dvd_zero _

/-- [proved-standard; formal-checked] The `n × n` minor of `embDiag e a` on the rows `e` is `Π a i`. -/
theorem minor_embDiag_self {ι : Type*} [DecidableEq ι] {n : ℕ} (e : Fin n ↪ ι) (a : Fin n → R) :
    ((embDiag e a).submatrix e id).det = ∏ i, a i := by
  have h : (embDiag e a).submatrix e id = diagonal a := by
    ext x i
    simp only [embDiag, submatrix_apply, of_apply, id_eq, diagonal_apply, e.injective.eq_iff]
    by_cases hxi : x = i
    · simp [hxi]
    · simp [hxi]
  rw [h, det_diagonal]

/-- [proved-standard; formal-checked] `c` divides every `n × n` minor of `embDiag e a` iff `c ∣ Π a i`. -/
theorem dvd_minors_embDiag_iff {ι : Type*} [DecidableEq ι] {n : ℕ} (e : Fin n ↪ ι) (a : Fin n → R) (c : R) :
    (∀ (u : Fin n → ι) (v : Fin n → Fin n), c ∣ ((embDiag e a).submatrix u v).det) ↔ c ∣ ∏ i, a i :=
  ⟨fun h => minor_embDiag_self e a ▸ h _ _, fun h u v => h.trans (prod_dvd_minor_embDiag e a u v)⟩

/-- [proved-standard; formal-checked] With each `d i ≠ 0` for `i < r`, `rectDiag m k r d` has rank `r` over ℚ. -/
theorem ratRank_rectDiag {m k r : ℕ} (d : ℕ → ℤ) (hm : r ≤ m) (hk : r ≤ k) (hd : ∀ j < r, d j ≠ 0) :
    ratRank (rectDiag m k r d) = r := by
  apply le_antisymm
  · by_contra h
    push Not at h
    obtain ⟨f, g, hfg⟩ := (le_ratRank_iff _).mp (Nat.succ_le_of_lt h)
    exact hfg (minor_eq_zero_of_lt d (Nat.lt_succ_self r) f g)
  · refine (le_ratRank_iff _).mpr ⟨Fin.castLE hm, Fin.castLE hk, ?_⟩
    rw [minor_leading d hm hk]
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hd j (Finset.mem_range.mp hj)

/-- [proved-standard; formal-checked] With each `a i ≠ 0`, `embDiag e a` has rank `n` over ℚ. -/
theorem ratRank_embDiag {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : Fin n ↪ ι) (a : Fin n → ℤ)
    (ha : ∀ i, a i ≠ 0) : ratRank (embDiag e a) = n := by
  apply le_antisymm
  · have := rank_le_card_width ((embDiag e a).map (Int.cast : ℤ → ℚ))
    rwa [Fintype.card_fin] at this
  · refine (le_ratRank_iff _).mpr ⟨e, id, ?_⟩
    rw [minor_embDiag_self]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i

end Diagonal

/-! ## 4. The Smith-invariant form -/

section Smith

variable {m k r : ℕ} (U : Matrix (Fin m) (Fin m) ℤ) (V : Matrix (Fin k) (Fin k) ℤ) (d : ℕ → ℤ)

/-- [proved-standard; formal-checked] `A = U D V`, `U`, `V` unimodular, `D` diagonal of rank `r`: `rank_ℚ A = r`. -/
theorem ratRank_smith (hU : IsUnit U.det) (hV : IsUnit V.det) (hm : r ≤ m) (hk : r ≤ k)
    (hd : ∀ j < r, d j ≠ 0) : ratRank (U * rectDiag m k r d * V) = r := by
  rw [ratRank_unimodular U _ V hU hV, ratRank_rectDiag d hm hk hd]

/-- [proved-standard; formal-checked] `c` divides every `r × r` minor of `U D V` iff `c ∣ Π_(i<r) d i`. -/
theorem dvd_maxMinors_smith_iff (hU : IsUnit U.det) (hV : IsUnit V.det) (hm : r ≤ m) (hk : r ≤ k) (c : ℤ) :
    (∀ (f : Fin r → Fin m) (g : Fin r → Fin k), c ∣ ((U * rectDiag m k r d * V).submatrix f g).det) ↔
      c ∣ ∏ j ∈ Finset.range r, d j := by
  rw [dvd_minors_unimodular_iff U _ V hU hV, dvd_minors_rectDiag_iff d hm hk]

/-- [proved-standard; formal-checked] The gcd of the `r × r` minors of `U D V` is `|Π_(i<r) d i|`. -/
theorem gcd_maxMinors_smith (hU : IsUnit U.det) (hV : IsUnit V.det) (hm : r ≤ m) (hk : r ≤ k) :
    Finset.univ.gcd (fun fg : (Fin r → Fin m) × (Fin r → Fin k) =>
      ((U * rectDiag m k r d * V).submatrix fg.1 fg.2).det) = |∏ j ∈ Finset.range r, d j| :=
  gcd_minors_eq_abs _ r _ (dvd_maxMinors_smith_iff U V d hU hV hm hk)

/-- [proved-standard; formal-checked] **A prime drops the rank of `U D V` iff it divides `Π_(i<r) d i`.** -/
theorem modRank_lt_ratRank_smith_iff (p : ℕ) [Fact p.Prime] (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hm : r ≤ m) (hk : r ≤ k) (hd : ∀ j < r, d j ≠ 0) :
    modRank p (U * rectDiag m k r d * V) < ratRank (U * rectDiag m k r d * V) ↔
      (p : ℤ) ∣ ∏ j ∈ Finset.range r, d j := by
  rw [modRank_lt_ratRank_iff, ratRank_smith U V d hU hV hm hk hd]
  exact dvd_maxMinors_smith_iff U V d hU hV hm hk _

/-- [proved-standard; formal-checked] The kernel of `U D V` modulo `p` is wider than over ℚ iff `p ∣ Π_(i<r) d i`. -/
theorem finrank_ker_lt_smith_iff (p : ℕ) [Fact p.Prime] (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hm : r ≤ m) (hk : r ≤ k) (hd : ∀ j < r, d j ≠ 0) :
    finrank ℚ (LinearMap.ker ((U * rectDiag m k r d * V).map (Int.cast : ℤ → ℚ)).mulVecLin) <
        finrank (ZMod p) (LinearMap.ker ((U * rectDiag m k r d * V).map (Int.cast : ℤ → ZMod p)).mulVecLin) ↔
      (p : ℤ) ∣ ∏ j ∈ Finset.range r, d j := by
  rw [finrank_ker_lt_iff, modRank_lt_ratRank_smith_iff U V d p hU hV hm hk hd]

end Smith

/-! ## 5. Mathlib's Smith form -/

section MathlibSmith

variable {m k n : ℕ} (A : Matrix (Fin m) (Fin k) ℤ)
  (snf : Basis.SmithNormalForm (LinearMap.range A.mulVecLin) (Fin m) n)

/-- [definition] The columns of the image basis `bN`. -/
noncomputable def imageCols : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun x i => (snf.bN i : Fin m → ℤ) x

/-- [definition] The columns of the ambient basis `bM`. -/
noncomputable def basisCols : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun x j => snf.bM j x

/-- [proved-standard; formal-checked] A column of `A` lies in its range. -/
theorem col_mem_range (j : Fin k) : A.col j ∈ LinearMap.range A.mulVecLin :=
  LinearMap.mem_range.mpr ⟨Pi.single j 1, by rw [mulVecLin_apply, mulVec_single_one]⟩

/-- [definition] The coordinates of `A`'s columns in the image basis `bN`. -/
noncomputable def coords : Matrix (Fin n) (Fin k) ℤ := Matrix.of fun i j => snf.bN.repr ⟨A.col j, col_mem_range A j⟩ i

/-- [definition] A section: for each `bN i`, a vector that `A` carries to it. -/
noncomputable def sectionCols : Matrix (Fin k) (Fin n) ℤ :=
  Matrix.of fun j i => (LinearMap.mem_range.mp (snf.bN i).2).choose j

/-- [proved-standard; formal-checked] `A` is the image basis's columns times their coordinates. -/
theorem eq_imageCols_mul_coords : A = imageCols A snf * coords A snf := by
  ext x j
  have h := congrArg (fun w : LinearMap.range A.mulVecLin => (w : Fin m → ℤ) x)
    (snf.bN.sum_repr ⟨A.col j, col_mem_range A j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [mul_apply]
  simp only [imageCols, coords, of_apply]
  exact h.symm.trans (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

/-- [proved-standard; formal-checked] The image basis's columns are `A` times the section. -/
theorem imageCols_eq_mul_sectionCols : imageCols A snf = A * sectionCols A snf := by
  ext x i
  have h := (LinearMap.mem_range.mp (snf.bN i).2).choose_spec
  rw [mulVecLin_apply] at h
  simp only [imageCols, sectionCols, of_apply, mul_apply]
  exact (congrFun h x).symm

/-- [proved-standard; formal-checked] The image basis's columns are `bM`'s columns times the diagonal `a` on `f`. -/
theorem imageCols_eq_basisCols_mul : imageCols A snf = basisCols A snf * embDiag snf.f snf.a := by
  ext x i
  simp only [imageCols, basisCols, embDiag, of_apply, mul_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [snf.snf i]
  simp [mul_comm]

/-- [proved-standard; formal-checked] `bM`'s columns are inverted by `bM.toMatrix` of the standard basis. -/
theorem flip_mul_basisCols : snf.bM.toMatrix (Pi.basisFun ℤ (Fin m)) * basisCols A snf = 1 := by
  have h : basisCols A snf = (Pi.basisFun ℤ (Fin m)).toMatrix snf.bM := by
    ext x j
    simp [basisCols, Basis.toMatrix_apply]
  rw [h, Basis.toMatrix_mul_toMatrix_flip]

/-- [proved-standard; formal-checked] `A` and Mathlib's diagonal on `f` share the divisors of their minors. -/
theorem dvd_minors_iff_embDiag {s : ℕ} (c : ℤ) :
    (∀ (u : Fin s → Fin m) (v : Fin s → Fin k), c ∣ (A.submatrix u v).det) ↔
      ∀ (u : Fin s → Fin m) (v : Fin s → Fin n), c ∣ ((embDiag snf.f snf.a).submatrix u v).det := by
  rw [dvd_minors_iff_of_right_factor A (imageCols A snf) (coords A snf) (sectionCols A snf)
      (eq_imageCols_mul_coords A snf) (imageCols_eq_mul_sectionCols A snf),
    dvd_minors_iff_of_left_factor (imageCols A snf) (embDiag snf.f snf.a) (basisCols A snf)
      (snf.bM.toMatrix (Pi.basisFun ℤ (Fin m))) (imageCols_eq_basisCols_mul A snf)
      (by rw [imageCols_eq_basisCols_mul, ← Matrix.mul_assoc, flip_mul_basisCols, Matrix.one_mul])]

include snf in
/-- [proved-standard; formal-checked] The rank over ℚ of `A` is the rank `n` of Mathlib's Smith form. -/
theorem ratRank_eq_of_smith : ratRank A = n := by
  rw [ratRank_eq_of_minors_eq_zero_iff A (embDiag snf.f snf.a) fun s => by
      simpa only [zero_dvd_iff] using dvd_minors_iff_embDiag A snf (s := s) 0,
    ratRank_embDiag _ _ (SmithCokernel.a_ne_zero snf)]

/-- [proved-standard; formal-checked] `c` divides every `n × n` minor of `A` iff `c ∣ Π a i`. -/
theorem dvd_maxMinors_of_smith_iff (c : ℤ) :
    (∀ (u : Fin n → Fin m) (v : Fin n → Fin k), c ∣ (A.submatrix u v).det) ↔ c ∣ ∏ i, snf.a i := by
  rw [dvd_minors_iff_embDiag A snf, dvd_minors_embDiag_iff]

/-- [proved-standard; formal-checked] The gcd of the maximal minors of `A` is `|Π a i|`. -/
theorem gcd_maxMinors_of_smith :
    Finset.univ.gcd (fun fg : (Fin n → Fin m) × (Fin n → Fin k) => (A.submatrix fg.1 fg.2).det) =
      |∏ i, snf.a i| :=
  gcd_minors_eq_abs A n _ (dvd_maxMinors_of_smith_iff A snf)

/-- [proved-standard; formal-checked] **A prime drops the rank of `A` iff it divides `Π a i`** (Mathlib's form). -/
theorem modRank_lt_ratRank_of_smith_iff (p : ℕ) [Fact p.Prime] :
    modRank p A < ratRank A ↔ (p : ℤ) ∣ ∏ i, snf.a i := by
  rw [modRank_lt_ratRank_iff, ratRank_eq_of_smith A snf]
  exact dvd_maxMinors_of_smith_iff A snf _

/-- [proved-standard; formal-checked] The kernel of `A` modulo `p` is wider than over ℚ iff `p ∣ Π a i`. -/
theorem finrank_ker_lt_of_smith_iff (p : ℕ) [Fact p.Prime] :
    finrank ℚ (LinearMap.ker (A.map (Int.cast : ℤ → ℚ)).mulVecLin) <
        finrank (ZMod p) (LinearMap.ker (A.map (Int.cast : ℤ → ZMod p)).mulVecLin) ↔
      (p : ℤ) ∣ ∏ i, snf.a i := by
  rw [finrank_ker_lt_iff, modRank_lt_ratRank_of_smith_iff A snf]

/-- [proved-standard; formal-checked] `Π a i` is the product of the form's nonzero invariants (`SmithCokernel`). -/
theorem prod_a_eq_prod_invariant :
    ∏ i, snf.a i = ∏ j ∈ Finset.univ.filter (fun j => SmithCokernel.invariant snf j ≠ 0),
      SmithCokernel.invariant snf j := by
  have hset : Finset.univ.filter (fun j => SmithCokernel.invariant snf j ≠ 0) = Finset.univ.map snf.f := by
    ext j
    simp [SmithCokernel.invariant_eq_zero_iff]
  rw [hset, Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => (SmithCokernel.invariant_f snf i).symm

/-- [proved-standard; formal-checked] On `SmithCokernel.smith`: `rank_ℚ A` is the form's rank. -/
theorem ratRank_eq_smith_rank : ratRank A = (SmithCokernel.smith A.mulVecLin).1 :=
  ratRank_eq_of_smith A (SmithCokernel.smith A.mulVecLin).2

/-- [proved-standard; formal-checked] **On `smith`: `p` drops the rank iff `p ∣ Π` of the nonzero invariants.** -/
theorem modRank_lt_ratRank_iff_smith (p : ℕ) [Fact p.Prime] :
    modRank p A < ratRank A ↔
      (p : ℤ) ∣ ∏ j ∈ Finset.univ.filter (fun j => SmithCokernel.invariant (SmithCokernel.smith A.mulVecLin).2 j ≠ 0),
        SmithCokernel.invariant (SmithCokernel.smith A.mulVecLin).2 j := by
  rw [← prod_a_eq_prod_invariant]
  exact modRank_lt_ratRank_of_smith_iff A _ p

/-- [proved-standard; formal-checked] On `smith`: the maximal minors' gcd is `|Π|` of the nonzero invariants. -/
theorem gcd_maxMinors_smith_eq :
    Finset.univ.gcd (fun fg : (Fin (SmithCokernel.smith A.mulVecLin).1 → Fin m) ×
        (Fin (SmithCokernel.smith A.mulVecLin).1 → Fin k) => (A.submatrix fg.1 fg.2).det) =
      |∏ j ∈ Finset.univ.filter (fun j => SmithCokernel.invariant (SmithCokernel.smith A.mulVecLin).2 j ≠ 0),
        SmithCokernel.invariant (SmithCokernel.smith A.mulVecLin).2 j| := by
  rw [← prod_a_eq_prod_invariant]
  exact gcd_maxMinors_of_smith A _

end MathlibSmith

end Holonics.Landmarks.SmithMinors
