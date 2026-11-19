import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# The closure key's torsion: the rank falls at the primes of every maximal minor, and the newline keys

[proved-derived; formal-checked] Formal obligations (#410), the box "The closure key's torsion (#405)". Sources:
`tower_ring::{rational_rank, closure_key}` (PR #460; the file at `700649f67`,
`crates/holonics/examples/solenoidal_alpha/complete_language/tower_ring.rs`) and the record of October 25 on the
newline closure (`research/records/2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_PLUS_ONE_*`, §§2, 5, 10, 11;
PRs #461, #466, #468); atlas `hnn.tower-ring-closure`, `key.newline-closure-torsion`,
`key.newline-closure-differences`, `key.newline-closure-reflection`.

What is proved.

1. **The rank by minors, over a field** (`le_rank_iff_exists_minor`): `r ≤ rank A` exactly when some `r × r` minor
   `det A[f, g]` is nonzero. Mathlib states the rank through the range; the easy half is `le_rank_of_minor_ne_zero`
   (through `rank_submatrix_le`), and `exists_minor_ne_zero_of_le_rank` chooses `r` independent columns and then `r`
   independent rows of them. Rank–nullity in this form is `finrank_ker_add_rank`.
2. **A prime is torsion where the rank falls, and the rank falls where it divides every maximal minor.** For an
   integer system `A`, `ratRank A` is its rank over ℚ and `modRank p A` its rank over `ZMod p`. A minor of a reduction
   is the reduction of the minor (`det_submatrix_cast`), so `r ≤ rank_ℚ A` iff some `r × r` minor is nonzero
   (`le_ratRank_iff`) and `r ≤ rank_p A` iff some is prime to `p` (`le_modRank_iff`). Hence `rank_p A ≤ rank_ℚ A`
   (`modRank_le_ratRank`), and `rank_p A < rank_ℚ A` iff `p` divides every maximal minor
   (`modRank_lt_ratRank_iff`), iff the kernel modulo `p` is wider than the rational kernel (`finrank_ker_lt_iff`).
   Each such prime is a prime factor of any nonzero maximal minor (`torsion_prime_mem_primeFactors`), which is why
   `closure_key` reads its candidate moduli from the one minor `det M` that `rational_rank` certifies.
3. **What certifies the rank** (`rank_certificate`). An `r × r` minor prime to `p` certifies
   `r ≤ rank_p A ≤ rank_ℚ A`. `s` integer vectors annihilated by every row, with `r + s` the column count, whose
   entries at `s` distinct columns form `δ` times the identity with `δ` prime to `p`, are independent over ℚ and over
   `ZMod p` (`linearIndependent_of_unit_block`) and certify `rank_ℚ A ≤ r` and `rank_p A ≤ r`
   (`rank_add_le_of_kernel`, `rank_add_le_of_cast_kernel`). Cramer's kernel at the minor's pivots has that shape
   with `δ = det M` (at its free column `det M`, at the other free columns `0`), so `rational_rank`'s check of every
   row against it certifies `rank_ℚ = rank_p = r`; that the Cramer vectors are integral and vanish on the pivot rows
   is the construction's own and is not needed for the certificate.
4. **Casting out elevens.** On `ℤ/(b + 1)` the base is a half-turn, `b = −1` (`base_eq_neg_one`), so a step of a
   leading-first reading is `b n + d = d − n` (`halfTurn_step`) and a digit word read leading first (`readLeading`)
   is its word of half-turns (`halfTurns`, `readLeading_halfTurns`), whose value is the alternating digit sum from the
   last digit (`readLeading_alternatingSum`, through `readLeading_eq_ofDigits` and `ofDigits_cast_alternatingSum`,
   which applies Mathlib's `Nat.ofDigits_neg_one`). The newline origin's torsion `ℤ/110` splits as `ℤ/10 × ℤ/11`
   (`newlineTorsionSplit`), carrying `c` to its last digit and its alternating digit sum
   (`newlineTorsionSplit_natCast`): the units key and casting out elevens.
5. **The newline closure's linear keys for sums (§5).** `SumKey` holds §4's shared moves: `u` after the newline and
   after `+`, `θ(x, y) = v x + w y` on digit pairs, `z` before `+` and before `=`, `u′` after `=`, and `ψ(d) = s d`.
   A line's closure (`SumKey.closure`) is the sum of the pair moves its newline loop meets, the pair into `c₀`
   excluded and `ψ(c₀)` subtracted, read by the line's shape (`operand`: one or two places; `result`: one, two or
   three). Over any commutative ring and base `b ≥ 2`, a key closing every true line with operands below `b²` has
   `s b (b + 1) = 0` (`SumKey.sum_necessity`, four lines); where `b(b + 1) = 0` the key `SumKey.ofScale s b`
   (`u = w = u′ = −s b`, `v = 2 s b`, `z = s + s b`) closes every line `x + y = c` to `s (x + y − c)`
   (`SumKey.ofScale_closure`). So a key with `s` a unit exists exactly where `b(b + 1) = 0` (`SumKey.exists_iff`), and
   modulo `q` exactly when `q ∣ b(b + 1)` (`SumKey.zmod_exists_iff`). In base 10, modulo 11 the key with `s = −1` has
   §2's moves (`SumKey.eleven_moves`; §2's gauge `+2` on the newline and in `ψ` removed) and closes a line to
   `c − a − b` (`eleven_closure`), modulo 10 it is the units key (`units_moves`), and modulo 110 one key closes a line
   to `a + b − c` (`torsion110_closure`).
6. **Sums with `=` reflecting (§11).** With the result's pairs read in the reversed hand and `c₀` in the starting hand
   (`resultReflected`, `closureReflected`), a key has `s b (b − 1) = 0` (`SumKey.reflected_necessity`), the key
   `ofScaleReflected s b` closes every line to `s (x + y − c)` where `b(b − 1) = 0` (`ofScaleReflected_closure`),
   and a key exists modulo `q` exactly when `q ∣ b(b − 1)` (`zmod_reflected_exists_iff`).
7. **Differences (§10).** `DiffKey` gives each separator its own moves (`u` after the newline, `u⁻` after `−`, `u′`
   after `=`, `z` before `−`, `z⁼` before `=`), with `θ(x, y) = v x + w y` and `ψ(d) = s d`, and `DiffKey.closure`
   reads a minuend and a subtrahend of one or two places and a result of one or two. A key closing every true line
   `x − y = c` with `y ≤ x < b²` has `2 s b = 0` (`DiffKey.diff_necessity`, five lines), `DiffKey.ofScale s b` closes
   every line to `s (x − y − c)` where `2b = 0` (`DiffKey.ofScale_closure`), and a key exists modulo `q` exactly
   when `q ∣ 2b` (`DiffKey.zmod_exists_iff`); in base 10 modulo 20 it is §10's key (`twenty_moves`) and closes a
   line to `c − x + y`, a false line to `δ mod 20` (`twenty_closure`). On the lines whose minuend has two places the
   record's integer key (`DiffKey.exact`) closes every line to `c − x + y` over any ring (`exact_closure`); on a
   one-place minuend it is off by `2 b x` (`exact_closure_one_place`), so over ℤ it misses every such line but
   `0 − 0 = 0`.

What is not claimed.
- The Smith-invariant form of item 2 is `Landmarks/SmithMinors`: through Cauchy–Binet the gcd of the maximal minors
  is the product of a Smith form's nonzero invariants up to sign, and `p` drops the rank iff it divides that product
  (`SmithMinors.gcd_maxMinors_smith_eq`, `SmithMinors.modRank_lt_ratRank_iff_smith`).
- The reduction of the rational kernel as a subspace (the integral saturation of `ker_ℚ`, which reduces to a subspace
  of width `dim ker_ℚ`): item 2 compares the two kernels' widths.
- The torsion of a general pair key, every pair its own move: the record's minors' gcds `b(b + 1)`, `2b` and
  `b(b − 1)` and its rank falls are computations over the finite line sets (bases 3 to 10 and 12). Items 5 to 7 are
  for keys linear in the digit values, which is how the record derives them.
- Operands below `b³` (§6), and the rest of §11: differences with `−` reflecting and the mixed menus. These are
  `Landmarks/ClosureKeyMenus` (operands below `b³` admit a key modulo `q` iff `q ∣ b·gcd(2, b + 1)`, which for a
  prime is `p ∣ 2b`; differences with `−` reflecting have no torsion; one menu with `−` reflecting and `=`
  restarting has `q ∣ b(b + 1)`).
- That a closure is read from a line's bytes: `closure` is the pair sum read by the line's shape, as §5 reads it, and
  a reader checks it against the loop's pairs.

The computational object is the helical pair interaction read on a closure's menu: each (seam, arriving class) pair is
a contact whose move turns a ring, a loop between two arrivals of the origin closes at the turn its standing classes
name, and the moduli where every loop closes are the torsion of the system of pair counts. Of the winding guide's six
general objects this touches the pair (the contacts' moves), the helix (a ring's residue, and the base's half-turn on
`ℤ/(b + 1)`) and faces and placement (a digit's place weight `bᵏ`, read `0` or `±1` on the cheap rings); the cell
holonomy, the tube and the tower thread stay attached.

Beside it stand `Landmarks/SmithCokernel` and `Landmarks/IntegralCokernel` (the integral cokernel ledger),
`Mathematics/RadixWindowReceiver.cheap_faces` (modulo a divisor of `b + 1` a number is its alternating digit sum,
read through `Nat.digits`) and `HNN/RingHand` (the ring's hand, which a reflector reverses).

No `sorry`, no `axiom`, no `native_decide`.
-/

open Module Matrix

namespace Holonics.Landmarks.ClosureKeyTorsion

/-! ## 1. The rank by minors, over a field -/

section Field

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
/-- A nonzero `r × r` minor bounds the rank below: `r ≤ rank A`. -/
theorem le_rank_of_minor_ne_zero (A : Matrix m n K) {r : ℕ} (f : Fin r → m) (g : Fin r → n)
    (h : (A.submatrix f g).det ≠ 0) : r ≤ A.rank := by
  classical
  have h1 := rank_of_det_ne_zero h
  have h2 := rank_submatrix_le A f g
  rw [Fintype.card_fin] at h1
  omega

/-- Where `r ≤ rank A`, some `r × r` minor is nonzero: `r` independent columns, then `r` independent
rows of them. -/
theorem exists_minor_ne_zero_of_le_rank (A : Matrix m n K) {r : ℕ} (h : r ≤ A.rank) :
    ∃ (f : Fin r → m) (g : Fin r → n), (A.submatrix f g).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  have : Fintype κ := Fintype.ofInjective a ha
  have hκ : Fintype.card κ = A.rank := by
    rw [rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  obtain ⟨e⟩ : Nonempty (Fin r ↪ κ) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, hκ]; exact h)
  set B : Matrix m (Fin r) K := A.submatrix id (a ∘ e) with hB
  have hBcol : LinearIndependent K B.col := by
    have : B.col = A.col ∘ a ∘ e := by ext j i; rfl
    rw [this]; exact hli.comp e e.injective
  have hBr : B.rank = r := by
    rw [← rank_transpose]
    have := LinearIndependent.rank_matrix (M := Bᵀ) (by rw [row_transpose]; exact hBcol)
    rw [this, Fintype.card_fin]
  obtain ⟨κ', a', ha', hspan', hli'⟩ := exists_linearIndependent' K B.row
  have : Fintype κ' := Fintype.ofInjective a' ha'
  have hκ' : Fintype.card κ' = r := by
    rw [← hBr, rank_eq_finrank_span_row, ← hspan', finrank_span_eq_card hli']
  let e' : Fin r ≃ κ' := (Fintype.equivFinOfCardEq hκ').symm
  refine ⟨a' ∘ e', a ∘ e, ?_⟩
  have hC : LinearIndependent K (A.submatrix (a' ∘ e') (a ∘ e)).row := by
    have : (A.submatrix (a' ∘ e') (a ∘ e)).row = B.row ∘ a' ∘ e' := by ext i j; rfl
    rw [this]; exact hli'.comp e' e'.injective
  exact ((isUnit_iff_isUnit_det _).mp (linearIndependent_rows_iff_isUnit.mp hC)).ne_zero

/-- Statement 1: **the rank by minors.** `r ≤ rank A` exactly when some `r × r` minor is nonzero. -/
theorem le_rank_iff_exists_minor (A : Matrix m n K) {r : ℕ} :
    r ≤ A.rank ↔ ∃ (f : Fin r → m) (g : Fin r → n), (A.submatrix f g).det ≠ 0 :=
  ⟨exists_minor_ne_zero_of_le_rank A, fun ⟨f, g, h⟩ => le_rank_of_minor_ne_zero A f g h⟩

omit [Fintype m] in
/-- Rank–nullity for a matrix: the kernel's width and the rank fill the columns. -/
theorem finrank_ker_add_rank (A : Matrix m n K) :
    finrank K (LinearMap.ker A.mulVecLin) + A.rank = Fintype.card n := by
  rw [Matrix.rank, add_comm, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_fintype_fun_eq_card]

omit [Fintype m] [Fintype n] in
/-- Vectors whose entries at `s` distinct columns form `δ` times the identity, `δ ≠ 0`, are independent. -/
theorem linearIndependent_of_unit_block {s : ℕ} (v : Fin s → n → K) (c : Fin s → n) (δ : K)
    (hδ : δ ≠ 0) (hc : ∀ k k', v k (c k') = if k = k' then δ else 0) : LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro w hw k
  have := congr_fun hw (c k)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, Pi.zero_apply, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact (mul_eq_zero.mp this).resolve_right hδ

omit [Fintype m] in
/-- `s` independent vectors in the kernel bound the rank above: `rank A + s ≤ #columns`. -/
theorem rank_add_le_of_kernel {s : ℕ} (A : Matrix m n K) (v : Fin s → n → K)
    (hli : LinearIndependent K v) (hv : ∀ k, A *ᵥ v k = 0) : A.rank + s ≤ Fintype.card n := by
  have hle : Submodule.span K (Set.range v) ≤ LinearMap.ker A.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simpa using hv k
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_fin] at h1
  have h2 := finrank_ker_add_rank A
  omega

end Field

/-! ## 2–3. An integer system, its reductions and the certificate -/

section Integer

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The rank of an integer system over ℚ. -/
noncomputable def ratRank (A : Matrix m n ℤ) : ℕ := (A.map (Int.cast : ℤ → ℚ)).rank

/-- The rank of an integer system reduced modulo `p`, over `ZMod p`. -/
noncomputable def modRank (p : ℕ) (A : Matrix m n ℤ) : ℕ := (A.map (Int.cast : ℤ → ZMod p)).rank

omit [Fintype m] [Fintype n] in
/-- A minor of the reduction is the reduction of the minor. -/
theorem det_submatrix_cast {R : Type*} [CommRing R] (A : Matrix m n ℤ) {r : ℕ} (f : Fin r → m)
    (g : Fin r → n) : ((A.map (Int.cast : ℤ → R)).submatrix f g).det = ((A.submatrix f g).det : R) :=
  ((Int.castRingHom R).map_det (A.submatrix f g)).symm

/-- `r ≤ rank_ℚ A` exactly when some integer `r × r` minor is nonzero. -/
theorem le_ratRank_iff (A : Matrix m n ℤ) {r : ℕ} :
    r ≤ ratRank A ↔ ∃ (f : Fin r → m) (g : Fin r → n), (A.submatrix f g).det ≠ 0 := by
  rw [ratRank, le_rank_iff_exists_minor]
  simp only [det_submatrix_cast, ne_eq, Int.cast_eq_zero]

/-- `r ≤ rank_p A` exactly when some integer `r × r` minor is prime to `p`. -/
theorem le_modRank_iff (p : ℕ) [Fact p.Prime] (A : Matrix m n ℤ) {r : ℕ} :
    r ≤ modRank p A ↔ ∃ (f : Fin r → m) (g : Fin r → n), ¬ (p : ℤ) ∣ (A.submatrix f g).det := by
  rw [modRank, le_rank_iff_exists_minor]
  simp only [det_submatrix_cast, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The rank modulo a prime never exceeds the rank over ℚ. -/
theorem modRank_le_ratRank (p : ℕ) [Fact p.Prime] (A : Matrix m n ℤ) : modRank p A ≤ ratRank A := by
  obtain ⟨f, g, h⟩ := (le_modRank_iff p A).mp le_rfl
  exact (le_ratRank_iff A).mpr ⟨f, g, fun h0 => h (h0 ▸ dvd_zero _)⟩

/-- Statement 2: **a prime drops the rank exactly when it divides every maximal minor.** -/
theorem modRank_lt_ratRank_iff (p : ℕ) [Fact p.Prime] (A : Matrix m n ℤ) :
    modRank p A < ratRank A ↔
      ∀ (f : Fin (ratRank A) → m) (g : Fin (ratRank A) → n), (p : ℤ) ∣ (A.submatrix f g).det := by
  rw [← not_le, le_modRank_iff]
  push Not
  rfl

omit [Fintype m] in
/-- Statement 2, in widths: the kernel modulo `p` is wider than the rational kernel exactly when the rank
falls modulo `p`. -/
theorem finrank_ker_lt_iff (p : ℕ) [Fact p.Prime] (A : Matrix m n ℤ) :
    finrank ℚ (LinearMap.ker (A.map (Int.cast : ℤ → ℚ)).mulVecLin) <
        finrank (ZMod p) (LinearMap.ker (A.map (Int.cast : ℤ → ZMod p)).mulVecLin) ↔
      modRank p A < ratRank A := by
  have h1 := finrank_ker_add_rank (A.map (Int.cast : ℤ → ℚ))
  have h2 := finrank_ker_add_rank (A.map (Int.cast : ℤ → ZMod p))
  simp only [ratRank, modRank]
  omega

/-- Statement 2: a prime where the rank falls is a prime factor of any nonzero maximal minor, so the
candidate moduli are read from one certified minor. -/
theorem torsion_prime_mem_primeFactors (p : ℕ) [Fact p.Prime] (A : Matrix m n ℤ)
    (f : Fin (ratRank A) → m) (g : Fin (ratRank A) → n) (hM : (A.submatrix f g).det ≠ 0)
    (hp : modRank p A < ratRank A) : p ∈ (A.submatrix f g).det.natAbs.primeFactors := by
  have h := (modRank_lt_ratRank_iff p A).mp hp f g
  rw [Nat.mem_primeFactors]
  exact ⟨Fact.out, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hM⟩

omit [Fintype m] in
/-- Integer kernel vectors with a `δ`-identity block, `δ` nonzero in the field, bound the field rank. -/
theorem rank_add_le_of_cast_kernel {K : Type*} [Field K] {s : ℕ} (A : Matrix m n ℤ)
    (v : Fin s → n → ℤ) (c : Fin s → n) (δ : ℤ) (hδ : (δ : K) ≠ 0) (hv : ∀ k, A *ᵥ v k = 0)
    (hc : ∀ k k', v k (c k') = if k = k' then δ else 0) :
    (A.map (Int.cast : ℤ → K)).rank + s ≤ Fintype.card n := by
  refine rank_add_le_of_kernel _ (fun k j => (v k j : K)) ?_ ?_
  · refine linearIndependent_of_unit_block _ c (δ : K) hδ fun k k' => ?_
    simp only [hc]
    split_ifs <;> simp
  · intro k
    ext i
    have := (Int.castRingHom K).map_mulVec A (v k) i
    simp only [hv k, Pi.zero_apply, map_zero] at this
    exact this.symm

/-- Statement 3: **what certifies the rank.** A minor prime to `p` and `s` kernel vectors checked on every row,
with a `δ`-identity block at `s` columns (`δ` prime to `p`; Cramer's kernel has `δ = det M`), certify
`rank_ℚ = rank_p = r` when `r + s` is the column count. -/
theorem rank_certificate (p : ℕ) [Fact p.Prime] (A : Matrix m n ℤ) {r s : ℕ} (f : Fin r → m)
    (g : Fin r → n) (hM : ¬ (p : ℤ) ∣ (A.submatrix f g).det) (v : Fin s → n → ℤ) (c : Fin s → n)
    (δ : ℤ) (hδ : ¬ (p : ℤ) ∣ δ) (hv : ∀ k, A *ᵥ v k = 0)
    (hc : ∀ k k', v k (c k') = if k = k' then δ else 0) (hrs : r + s = Fintype.card n) :
    ratRank A = r ∧ modRank p A = r := by
  have h1 : r ≤ modRank p A := (le_modRank_iff p A).mpr ⟨f, g, hM⟩
  have h2 := modRank_le_ratRank p A
  have hδq : (δ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr fun h0 => hδ (h0 ▸ dvd_zero _)
  have hδp : (δ : ZMod p) ≠ 0 := fun h0 => hδ ((ZMod.intCast_zmod_eq_zero_iff_dvd δ p).mp h0)
  have h3 := rank_add_le_of_cast_kernel A v c δ hδq hv hc
  have h4 := rank_add_le_of_cast_kernel A v c δ hδp hv hc
  simp only [ratRank, modRank] at *
  omega

end Integer

/-! ## 4. Casting out elevens -/

section HalfTurns

/-- On `ℤ/(b + 1)` the base is a half-turn: `b = −1`. -/
theorem base_eq_neg_one (b : ℕ) : ((b : ℕ) : ZMod (b + 1)) = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  exact_mod_cast ZMod.natCast_self (b + 1)

/-- Statement 4: a step of a leading-first reading is a half-turn, `b n + d = d − n`. -/
theorem halfTurn_step (b : ℕ) (x d : ZMod (b + 1)) : (b : ZMod (b + 1)) * x + d = d - x := by
  rw [base_eq_neg_one]; ring

/-- Reading a digit word leading first, `v ↦ b v + d`. -/
def readLeading (b : ℕ) (L : List ℕ) : ℕ := L.foldl (fun v d => b * v + d) 0

/-- The half-turn word: `v ↦ d − v`. -/
def halfTurns {R : Type*} [Ring R] (L : List R) : R := L.foldl (fun v d => d - v) 0

/-- On `ℤ/(b + 1)` the leading-first reading from any start is the half-turn word from that start. -/
theorem cast_foldl_halfTurns (b : ℕ) (L : List ℕ) (a : ℕ) :
    ((L.foldl (fun v d => b * v + d) a : ℕ) : ZMod (b + 1)) =
      (L.map (fun d : ℕ => (d : ZMod (b + 1)))).foldl (fun v d => d - v) (a : ZMod (b + 1)) := by
  induction L generalizing a with
  | nil => rfl
  | cons d L ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    congr 1
    push_cast
    exact halfTurn_step b _ _

/-- Statement 4: on `ℤ/(b + 1)` a digit word read leading first is its word of half-turns. -/
theorem readLeading_halfTurns (b : ℕ) (L : List ℕ) :
    ((readLeading b L : ℕ) : ZMod (b + 1)) = halfTurns (L.map (fun d : ℕ => (d : ZMod (b + 1)))) := by
  simpa [readLeading, halfTurns] using cast_foldl_halfTurns b L 0

/-- The leading-first reading from `a` is `a bⁿ` plus the word's value (Mathlib's digits run from the last). -/
theorem foldl_eq_ofDigits_reverse (b : ℕ) (L : List ℕ) (a : ℕ) :
    L.foldl (fun v d => b * v + d) a = a * b ^ L.length + Nat.ofDigits b L.reverse := by
  induction L generalizing a with
  | nil => simp
  | cons d L ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, Nat.ofDigits_append, Nat.ofDigits_singleton,
      List.length_reverse, List.length_cons]
    ring

/-- The leading-first reading is the value of the reversed digit list. -/
theorem readLeading_eq_ofDigits (b : ℕ) (L : List ℕ) : readLeading b L = Nat.ofDigits b L.reverse := by
  have := foldl_eq_ofDigits_reverse b L 0
  rw [zero_mul, zero_add] at this
  exact this

/-- On `ℤ/(b + 1)` a number is the alternating sum of its digits, from the last (Mathlib's
`Nat.ofDigits_neg_one`). -/
theorem ofDigits_cast_alternatingSum (b : ℕ) (L : List ℕ) :
    ((Nat.ofDigits b L : ℕ) : ZMod (b + 1)) = ((L.map fun d : ℕ => (d : ℤ)).alternatingSum : ℤ) := by
  have h : ((b : ℕ) : ℤ) ≡ -1 [ZMOD ((b + 1 : ℕ) : ℤ)] :=
    (Int.modEq_iff_dvd.mpr (by push_cast; ring_nf; exact dvd_refl _)).symm
  have := Nat.ofDigits_zmodeq' (b : ℤ) (-1) (b + 1) h L
  rw [Nat.ofDigits_neg_one, ← Nat.coe_ofDigits] at this
  rw [← Int.cast_natCast, (ZMod.intCast_eq_intCast_iff _ _ _).mpr this]

/-- Statement 4: the half-turn word's value is the alternating digit sum from the last digit. -/
theorem readLeading_alternatingSum (b : ℕ) (L : List ℕ) :
    ((readLeading b L : ℕ) : ZMod (b + 1)) =
      ((L.reverse.map fun d : ℕ => (d : ℤ)).alternatingSum : ℤ) := by
  rw [readLeading_eq_ofDigits, ofDigits_cast_alternatingSum]

/-- The newline origin's torsion `ℤ/110` splits into its `10`-part and its `11`-part. -/
def newlineTorsionSplit : ZMod 110 ≃+* ZMod 10 × ZMod 11 :=
  ZMod.chineseRemainder (by norm_num : Nat.Coprime 10 11)

/-- The split carries `c` to its last digit and to its alternating digit sum: the units key and
casting out elevens. -/
theorem newlineTorsionSplit_natCast (c : ℕ) :
    newlineTorsionSplit (c : ZMod 110) =
      (((c % 10 : ℕ) : ZMod 10),
        ((((Nat.digits 10 c).map fun d : ℕ => (d : ℤ)).alternatingSum : ℤ) : ZMod 11)) := by
  rw [map_natCast]
  refine Prod.ext ?_ ?_
  · simp [ZMod.natCast_mod]
  · simp only [Prod.snd_natCast]
    have := ofDigits_cast_alternatingSum 10 (Nat.digits 10 c)
    rwa [Nat.ofDigits_digits] at this

end HalfTurns

/-! ## 5–6. The newline closure's linear keys for sums -/

section SumKeys

/-- §5's key linear in the digit values with §4's shared moves: `u` after the newline and after `+`,
`θ(x, y) = v x + w y` on digit pairs, `z` before `+` and before `=`, `u′` after `=`, `ψ(d) = s d`. -/
structure SumKey (R : Type*) where
  u : R
  v : R
  w : R
  z : R
  u' : R
  s : R

namespace SumKey

variable {R : Type*} [CommRing R] (κ : SumKey R) (b : ℕ)

/-- An operand of one place `d` meets `(seam, d)(d, sep)`; of two places `d₁d₀`, `(seam, d₁)(d₁, d₀)(d₀, sep)`. -/
def operand (x : ℕ) : R :=
  if x < b then (κ.u + κ.z) * (x : R) else (κ.u + κ.v) * ((x / b : ℕ) : R) + (κ.w + κ.z) * ((x % b : ℕ) : R)

/-- The result after `=`: its pairs up to and not including the pair into `c₀`, less `ψ(c₀)`; one place
`c₀`, two places `c₁c₀` (`(=, c₁)`), three places `c₂c₁c₀` (`(=, c₂)(c₂, c₁)`). -/
def result (c : ℕ) : R :=
  if c < b then -(κ.s * (c : R))
  else if c < b ^ 2 then κ.u' * ((c / b : ℕ) : R) - κ.s * ((c % b : ℕ) : R)
  else (κ.u' + κ.v) * ((c / b ^ 2 : ℕ) : R) + κ.w * ((c / b % b : ℕ) : R) - κ.s * ((c % b : ℕ) : R)

/-- A line's closure: the sum of the pair moves its newline loop meets, less `ψ(c₀)`. -/
def closure (x y c : ℕ) : R := κ.operand b x + κ.operand b y + κ.result b c

/-- A one-place operand. -/
theorem operand_one {x : ℕ} (hx : x < b) : κ.operand b x = (κ.u + κ.z) * (x : R) := if_pos hx

/-- The places of a two-place word. -/
theorem div_mod_two {d₁ d₀ : ℕ} (h₀ : d₀ < b) : (b * d₁ + d₀) / b = d₁ ∧ (b * d₁ + d₀) % b = d₀ := by
  have hb : 0 < b := by omega
  constructor
  · rw [add_comm, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt h₀, zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₀]

/-- A two-place operand `b d₁ + d₀`. -/
theorem operand_two {d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : 1 ≤ d₁) :
    κ.operand b (b * d₁ + d₀) = (κ.u + κ.v) * (d₁ : R) + (κ.w + κ.z) * (d₀ : R) := by
  have hlt : ¬ b * d₁ + d₀ < b := by nlinarith
  obtain ⟨h1, h2⟩ := div_mod_two b (d₁ := d₁) h₀
  rw [operand, if_neg hlt, h1, h2]

/-- A one-place result. -/
theorem result_one {c : ℕ} (hc : c < b) : κ.result b c = -(κ.s * (c : R)) := if_pos hc

/-- A two-place result `b d₁ + d₀`. -/
theorem result_two {d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : 1 ≤ d₁) (h₁' : d₁ < b) :
    κ.result b (b * d₁ + d₀) = κ.u' * (d₁ : R) - κ.s * (d₀ : R) := by
  have hlt : ¬ b * d₁ + d₀ < b := by nlinarith
  have hlt' : b * d₁ + d₀ < b ^ 2 := by nlinarith
  obtain ⟨h1, h2⟩ := div_mod_two b (d₁ := d₁) h₀
  rw [result, if_neg hlt, if_pos hlt', h1, h2]

/-- The places of a three-place word. -/
theorem div_mod_three {d₂ d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : d₁ < b) :
    (b ^ 2 * d₂ + b * d₁ + d₀) / b ^ 2 = d₂ ∧ (b ^ 2 * d₂ + b * d₁ + d₀) / b % b = d₁ ∧
      (b ^ 2 * d₂ + b * d₁ + d₀) % b = d₀ := by
  have hb : 0 < b := by omega
  have hlo : b * d₁ + d₀ < b ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [show b ^ 2 * d₂ + b * d₁ + d₀ = (b * d₁ + d₀) + b ^ 2 * d₂ by ring,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add]
  · rw [show b ^ 2 * d₂ + b * d₁ + d₀ = d₀ + b * (b * d₂ + d₁) by ring, Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt h₀, zero_add, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₁]
  · rw [show b ^ 2 * d₂ + b * d₁ + d₀ = d₀ + b * (b * d₂ + d₁) by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt h₀]

/-- A three-place result `b² d₂ + b d₁ + d₀`. -/
theorem result_three {d₂ d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : d₁ < b) (h₂ : 1 ≤ d₂) :
    κ.result b (b ^ 2 * d₂ + b * d₁ + d₀) =
      (κ.u' + κ.v) * (d₂ : R) + κ.w * (d₁ : R) - κ.s * (d₀ : R) := by
  have hlt : ¬ b ^ 2 * d₂ + b * d₁ + d₀ < b := by nlinarith
  have hlt' : ¬ b ^ 2 * d₂ + b * d₁ + d₀ < b ^ 2 := by nlinarith
  obtain ⟨e2, e1, e0⟩ := div_mod_three b (d₂ := d₂) h₀ h₁
  rw [result, if_neg hlt, if_neg hlt', e2, e1, e0]

/-- Statement 5: a key closing every true sum with operands below `b²` has `s b (b + 1) = 0` (four lines:
`1 + 0`, `(b − 1) + 1`, `(b + 1) + 0`, `(b² − 1) + (b + 1)`). -/
theorem sum_necessity (hb : 2 ≤ b)
    (h : ∀ x y, x < b ^ 2 → y < b ^ 2 → κ.closure b x y (x + y) = 0) :
    κ.s * (b : R) * ((b : R) + 1) = 0 := by
  have h' : ∀ x y c, x < b ^ 2 → y < b ^ 2 → c = x + y → κ.closure b x y c = 0 :=
    fun x y c hx hy hc => hc ▸ h x y hx hy
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
  have E1 := h' 1 0 1 (by nlinarith) (by nlinarith) rfl
  rw [closure, operand_one κ (k + 2) (by omega : 1 < k + 2), operand_one κ (k + 2) (by omega : 0 < k + 2),
    result_one κ (k + 2) (by omega : 1 < k + 2)] at E1
  have E2 := h' (k + 1) 1 ((k + 2) * 1 + 0) (by nlinarith) (by nlinarith) (by ring)
  rw [closure, operand_one κ (k + 2) (by omega : k + 1 < k + 2),
    operand_one κ (k + 2) (by omega : 1 < k + 2), result_two κ (k + 2) (by omega) le_rfl (by omega)] at E2
  have E4 := h' ((k + 2) * 1 + 1) 0 ((k + 2) * 1 + 1) (by nlinarith) (by nlinarith) (by ring)
  rw [closure, operand_two κ (k + 2) (by omega) le_rfl, operand_one κ (k + 2) (by omega : 0 < k + 2),
    result_two κ (k + 2) (by omega) le_rfl (by omega)] at E4
  have E6 := h' ((k + 2) * (k + 1) + (k + 1)) ((k + 2) * 1 + 1) ((k + 2) ^ 2 * 1 + (k + 2) * 1 + 0)
    (by nlinarith) (by nlinarith) (by ring)
  rw [closure, operand_two κ (k + 2) (by omega) (by omega), operand_two κ (k + 2) (by omega) le_rfl,
    result_three κ (k + 2) (by omega) (by omega) le_rfl] at E6
  push_cast at E1 E2 E4 E6 ⊢
  linear_combination E6 + (1 - ((k : R) + 2) ^ 2) * E1 + ((k : R) + 2) * E2 - ((k : R) + 2 + 1) * E4

/-- §5's solution: `u ≡ w ≡ u′ ≡ −s b`, `v ≡ 2 s b`, `z ≡ s + s b`. -/
def ofScale (s : R) (b : ℕ) : SumKey R :=
  ⟨-(s * b), 2 * s * b, -(s * b), s + s * b, -(s * b), s⟩

/-- Statement 5: where `b(b + 1) = 0`, §5's solution closes every line `x + y = c` to `s (x + y − c)`. -/
theorem ofScale_closure (s : R) (hR : ((b * (b + 1) : ℕ) : R) = 0) (x y c : ℕ) :
    (ofScale s b).closure b x y c = s * ((x : R) + y - c) := by
  have hR' : (b : R) * b = -b := by push_cast at hR; linear_combination hR
  have hop : ∀ t : ℕ, (ofScale s b).operand b t = s * t := by
    intro t
    unfold operand
    split_ifs
    · simp only [ofScale]; ring
    · conv_rhs => rw [← Nat.div_add_mod t b]
      simp only [ofScale]; push_cast; ring
  have hres : (ofScale s b).result b c = -(s * c) := by
    unfold result
    split_ifs
    · rfl
    · conv_rhs => rw [← Nat.div_add_mod c b]
      simp only [ofScale]; push_cast; ring
    · have e : c = b ^ 2 * (c / b ^ 2) + b * (c / b % b) + c % b := by
        have h1 := Nat.div_add_mod c b
        have h2 := Nat.div_add_mod (c / b) b
        rw [Nat.div_div_eq_div_mul, ← pow_two] at h2
        nlinarith [h1, h2]
      conv_rhs => rw [e]
      simp only [ofScale]; push_cast
      linear_combination (s * ((c / b ^ 2 : ℕ) : R)) * hR'
  rw [closure, hop, hop, hres]
  ring

/-- Statement 5: a key with `s` a unit closes every true sum with operands below `b²` exactly where
`b(b + 1) = 0`. -/
theorem exists_iff (hb : 2 ≤ b) :
    (∃ κ : SumKey R, IsUnit κ.s ∧ ∀ x y, x < b ^ 2 → y < b ^ 2 → κ.closure b x y (x + y) = 0) ↔
      ((b * (b + 1) : ℕ) : R) = 0 := by
  constructor
  · rintro ⟨κ, hs, h⟩
    have := κ.sum_necessity b hb h
    rw [mul_assoc, hs.mul_right_eq_zero] at this
    push_cast
    exact this
  · intro hR
    refine ⟨ofScale 1 b, isUnit_one, fun x y _ _ => ?_⟩
    rw [ofScale_closure b 1 hR]
    push_cast
    ring

/-- Statement 5: modulo `q`, such a key exists exactly when `q ∣ b(b + 1)`. -/
theorem zmod_exists_iff (q : ℕ) (hb : 2 ≤ b) :
    (∃ κ : SumKey (ZMod q), IsUnit κ.s ∧
        ∀ x y, x < b ^ 2 → y < b ^ 2 → κ.closure b x y (x + y) = 0) ↔ q ∣ b * (b + 1) := by
  rw [exists_iff b hb, ZMod.natCast_eq_zero_iff]

/-- Statement 5, base 10 modulo 11: the key closes a line to `c − a − b` (casting out elevens). -/
theorem eleven_closure (x y c : ℕ) :
    (ofScale (-1 : ZMod 11) 10).closure 10 x y c = (c : ZMod 11) - x - y := by
  rw [ofScale_closure 10 (-1) (by decide)]
  ring

/-- Statement 5: modulo 11 the key with `s = −1` has §2's moves: `θ(+, y) = −y`, `θ(x, y) = 2x − y`,
`θ(digit, op) = 0`, `θ(=, y) = −y`, `ψ(d) = −d` (§2's gauge `+2` on the newline and in `ψ` removed). -/
theorem eleven_moves : ofScale (-1 : ZMod 11) 10 = ⟨-1, 2, -1, 0, -1, -1⟩ := by
  simp only [ofScale, SumKey.mk.injEq]
  decide

/-- Statement 5: modulo 10 the key is the units key: `z ≡ s` and every other move `0`. -/
theorem units_moves : ofScale (1 : ZMod 10) 10 = ⟨0, 0, 0, 1, 0, 1⟩ := by
  simp only [ofScale, SumKey.mk.injEq]
  decide

/-- Statement 5: modulo 110 one key closes a line to `a + b − c`. -/
theorem torsion110_closure (x y c : ℕ) :
    (ofScale (1 : ZMod 110) 10).closure 10 x y c = (x : ZMod 110) + y - c := by
  rw [ofScale_closure 10 1 (by decide)]
  ring

/-- The result with `=` reflecting: its pairs read in the reversed hand, `c₀` in the starting hand. -/
def resultReflected (c : ℕ) : R :=
  if c < b then -(κ.s * (c : R))
  else if c < b ^ 2 then -(κ.u' * ((c / b : ℕ) : R)) - κ.s * ((c % b : ℕ) : R)
  else -((κ.u' + κ.v) * ((c / b ^ 2 : ℕ) : R)) - κ.w * ((c / b % b : ℕ) : R) - κ.s * ((c % b : ℕ) : R)

/-- A line's closure with `=` reflecting. -/
def closureReflected (x y c : ℕ) : R := κ.operand b x + κ.operand b y + κ.resultReflected b c

/-- Statement 6: with `=` reflecting, a key closing every true sum has `s b (b − 1) = 0`. -/
theorem reflected_necessity (hb : 2 ≤ b)
    (h : ∀ x y, x < b ^ 2 → y < b ^ 2 → κ.closureReflected b x y (x + y) = 0) :
    κ.s * (b : R) * ((b : R) - 1) = 0 := by
  have h' : ∀ x y c, x < b ^ 2 → y < b ^ 2 → c = x + y → κ.closureReflected b x y c = 0 :=
    fun x y c hx hy hc => hc ▸ h x y hx hy
  have hr1 : ∀ c, c < b → κ.resultReflected b c = -(κ.s * (c : R)) := fun c hc => if_pos hc
  have hr2 : ∀ d₁ d₀, d₀ < b → 1 ≤ d₁ → d₁ < b →
      κ.resultReflected b (b * d₁ + d₀) = -(κ.u' * (d₁ : R)) - κ.s * (d₀ : R) := by
    intro d₁ d₀ h₀ h₁ h₁'
    have hlt : ¬ b * d₁ + d₀ < b := by nlinarith
    have hlt' : b * d₁ + d₀ < b ^ 2 := by nlinarith
    obtain ⟨e1, e2⟩ := div_mod_two b (d₁ := d₁) h₀
    rw [resultReflected, if_neg hlt, if_pos hlt', e1, e2]
  have hr3 : ∀ d₂ d₁ d₀, d₀ < b → d₁ < b → 1 ≤ d₂ →
      κ.resultReflected b (b ^ 2 * d₂ + b * d₁ + d₀) =
        -((κ.u' + κ.v) * (d₂ : R)) - κ.w * (d₁ : R) - κ.s * (d₀ : R) := by
    intro d₂ d₁ d₀ h₀ h₁ h₂
    have hlt : ¬ b ^ 2 * d₂ + b * d₁ + d₀ < b := by nlinarith
    have hlt' : ¬ b ^ 2 * d₂ + b * d₁ + d₀ < b ^ 2 := by nlinarith
    obtain ⟨e2, e1, e0⟩ := div_mod_three b (d₂ := d₂) h₀ h₁
    rw [resultReflected, if_neg hlt, if_neg hlt', e2, e1, e0]
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
  have E1 := h' 1 0 1 (by nlinarith) (by nlinarith) rfl
  rw [closureReflected, operand_one κ (k + 2) (by omega : 1 < k + 2),
    operand_one κ (k + 2) (by omega : 0 < k + 2), hr1 1 (by omega)] at E1
  have E2 := h' (k + 1) 1 ((k + 2) * 1 + 0) (by nlinarith) (by nlinarith) (by ring)
  rw [closureReflected, operand_one κ (k + 2) (by omega : k + 1 < k + 2),
    operand_one κ (k + 2) (by omega : 1 < k + 2), hr2 1 0 (by omega) le_rfl (by omega)] at E2
  have E4 := h' ((k + 2) * 1 + 1) 0 ((k + 2) * 1 + 1) (by nlinarith) (by nlinarith) (by ring)
  rw [closureReflected, operand_two κ (k + 2) (by omega) le_rfl,
    operand_one κ (k + 2) (by omega : 0 < k + 2), hr2 1 1 (by omega) le_rfl (by omega)] at E4
  have E6 := h' ((k + 2) * (k + 1) + (k + 1)) ((k + 2) * 1 + 1) ((k + 2) ^ 2 * 1 + (k + 2) * 1 + 0)
    (by nlinarith) (by nlinarith) (by ring)
  rw [closureReflected, operand_two κ (k + 2) (by omega) (by omega), operand_two κ (k + 2) (by omega) le_rfl,
    hr3 1 1 0 (by omega) (by omega) le_rfl] at E6
  push_cast at E1 E2 E4 E6 ⊢
  linear_combination E6 - ((k : R) + 1) ^ 2 * E1 - ((k : R) + 1) * E4 + (k : R) * E2

/-- The reflected solution: `u ≡ w ≡ u′ ≡ s b`, `v ≡ 0`, `z ≡ s − s b`. -/
def ofScaleReflected (s : R) (b : ℕ) : SumKey R := ⟨s * b, 0, s * b, s - s * b, s * b, s⟩

/-- Statement 6: where `b(b − 1) = 0`, the reflected solution closes every line to `s (x + y − c)`. -/
theorem ofScaleReflected_closure (s : R) (hR : ((b * (b - 1) : ℕ) : R) = 0) (x y c : ℕ) :
    (ofScaleReflected s b).closureReflected b x y c = s * ((x : R) + y - c) := by
  have hR' : (b : R) * b = b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0; simp
    · have : ((b - 1 : ℕ) : R) = (b : R) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [Nat.cast_mul, this] at hR
      linear_combination hR
  have hop : ∀ t : ℕ, (ofScaleReflected s b).operand b t = s * t := by
    intro t
    unfold operand
    split_ifs
    · simp only [ofScaleReflected]; ring
    · conv_rhs => rw [← Nat.div_add_mod t b]
      simp only [ofScaleReflected]; push_cast; ring
  have hres : (ofScaleReflected s b).resultReflected b c = -(s * c) := by
    unfold resultReflected
    split_ifs
    · rfl
    · conv_rhs => rw [← Nat.div_add_mod c b]
      simp only [ofScaleReflected]; push_cast; ring
    · have e : c = b ^ 2 * (c / b ^ 2) + b * (c / b % b) + c % b := by
        have h1 := Nat.div_add_mod c b
        have h2 := Nat.div_add_mod (c / b) b
        rw [Nat.div_div_eq_div_mul, ← pow_two] at h2
        nlinarith [h1, h2]
      conv_rhs => rw [e]
      simp only [ofScaleReflected]; push_cast
      linear_combination (s * ((c / b ^ 2 : ℕ) : R)) * hR'
  rw [closureReflected, hop, hop, hres]
  ring

/-- Statement 6: with `=` reflecting, a key with `s` a unit exists exactly where `b(b − 1) = 0`. -/
theorem reflected_exists_iff (hb : 2 ≤ b) :
    (∃ κ : SumKey R, IsUnit κ.s ∧
        ∀ x y, x < b ^ 2 → y < b ^ 2 → κ.closureReflected b x y (x + y) = 0) ↔
      ((b * (b - 1) : ℕ) : R) = 0 := by
  have hc : ((b - 1 : ℕ) : R) = (b : R) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  constructor
  · rintro ⟨κ, hs, h⟩
    have := κ.reflected_necessity b hb h
    rw [mul_assoc, hs.mul_right_eq_zero] at this
    rw [Nat.cast_mul, hc]
    exact this
  · intro hR
    refine ⟨ofScaleReflected 1 b, isUnit_one, fun x y _ _ => ?_⟩
    rw [ofScaleReflected_closure b 1 hR]
    push_cast
    ring

/-- Statement 6: modulo `q`, exactly when `q ∣ b(b − 1)`. -/
theorem zmod_reflected_exists_iff (q : ℕ) (hb : 2 ≤ b) :
    (∃ κ : SumKey (ZMod q), IsUnit κ.s ∧
        ∀ x y, x < b ^ 2 → y < b ^ 2 → κ.closureReflected b x y (x + y) = 0) ↔ q ∣ b * (b - 1) := by
  rw [reflected_exists_iff b hb, ZMod.natCast_eq_zero_iff]

end SumKey

end SumKeys

/-! ## 7. The newline closure's linear keys for differences -/

section DiffKeys

/-- §10's key linear in the digit values, each separator its own moves: `u` after the newline, `u⁻` (`um`)
after `−`, `u′` after `=`, `z` before `−`, `z⁼` (`ze`) before `=`, `θ(x, y) = v x + w y`, `ψ(d) = s d`. -/
structure DiffKey (R : Type*) where
  u : R
  um : R
  u' : R
  z : R
  ze : R
  v : R
  w : R
  s : R

namespace DiffKey

variable {R : Type*} [CommRing R] (κ : DiffKey R) (b : ℕ)

/-- The minuend, of one or two places, between the newline and `−`. -/
def minuend (x : ℕ) : R :=
  if x < b then (κ.u + κ.z) * (x : R) else (κ.u + κ.v) * ((x / b : ℕ) : R) + (κ.w + κ.z) * ((x % b : ℕ) : R)

/-- The subtrahend, of one or two places, between `−` and `=`. -/
def subtrahend (y : ℕ) : R :=
  if y < b then (κ.um + κ.ze) * (y : R)
  else (κ.um + κ.v) * ((y / b : ℕ) : R) + (κ.w + κ.ze) * ((y % b : ℕ) : R)

/-- The result after `=`, of one or two places (a difference never has more places than its minuend). -/
def result (c : ℕ) : R :=
  if c < b then -(κ.s * (c : R)) else κ.u' * ((c / b : ℕ) : R) - κ.s * ((c % b : ℕ) : R)

/-- A line's closure `x − y = c`: the pair moves its newline loop meets, less `ψ(c₀)`. -/
def closure (x y c : ℕ) : R := κ.minuend b x + κ.subtrahend b y + κ.result b c

/-- A one-place minuend. -/
theorem minuend_one {x : ℕ} (hx : x < b) : κ.minuend b x = (κ.u + κ.z) * (x : R) := if_pos hx

/-- A two-place minuend. -/
theorem minuend_two {d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : 1 ≤ d₁) :
    κ.minuend b (b * d₁ + d₀) = (κ.u + κ.v) * (d₁ : R) + (κ.w + κ.z) * (d₀ : R) := by
  have hlt : ¬ b * d₁ + d₀ < b := by nlinarith
  obtain ⟨h1, h2⟩ := SumKey.div_mod_two b (d₁ := d₁) h₀
  rw [minuend, if_neg hlt, h1, h2]

/-- A one-place subtrahend. -/
theorem subtrahend_one {y : ℕ} (hy : y < b) : κ.subtrahend b y = (κ.um + κ.ze) * (y : R) := if_pos hy

/-- A two-place subtrahend. -/
theorem subtrahend_two {d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : 1 ≤ d₁) :
    κ.subtrahend b (b * d₁ + d₀) = (κ.um + κ.v) * (d₁ : R) + (κ.w + κ.ze) * (d₀ : R) := by
  have hlt : ¬ b * d₁ + d₀ < b := by nlinarith
  obtain ⟨h1, h2⟩ := SumKey.div_mod_two b (d₁ := d₁) h₀
  rw [subtrahend, if_neg hlt, h1, h2]

/-- A one-place result. -/
theorem result_one {c : ℕ} (hc : c < b) : κ.result b c = -(κ.s * (c : R)) := if_pos hc

/-- A two-place result. -/
theorem result_two {d₁ d₀ : ℕ} (h₀ : d₀ < b) (h₁ : 1 ≤ d₁) :
    κ.result b (b * d₁ + d₀) = κ.u' * (d₁ : R) - κ.s * (d₀ : R) := by
  have hlt : ¬ b * d₁ + d₀ < b := by nlinarith
  obtain ⟨h1, h2⟩ := SumKey.div_mod_two b (d₁ := d₁) h₀
  rw [result, if_neg hlt, h1, h2]

/-- Statement 7: a key closing every true difference with `y ≤ x < b²` has `2 s b = 0` (five lines:
`b − 0`, `(b + 1) − 0`, `1 − 1`, `(b + 1) − (b + 1)`, `b − 1`). -/
theorem diff_necessity (hb : 2 ≤ b)
    (h : ∀ x y, y ≤ x → x < b ^ 2 → κ.closure b x y (x - y) = 0) :
    2 * κ.s * (b : R) = 0 := by
  have h' : ∀ x y c, y ≤ x → x < b ^ 2 → c = x - y → κ.closure b x y c = 0 :=
    fun x y c hxy hx hc => hc ▸ h x y hxy hx
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
  have D2 := h' ((k + 2) * 1 + 0) 0 ((k + 2) * 1 + 0) (by omega) (by nlinarith) (by omega)
  rw [closure, minuend_two κ (k + 2) (by omega) le_rfl, subtrahend_one κ (k + 2) (by omega : 0 < k + 2),
    result_two κ (k + 2) (by omega) le_rfl] at D2
  have D3 := h' ((k + 2) * 1 + 1) 0 ((k + 2) * 1 + 1) (by omega) (by nlinarith) (by omega)
  rw [closure, minuend_two κ (k + 2) (by omega) le_rfl, subtrahend_one κ (k + 2) (by omega : 0 < k + 2),
    result_two κ (k + 2) (by omega) le_rfl] at D3
  have D4 := h' 1 1 0 le_rfl (by nlinarith) (by omega)
  rw [closure, minuend_one κ (k + 2) (by omega : 1 < k + 2), subtrahend_one κ (k + 2) (by omega : 1 < k + 2),
    result_one κ (k + 2) (by omega : 0 < k + 2)] at D4
  have D6 := h' ((k + 2) * 1 + 1) ((k + 2) * 1 + 1) 0 le_rfl (by nlinarith) (by omega)
  rw [closure, minuend_two κ (k + 2) (by omega) le_rfl, subtrahend_two κ (k + 2) (by omega) le_rfl,
    result_one κ (k + 2) (by omega : 0 < k + 2)] at D6
  have D7 := h' ((k + 2) * 1 + 0) 1 (k + 1) (by omega) (by nlinarith) (by omega)
  rw [closure, minuend_two κ (k + 2) (by omega) le_rfl, subtrahend_one κ (k + 2) (by omega : 1 < k + 2),
    result_one κ (k + 2) (by omega : k + 1 < k + 2)] at D7
  push_cast at D2 D3 D4 D6 D7 ⊢
  linear_combination 2 * D2 - 2 * D3 + D4 + D6 - 2 * D7

/-- §10's solution on the whole menu: `u ≡ u⁻ ≡ w ≡ 0`, `z ≡ s`, `z⁼ ≡ −s`, `v ≡ s b`, `u′ ≡ −s b`. -/
def ofScale (s : R) (b : ℕ) : DiffKey R := ⟨0, 0, -(s * b), s, -s, s * b, 0, s⟩

/-- Statement 7: where `2b = 0`, §10's solution closes every line `x − y = c` to `s (x − y − c)`. -/
theorem ofScale_closure (s : R) (hR : ((2 * b : ℕ) : R) = 0) (x y c : ℕ) :
    (ofScale s b).closure b x y c = s * ((x : R) - y - c) := by
  have hR' : 2 * (b : R) = 0 := by push_cast at hR; exact hR
  have hm : (ofScale s b).minuend b x = s * x := by
    unfold minuend
    split_ifs
    · simp only [ofScale]; ring
    · conv_rhs => rw [← Nat.div_add_mod x b]
      simp only [ofScale]; push_cast; ring
  have hs : (ofScale s b).subtrahend b y = -(s * y) := by
    unfold subtrahend
    split_ifs
    · simp only [ofScale]; ring
    · conv_rhs => rw [← Nat.div_add_mod y b]
      simp only [ofScale]; push_cast
      linear_combination (s * ((y / b : ℕ) : R)) * hR'
  have hr : (ofScale s b).result b c = -(s * c) := by
    unfold result
    split_ifs
    · rfl
    · conv_rhs => rw [← Nat.div_add_mod c b]
      simp only [ofScale]; push_cast; ring
  rw [closure, hm, hs, hr]
  ring

/-- Statement 7: a key with `s` a unit closes every true difference with `y ≤ x < b²` exactly where
`2b = 0`. -/
theorem exists_iff (hb : 2 ≤ b) :
    (∃ κ : DiffKey R, IsUnit κ.s ∧ ∀ x y, y ≤ x → x < b ^ 2 → κ.closure b x y (x - y) = 0) ↔
      ((2 * b : ℕ) : R) = 0 := by
  constructor
  · rintro ⟨κ, hs, h⟩
    have := κ.diff_necessity b hb h
    rw [mul_comm 2, mul_assoc, hs.mul_right_eq_zero] at this
    push_cast
    exact this
  · intro hR
    refine ⟨ofScale 1 b, isUnit_one, fun x y hxy _ => ?_⟩
    rw [ofScale_closure b 1 hR, Nat.cast_sub hxy]
    ring

/-- Statement 7: modulo `q`, such a key exists exactly when `q ∣ 2b`. -/
theorem zmod_exists_iff (q : ℕ) (hb : 2 ≤ b) :
    (∃ κ : DiffKey (ZMod q), IsUnit κ.s ∧
        ∀ x y, y ≤ x → x < b ^ 2 → κ.closure b x y (x - y) = 0) ↔ q ∣ 2 * b := by
  rw [exists_iff b hb, ZMod.natCast_eq_zero_iff]

/-- Statement 7: modulo 20 with `s = −1` the key is §10's: `θ(x, y) = −10x`, `θ(x, −) = −x`, `θ(x, =) = x`,
`θ(=, y) = 10y`, `ψ(d) = −d`, every other move `0`. -/
theorem twenty_moves : ofScale (-1 : ZMod 20) 10 = ⟨0, 0, 10, -1, 1, -10, 0, -1⟩ := by
  simp only [ofScale, DiffKey.mk.injEq]
  decide

/-- Statement 7: modulo 20 the key closes a line to `c − x + y`, a false line to `δ mod 20`. -/
theorem twenty_closure (x y c : ℕ) :
    (ofScale (-1 : ZMod 20) 10).closure 10 x y c = (c : ZMod 20) - x + y := by
  rw [ofScale_closure 10 (-1) (by decide)]
  ring

/-- §10's exact difference on the lines whose minuend has two places, in the record's gauge `s = −1`:
`θ(newline, y) = −2b y`, `θ(x, y) = b x`, `θ(x, −) = −x`, `θ(−, y) = 0`, `θ(x, =) = x`, `θ(=, y) = b y`. -/
def exact (b : ℕ) : DiffKey R := ⟨-(2 * b), 0, b, -1, 1, b, 0, -1⟩

/-- Statement 7: on a minuend of two places the exact key closes every line to `c − x + y`, over any ring. -/
theorem exact_closure {x : ℕ} (hx : b ≤ x) (y c : ℕ) :
    (exact b : DiffKey R).closure b x y c = (c : R) - x + y := by
  have hm : (exact b : DiffKey R).minuend b x = -(x : R) := by
    rw [minuend, if_neg (by omega)]
    conv_rhs => rw [← Nat.div_add_mod x b]
    simp only [exact]; push_cast; ring
  have hs : (exact b : DiffKey R).subtrahend b y = y := by
    unfold subtrahend
    split_ifs
    · simp only [exact]; ring
    · conv_rhs => rw [← Nat.div_add_mod y b]
      simp only [exact]; push_cast; ring
  have hr : (exact b : DiffKey R).result b c = c := by
    unfold result
    split_ifs
    · simp only [exact]; ring
    · conv_rhs => rw [← Nat.div_add_mod c b]
      simp only [exact]; push_cast; ring
  rw [closure, hm, hs, hr]
  ring

/-- Statement 7: on a one-place minuend the exact key is off by `2 b x`. -/
theorem exact_closure_one_place {x : ℕ} (hx : x < b) (y c : ℕ) :
    (exact b : DiffKey R).closure b x y c = (c : R) - x + y - 2 * b * x := by
  have hm : (exact b : DiffKey R).minuend b x = -(x : R) - 2 * b * x := by
    rw [minuend, if_pos hx]
    simp only [exact]; ring
  have hs : (exact b : DiffKey R).subtrahend b y = y := by
    unfold subtrahend
    split_ifs
    · simp only [exact]; ring
    · conv_rhs => rw [← Nat.div_add_mod y b]
      simp only [exact]; push_cast; ring
  have hr : (exact b : DiffKey R).result b c = c := by
    unfold result
    split_ifs
    · simp only [exact]; ring
    · conv_rhs => rw [← Nat.div_add_mod c b]
      simp only [exact]; push_cast; ring
  rw [closure, hm, hs, hr]
  ring

end DiffKey

end DiffKeys

end Holonics.Landmarks.ClosureKeyTorsion
