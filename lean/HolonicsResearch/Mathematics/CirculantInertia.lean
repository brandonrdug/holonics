import HolonicsResearch.Mathematics.RingSpectrum
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# A circulant's inertia is read by its windings

The box of #410 "`winding.circulant-inertia`, `winding.cyclotomic-null-test`,
`winding.hand-is-convention` (release through modes, #73)" owes the Lean statements of three atlas
rows (`docs/atlas/geometry.tsv`) whose only owner was the retired
`crates/holonics/src/geometry/winding_inertia.rs`
([history](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics/src/geometry/winding_inertia.rs),
removed at `d329cb541`). Its open paragraph: where a form carries a cyclic or circulant symmetry,
its inertia factors through the character group and every negative direction has a name, its
winding, so the return is the passages each labelled by how far it turns, never a count of signs.
The record `research/records/2026-08-18_THE_MONOID_IS_APERIODIC_BY_CONSTRUCTION_SO_THE_CRYSTAL_NEEDS_THE_TURN.md`
reads that owner as the one that returns inertia as windings, and the record of November 12 whose
name opens `2026-11-12_THE_LAW_ACROSS_A_PLACE_IS_HELD_BY_A_PUMPED_CONTACT_A_TRIAD_IS_A_CHARACTER`
cites the first row as "a circulant is diagonalized by the characters `ω^(jk)`". This file proves
the three rows on the ring `ℤ/n`, reusing the colours and the Fourier transform of
`Mathematics/OnePlaneRing` and `Mathematics/RingSpectrum`.

Orientation: `circ c` is the circulant with first row `c`, `(circ c)_(ij) = c_(j−i)`, the atlas's
`circ(c₀, …, c_(n−1))`. Mathlib's `Matrix.circulant c` has first column `c`; it is the transpose
(`circ_eq_transpose_circulant`) and reads colour `k` at `f(ω^(−k))` (`circulant_mulVec_colour`).

[proved-standard; formal-checked] What is proved.

1. **A circulant's eigenvalues are its symbol at the colours** (`eval_symbol`,
   `circ_mulVec_colour`, `colour_ne_zero`, `circ_mulVec_pow`, `circulant_mulVec_colour`). For any
   additive character `ψ` of `ℤ/n` into a commutative ring, the colour `v_k(j) = ψ(j k)` has
   `circ c · v_k = f(ψ(k)) v_k`, `f(x) = Σ_j c_j x^j` the symbol, and is nonzero over a nontrivial
   ring. For any `ω` with `ωⁿ = 1` (a primitive root among them), `v_k(j) = ω^(j k)` and
   `λ_k = f(ω^k)`.
2. **The Fourier transform diagonalizes every circulant** (`dft_circ`, `charpoly_circ`,
   `isPrimitiveRoot_stdAddChar_one`, `stdAddChar_eq_pow`): `𝓕(C v)(k) = f(ψ(k)) 𝓕v(k)`, so
   `det(x − C) = ∏_k (x − f(ψ(k)))`, with `ψ(1) = e^(2πi/n)` a primitive `n`-th root and
   `ψ(k) = ψ(1)^k`.
3. **A symmetric circulant reads through the cosines of multiples of the turn**
   (`eval_symbol_symm`, `sum_even_split`, `eigen_openHalf`, `eval_symbol_int_symm`). For real `c`
   with `c_(−j) = c_j`, `λ_k = Σ_j c_j cos(2π j k / n)` is real, and
   `λ_k = c₀ + Σ_(0 < 2m < n) c_m β_(mk) + [2 ∣ n] c_(n/2) (−1)^k` with the star values
   `β_m = 2cos(2πm/n)`: for integer `c`, an integer combination of star values.
4. **The cycle** (`eval_symbol_cycleAdj`, `cycleLaplacian_eq_circ`, `gapSq_eq_two_sub_beta`,
   `beta_neg_iff`, `beta_eq_zero_iff`, `beta_pos_iff`, `beta_neg_iff_step`,
   `exists_beta_eq_zero_iff`). The cycle adjacency `c = e₁ + e_(−1)` has `λ_k = β_k`; the cycle
   Laplacian of `RingSpectrum` is the circulant `2e₀ − c`, and its squared gap is `2 − β_k`. With
   `0 ≤ k < n`, `β_k < 0` exactly when `n < 4k < 3n` (the step `k/n` strictly between a quarter
   and three quarters of a turn), `β_k = 0` exactly when `4k = n` or `4k = 3n`, and a null passage
   exists exactly when `4 ∣ n`.
5. **The cyclotomic null test** (`isPrimitiveRoot_pow`, `aeval_eq_zero_iff_cyclotomic_dvd`,
   `aeval_eq_zero_iff_modByMonic`, `eq_cyclotomic_mul_divByMonic`, `eval_symbol_eq_zero_iff`). For
   `ζ` a primitive `n`-th root and `d = n / gcd(k, n)`, `ζ^k` is a primitive `d`-th root, and for
   `f ∈ ℚ[X]`, `f(ζ^k) = 0 ⟺ Φ_d ∣ f ⟺ f mod Φ_d = 0`, with `f = Φ_d · (f div Φ_d)` the witness.
   A rational circulant's passage `k` is null exactly when `Φ_(n / gcd(k, n))` divides its symbol:
   one polynomial division, never a limit.
6. **The hand is a convention** (`posSet_neg`, `nullSet_neg`, `negSet_neg`, `inertia_neg`,
   `partition_neg`, `inertia_card`, `circ_neg`, `symbol_neg`, `eval_symbol_neg`, `eigen_neg`,
   `inertia_eigen_neg`). The inertia `(p, z, q)` of a real reading on the colours counts the
   filters `λ_k > 0`, `= 0`, `< 0`, and the counts add to the number of colours. `−C` reads `−λ_k`
   at every colour, its inertia is `(q, z, p)`, and its three classes are the same set partition
   with the outer two exchanged.
7. **The witness `n = 8`** (`negSet_cycle_eight`, `nullSet_cycle_eight`, `posSet_cycle_eight`,
   `inertia_cycle_eight`, `cyclotomic_four_dvd_cycle_eight`): the cycle adjacency is null at
   `k = 2, 6`, negative at `k = 3, 4, 5`, positive at `k = 0, 1, 7`, inertia `(3, 2, 3)`; and the
   cyclotomic test reads the same null at `k = 2`: `Φ₄ ∣ X + X⁷`.

What is not claimed. The sign of a nonzero `λ_k` refined by Sturm's chain on `det(xI − C)`
(Faddeev–LeVerrier), the owner's certificate; the chain itself is `Mathematics/Sturm`. Niven's
rational star values (`winding.niven-star-values`) and the star table as the roots of
`D_n(x) − 2`. Circulants over other fields. Sylvester's law (congruence invariance of the split),
which the owner cross-checked against elimination; here the frame change is the hand alone.

The computational object is the helical pair interaction, read on a ring of `n` cells: every
pair contact at offset `j` carries the one weight `c_j`, so the coupling commutes with the turn of
the ring and its passages are the colours, the circle's turns read at step `k`. Of the winding
guide's six general objects this touches the helix (a colour is a point `ω^k` of the circle, and
its winding `k/n` names the passage), the pair (the contacts addressed by their offset `j − i`)
and faces and placement (the eigenvalue at a colour is a face, its sign placed by the quarter
turns); the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas rows `winding.circulant-inertia`, `winding.cyclotomic-null-test` and
`winding.hand-is-convention`.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Polynomial ZMod Complex Finset
open scoped ComplexConjugate

namespace Holonics.Mathematics.CirculantInertia

open Holonics.Mathematics.OnePlaneRing Holonics.Mathematics.RingSpectrum

variable {n : ℕ}

section Colours

variable {R : Type*}

/-- [definition] The circulant with first row `c`: `(circ c)_(ij) = c_(j−i)`. -/
def circ (c : ZMod n → R) : Matrix (ZMod n) (ZMod n) R := Matrix.of fun i j => c (j - i)

/-- [definition] The entry rule of `circ`. -/
theorem circ_apply (c : ZMod n → R) (i j : ZMod n) : circ c i j = c (j - i) := rfl

/-- [proved-standard; formal-checked] Mathlib's `circulant c` (first column `c`) is the transpose. -/
theorem circ_eq_transpose_circulant (c : ZMod n → R) : circ c = (Matrix.circulant c).transpose := by
  ext i j
  rfl

/-- [proved-standard; formal-checked] Mathlib's `circulant c` is `circ` of the reversed row. -/
theorem circulant_eq_circ [Neg R] (c : ZMod n → R) : Matrix.circulant c = circ fun j => c (-j) := by
  ext i j
  rw [Matrix.circulant_apply, circ_apply, neg_sub]

variable [CommRing R]

/-- [definition] The colour `k` under the character `ψ`: `v_k(j) = ψ(j k)`. -/
def colour (ψ : AddChar (ZMod n) R) (k : ZMod n) : ZMod n → R := fun j => ψ (j * k)

/-- [proved-standard; formal-checked] A colour is a nonzero vector: `v_k(0) = 1`. -/
theorem colour_ne_zero [Nontrivial R] (ψ : AddChar (ZMod n) R) (k : ZMod n) : colour ψ k ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [colour] at this

variable [NeZero n]

/-- [definition] The symbol `f(x) = Σ_j c_j x^j`, `j` read in `[0, n)`. -/
noncomputable def symbol (c : ZMod n → R) : R[X] := ∑ j, C (c j) * X ^ j.val

/-- [proved-standard; formal-checked] The symbol at a colour is `f(ψ(k)) = Σ_j c_j ψ(j k)`. -/
theorem eval_symbol (ψ : AddChar (ZMod n) R) (c : ZMod n → R) (k : ZMod n) :
    (symbol c).eval (ψ k) = ∑ j, c j * ψ (j * k) := by
  simp only [symbol, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine sum_congr rfl fun j _ => ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_zmod_val]

/-- [proved-standard; formal-checked] `(circ c · v)(i) = Σ_l c_l v(i + l)`. -/
theorem mulVec_circ (c : ZMod n → R) (v : ZMod n → R) (i : ZMod n) :
    (circ c).mulVec v i = ∑ l, c l * v (i + l) := by
  simp only [Matrix.mulVec, dotProduct, circ_apply]
  exact (Fintype.sum_equiv (Equiv.addLeft i) _ _ fun l => by simp).symm

/-- [proved-standard; formal-checked] **A circulant's eigenvalues are its symbol at the colours**:
`circ c · v_k = f(ψ(k)) v_k`. -/
theorem circ_mulVec_colour (ψ : AddChar (ZMod n) R) (c : ZMod n → R) (k : ZMod n) :
    (circ c).mulVec (colour ψ k) = (symbol c).eval (ψ k) • colour ψ k := by
  funext i
  rw [mulVec_circ, eval_symbol, Pi.smul_apply, smul_eq_mul, sum_mul]
  refine sum_congr rfl fun l _ => ?_
  simp only [colour, add_mul, AddChar.map_add_eq_mul]
  ring

/-- [proved-standard; formal-checked] Mathlib's orientation: `circulant c · v_k = f(ψ(−k)) v_k`. -/
theorem circulant_mulVec_colour (ψ : AddChar (ZMod n) R) (c : ZMod n → R) (k : ZMod n) :
    (Matrix.circulant c).mulVec (colour ψ k) = (symbol c).eval (ψ (-k)) • colour ψ k := by
  rw [circulant_eq_circ, circ_mulVec_colour, eval_symbol, eval_symbol]
  congr 1
  exact Fintype.sum_equiv (Equiv.neg _) _ _ fun j => by simp [neg_mul, mul_neg]

/-- [proved-standard; formal-checked] **At a root of unity**: for `ωⁿ = 1`, the vector
`v_k(j) = ω^(j k)` has `circ c · v_k = f(ω^k) v_k`. -/
theorem circ_mulVec_pow (c : ZMod n → R) {ω : R} (hω : ω ^ n = 1) (k : ZMod n) :
    (circ c).mulVec (fun j => ω ^ (j.val * k.val)) =
      (symbol c).eval (ω ^ k.val) • fun j => ω ^ (j.val * k.val) := by
  have hv : (fun j : ZMod n => ω ^ (j.val * k.val)) = colour (AddChar.zmodChar n hω) k := by
    funext j
    rw [colour, AddChar.zmodChar_apply, ZMod.val_mul, ← pow_eq_pow_mod _ hω]
  rw [hv, ← AddChar.zmodChar_apply hω, circ_mulVec_colour]

end Colours

section Fourier

variable [NeZero n]

/-- [proved-standard; formal-checked] `ψ(k) = ψ(1)^k`. -/
theorem stdAddChar_eq_pow (k : ZMod n) :
    (stdAddChar k : ℂ) = (stdAddChar (1 : ZMod n)) ^ k.val := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_one, natCast_zmod_val]

/-- [proved-standard; formal-checked] `ψ(1) = e^(2πi/n)` is a primitive `n`-th root of unity. -/
theorem isPrimitiveRoot_stdAddChar_one : IsPrimitiveRoot (stdAddChar (1 : ZMod n) : ℂ) n := by
  refine ⟨?_, fun l hl => ?_⟩
  · rw [← AddChar.map_nsmul_eq_pow, nsmul_one, natCast_self, AddChar.map_zero_eq_one]
  · rw [← AddChar.map_nsmul_eq_pow, nsmul_one, ← AddChar.map_zero_eq_one (stdAddChar (N := n))] at hl
    exact (natCast_eq_zero_iff l n).mp (injective_stdAddChar hl)

/-- [proved-standard; formal-checked] **The colours diagonalize every circulant**: the Fourier
transform carries `circ c` to multiplication by `f(ψ(k))`. -/
theorem dft_circ (c : ZMod n → ℂ) (v : ZMod n → ℂ) (k : ZMod n) :
    𝓕 ((circ c).mulVec v) k = (symbol c).eval (stdAddChar k) * 𝓕 v k := by
  have hv : (circ c).mulVec v = ∑ l, c l • fun i => v (i + l) := by
    funext i
    rw [mulVec_circ, Finset.sum_apply]
    rfl
  rw [hv, map_sum, Finset.sum_apply, eval_symbol, sum_mul]
  refine sum_congr rfl fun l _ => ?_
  rw [_root_.map_smul, Pi.smul_apply, dft_comp_add, smul_eq_mul, smul_eq_mul, mul_comm l k]
  ring

/-- [proved-standard; formal-checked] **A circulant's characteristic polynomial**:
`det(x − circ c) = ∏_k (x − f(ψ(k)))`. -/
theorem charpoly_circ (c : ZMod n → ℂ) :
    (circ c).charpoly = ∏ k : ZMod n, (X - C ((symbol c).eval (stdAddChar k))) := by
  rw [← Matrix.charpoly_diagonal, ← Matrix.charpoly_toLin',
    ← Matrix.charpoly_toLin' (Matrix.diagonal _),
    ← LinearEquiv.charpoly_conj (dft (N := n) (E := ℂ))]
  congr 1
  refine LinearMap.ext fun w => ?_
  funext k
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  change 𝓕 ((circ c).mulVec (dft.symm w)) k = _
  rw [dft_circ, LinearEquiv.apply_symm_apply]

end Fourier

section Symmetric

variable [NeZero n]

/-- [definition] The star value `β_m = 2cos(2πm/n)`. -/
noncomputable def beta (n m : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * m / n)

/-- [proved-standard; formal-checked] `Re ψ(m) = cos(2πm/n)`. -/
theorem re_stdAddChar_natCast (m : ℕ) :
    (stdAddChar (m : ZMod n) : ℂ).re = Real.cos (2 * Real.pi * m / n) := by
  rw [stdAddChar_apply, toCircle_natCast,
    show (2 * (Real.pi : ℂ) * I * m / n) = ((2 * Real.pi * m / n : ℝ) : ℂ) * I by push_cast; ring,
    exp_ofReal_mul_I_re]

/-- [proved-standard; formal-checked] A colour and its mirror add to the star value:
`ψ(m) + ψ(−m) = β_m`. -/
theorem stdAddChar_add_neg (m : ℕ) :
    (stdAddChar (m : ZMod n) : ℂ) + stdAddChar (-(m : ZMod n)) = (beta n m : ℂ) := by
  rw [AddChar.map_neg_eq_conj, Complex.add_conj, re_stdAddChar_natCast, beta]

/-- [proved-standard; formal-checked] `j k` read through the residues in `[0, n)`. -/
theorem mul_eq_natCast (j k : ZMod n) : j * k = ((j.val * k.val : ℕ) : ZMod n) := by
  push_cast
  rw [natCast_zmod_val, natCast_zmod_val]

/-- [definition] The real eigenvalue at colour `k` of a symmetric real circulant:
`Σ_j c_j cos(2π j k / n)`. -/
noncomputable def eigen (c : ZMod n → ℝ) (k : ZMod n) : ℝ :=
  ∑ j, c j * Real.cos (2 * Real.pi * (j.val * k.val : ℕ) / n)

/-- [proved-standard; formal-checked] **A symmetric circulant's eigenvalues are real**: for
`c_(−j) = c_j`, `f(ψ(k)) = Σ_j c_j cos(2π j k / n)`. -/
theorem eval_symbol_symm (c : ZMod n → ℝ) (hc : ∀ j, c (-j) = c j) (k : ZMod n) :
    (symbol fun j => (c j : ℂ)).eval (stdAddChar k) = (eigen c k : ℂ) := by
  rw [eval_symbol]
  have hre : ∀ j : ZMod n, (stdAddChar (j * k) : ℂ) + stdAddChar (-(j * k)) =
      2 * (Real.cos (2 * Real.pi * (j.val * k.val : ℕ) / n) : ℂ) := fun j => by
    rw [mul_eq_natCast, stdAddChar_add_neg, beta]
    push_cast
    ring
  have hneg : ∑ j, (c j : ℂ) * stdAddChar (j * k) = ∑ j, (c j : ℂ) * stdAddChar (-(j * k)) :=
    Fintype.sum_equiv (Equiv.neg _) _ _ fun j => by simp [hc, neg_mul]
  have h2 : 2 * ∑ j, (c j : ℂ) * stdAddChar (j * k) = 2 * (eigen c k : ℂ) := by
    rw [two_mul]
    nth_rewrite 2 [hneg]
    rw [← sum_add_distrib, eigen, Complex.ofReal_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_add, hre, Complex.ofReal_mul]
    ring
  exact mul_left_cancel₀ two_ne_zero h2

/-- [definition] The colours strictly inside the first half turn, `0 < 2m < n`. -/
def openHalf (n : ℕ) [NeZero n] : Finset (ZMod n) := univ.filter fun j => 0 < j.val ∧ 2 * j.val < n

/-- [proved-standard; formal-checked] **A mirror-even sum folds onto the half turn**: for
`h(−j) = h(j)`, `Σ_j h(j) = h(0) + 2 Σ_(0 < 2j < n) h(j) + Σ_(2j = n) h(j)`. -/
theorem sum_even_split {M : Type*} [AddCommMonoid M] (h : ZMod n → M) (hh : ∀ j, h (-j) = h j) :
    ∑ j, h j = h 0 + 2 • ∑ j ∈ openHalf n, h j +
      ∑ j ∈ univ.filter (fun j : ZMod n => 2 * j.val = n), h j := by
  have hn := NeZero.ne n
  have hpt : ∀ j : ZMod n, h j = (if j.val = 0 then h j else 0) +
      (if 0 < j.val ∧ 2 * j.val < n then h j else 0) + (if 2 * j.val = n then h j else 0) +
      (if n < 2 * j.val then h j else 0) := fun j => by
    split_ifs <;> first | (exfalso; omega) | simp
  have h0 : univ.filter (fun j : ZMod n => j.val = 0) = {0} := by
    ext j
    simp [ZMod.val_eq_zero]
  have hT : ∑ j ∈ univ.filter (fun j : ZMod n => n < 2 * j.val), h j = ∑ j ∈ openHalf n, h j := by
    refine sum_nbij' (fun j => -j) (fun j => -j) (fun j hj => ?_) (fun j hj => ?_)
      (fun j _ => neg_neg j) (fun j _ => neg_neg j) (fun j _ => (hh j).symm)
    · simp only [openHalf, mem_filter, mem_univ, true_and] at hj ⊢
      have hj0 : j ≠ 0 := by
        rintro rfl
        simp at hj
      rw [ZMod.neg_val, if_neg hj0]
      have := ZMod.val_lt j
      omega
    · simp only [openHalf, mem_filter, mem_univ, true_and] at hj ⊢
      have hj0 : j ≠ 0 := by
        rintro rfl
        simp at hj
      rw [ZMod.neg_val, if_neg hj0]
      omega
  rw [sum_congr rfl fun j _ => hpt j]
  simp only [sum_add_distrib, ← sum_filter]
  rw [h0, sum_singleton, hT, openHalf, two_nsmul]
  abel

/-- [proved-standard; formal-checked] `cos(2π j k / n) = Re ψ(j k)`. -/
theorem cos_eq_re (j k : ZMod n) :
    Real.cos (2 * Real.pi * (j.val * k.val : ℕ) / n) = (stdAddChar (j * k) : ℂ).re := by
  rw [mul_eq_natCast j k, re_stdAddChar_natCast]

/-- [proved-standard; formal-checked] The half-turn colour `2m = n` exists exactly when `n` is
even, and it is `n/2`. -/
theorem filter_half_turn :
    univ.filter (fun j : ZMod n => 2 * j.val = n) =
      if 2 ∣ n then {((n / 2 : ℕ) : ZMod n)} else ∅ := by
  have hn := NeZero.pos n
  ext j
  simp only [mem_filter, mem_univ, true_and]
  split_ifs with h2
  · rw [mem_singleton]
    constructor
    · intro hj
      rw [← natCast_zmod_val j]
      congr 1
      omega
    · rintro rfl
      rw [ZMod.val_cast_of_lt (by omega)]
      omega
  · simp only [notMem_empty, iff_false]
    omega

/-- [proved-standard; formal-checked] **A symmetric circulant reads through the star values**:
`λ_k = c₀ + Σ_(0 < 2m < n) c_m β_(mk) + [2 ∣ n] c_(n/2) (−1)^k`. -/
theorem eigen_openHalf (c : ZMod n → ℝ) (hc : ∀ j, c (-j) = c j) (k : ZMod n) :
    eigen c k = c 0 + ∑ j ∈ openHalf n, c j * beta n (j.val * k.val) +
      if 2 ∣ n then c ((n / 2 : ℕ) : ZMod n) * (-1) ^ k.val else 0 := by
  have hh : ∀ j : ZMod n, c (-j) * Real.cos (2 * Real.pi * ((-j).val * k.val : ℕ) / n) =
      c j * Real.cos (2 * Real.pi * (j.val * k.val : ℕ) / n) := fun j => by
    rw [hc, cos_eq_re, cos_eq_re, neg_mul, AddChar.map_neg_eq_conj, Complex.conj_re]
  rw [eigen, sum_even_split _ hh, filter_half_turn]
  congr 1
  · congr 1
    · simp
    · rw [smul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [two_nsmul, beta]
      ring
  · split_ifs with h2
    · rw [sum_singleton]
      have hn2 : n = 2 * (n / 2) := (Nat.mul_div_cancel' h2).symm
      have hpos : 0 < n / 2 := by
        have := NeZero.pos n
        omega
      rw [ZMod.val_cast_of_lt (by omega)]
      congr 1
      rw [← Real.cos_nat_mul_pi]
      congr 1
      rw [show (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) by exact_mod_cast hn2]
      have : ((n / 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      push_cast
      field_simp
    · rw [sum_empty]

/-- [proved-standard; formal-checked] **An integer symmetric circulant's eigenvalue is an integer
combination of star values**, read at colour `k`. -/
theorem eval_symbol_int_symm (c : ZMod n → ℤ) (hc : ∀ j, c (-j) = c j) (k : ZMod n) :
    (symbol fun j => (c j : ℂ)).eval (stdAddChar k) =
      (((c 0 : ℝ) + ∑ j ∈ openHalf n, (c j : ℝ) * beta n (j.val * k.val) +
        if 2 ∣ n then (c ((n / 2 : ℕ) : ZMod n) : ℝ) * (-1) ^ k.val else 0 : ℝ) : ℂ) := by
  have e : (fun j => (c j : ℂ)) = fun j => (((c j : ℝ)) : ℂ) :=
    funext fun j => (Complex.ofReal_intCast _).symm
  have hc' : ∀ j, (c (-j) : ℝ) = c j := fun j => by rw [hc]
  rw [e, eval_symbol_symm _ hc', eigen_openHalf _ hc']

end Symmetric

section Cycle

/-- [definition] The cycle adjacency's first row, `e₁ + e_(−1)`. -/
def cycleAdj (n : ℕ) : ZMod n → ℤ := fun j => (if j = 1 then 1 else 0) + (if j = -1 then 1 else 0)

/-- [proved-standard; formal-checked] The cycle Laplacian of `RingSpectrum` is the circulant
`2e₀ − e₁ − e_(−1)`. -/
theorem cycleLaplacian_eq_circ :
    cycleLaplacian n = circ fun j => (if j = 0 then 2 else 0) - cycleAdj n j := by
  ext i j
  have h1 : j - i = 1 ↔ j = i + 1 := sub_eq_iff_eq_add'
  have h2 : j - i = -1 ↔ j = i - 1 := by
    rw [sub_eq_iff_eq_add', ← sub_eq_add_neg]
  simp only [cycleLaplacian, circ_apply, cycleAdj, sub_eq_zero, h1, h2]
  ring

/-- [proved-standard; formal-checked] The cycle adjacency is symmetric. -/
theorem cycleAdj_neg (j : ZMod n) : cycleAdj n (-j) = cycleAdj n j := by
  simp only [cycleAdj, neg_eq_iff_eq_neg, neg_neg]
  rw [add_comm]

variable [NeZero n]

/-- [proved-standard; formal-checked] **The cycle's eigenvalues are the star values**:
`λ_k = ψ(k) + ψ(−k) = β_k`. -/
theorem eval_symbol_cycleAdj (k : ZMod n) :
    (symbol fun j => (cycleAdj n j : ℂ)).eval (stdAddChar k) = (beta n k.val : ℂ) := by
  rw [eval_symbol]
  simp only [cycleAdj, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero, add_mul, ite_mul,
    one_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_univ, if_true, neg_one_mul]
  have := stdAddChar_add_neg (n := n) k.val
  rwa [natCast_zmod_val] at this

/-- [proved-standard; formal-checked] The ring's squared gap is two less the star value:
`2 − ψ(k) − ψ(−k) = 2 − β_k`. -/
theorem gapSq_eq_two_sub_beta (k : ZMod n) : gapSq k = 2 - (beta n k.val : ℂ) := by
  have := stdAddChar_add_neg (n := n) k.val
  rw [natCast_zmod_val] at this
  rw [gapSq, ← this]
  ring

end Cycle

section Sign

/-- [proved-standard; formal-checked] `β_m > 0` inside a quarter turn of `0`. -/
theorem beta_pos_of {n m : ℕ} (hm : m < n) (h : 4 * m < n ∨ 3 * n < 4 * m) : 0 < beta n m := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpi := Real.pi_pos
  have hmn : (m : ℝ) < n := by exact_mod_cast hm
  unfold beta
  apply mul_pos two_pos
  rcases h with h | h
  · have h' : (4 * m : ℝ) < n := by exact_mod_cast h
    have h0 : 0 ≤ 2 * Real.pi * m / n := by positivity
    have h1 : 2 * Real.pi * m / n < Real.pi / 2 := by
      rw [div_lt_iff₀ hn]
      nlinarith
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  · have h' : (3 * n : ℝ) < 4 * m := by exact_mod_cast h
    have h0 : -(Real.pi / 2) + 2 * Real.pi < 2 * Real.pi * m / n := by
      rw [lt_div_iff₀ hn]
      nlinarith
    have h1 : 2 * Real.pi * m / n < 2 * Real.pi := by
      rw [div_lt_iff₀ hn]
      nlinarith
    rw [← Real.cos_sub_two_pi]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/-- [proved-standard; formal-checked] `β_m = 0` at a quarter and at three quarters of a turn. -/
theorem beta_eq_zero_of {n m : ℕ} (hn0 : 0 < n) (h : 4 * m = n ∨ 4 * m = 3 * n) :
    beta n m = 0 := by
  have hn : (n : ℝ) ≠ 0 := by positivity
  unfold beta
  rcases h with h | h
  · have e : (4 * m : ℝ) = n := by exact_mod_cast h
    have : 2 * Real.pi * m / n = Real.pi / 2 := by
      rw [div_eq_iff hn]
      linear_combination (Real.pi / 2) * e
    rw [this, Real.cos_pi_div_two, mul_zero]
  · have e : (4 * m : ℝ) = 3 * n := by exact_mod_cast h
    have : 2 * Real.pi * m / n = Real.pi / 2 + Real.pi := by
      rw [div_eq_iff hn]
      linear_combination (Real.pi / 2) * e
    rw [this, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero, mul_zero]

/-- [proved-standard; formal-checked] `β_m < 0` strictly between a quarter and three quarters. -/
theorem beta_neg_of {n m : ℕ} (h : n < 4 * m ∧ 4 * m < 3 * n) : beta n m < 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpi := Real.pi_pos
  have h1 : (n : ℝ) < 4 * m := by exact_mod_cast h.1
  have h2 : (4 * m : ℝ) < 3 * n := by exact_mod_cast h.2
  unfold beta
  have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2 * Real.pi * m / n)
    (by rw [lt_div_iff₀ hn]; nlinarith) (by rw [div_lt_iff₀ hn]; nlinarith)
  linarith

/-- [proved-standard; formal-checked] **The passage is negative exactly past the quarter turn**:
for `0 ≤ m < n`, `β_m < 0 ⟺ n < 4m < 3n`. -/
theorem beta_neg_iff {n m : ℕ} (hm : m < n) : beta n m < 0 ↔ n < 4 * m ∧ 4 * m < 3 * n := by
  refine ⟨fun h => ?_, beta_neg_of⟩
  by_contra hc
  rcases (by omega : (4 * m < n ∨ 3 * n < 4 * m) ∨ (4 * m = n ∨ 4 * m = 3 * n)) with h' | h'
  · linarith [beta_pos_of hm h']
  · linarith [beta_eq_zero_of (by omega) h']

/-- [proved-standard; formal-checked] **The null passages sit at the quarter turns**: for
`0 ≤ m < n`, `β_m = 0 ⟺ 4m = n ∨ 4m = 3n`. -/
theorem beta_eq_zero_iff {n m : ℕ} (hm : m < n) : beta n m = 0 ↔ 4 * m = n ∨ 4 * m = 3 * n := by
  refine ⟨fun h => ?_, beta_eq_zero_of (by omega)⟩
  by_contra hc
  rcases (by omega : (4 * m < n ∨ 3 * n < 4 * m) ∨ (n < 4 * m ∧ 4 * m < 3 * n)) with h' | h'
  · linarith [beta_pos_of hm h']
  · linarith [beta_neg_of h']

/-- [proved-standard; formal-checked] For `0 ≤ m < n`, `β_m > 0 ⟺ 4m < n ∨ 3n < 4m`. -/
theorem beta_pos_iff {n m : ℕ} (hm : m < n) : 0 < beta n m ↔ 4 * m < n ∨ 3 * n < 4 * m := by
  refine ⟨fun h => ?_, beta_pos_of hm⟩
  by_contra hc
  rcases (by omega : (4 * m = n ∨ 4 * m = 3 * n) ∨ (n < 4 * m ∧ 4 * m < 3 * n)) with h' | h'
  · linarith [beta_eq_zero_of (by omega) h']
  · linarith [beta_neg_of h']

/-- [proved-standard; formal-checked] The same, read on the step: `β_m < 0` exactly when
`m/n ∈ (1/4, 3/4)`. -/
theorem beta_neg_iff_step {n m : ℕ} (hm : m < n) :
    beta n m < 0 ↔ 1 / 4 < (m / n : ℝ) ∧ (m / n : ℝ) < 3 / 4 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [beta_neg_iff hm, lt_div_iff₀ hn, div_lt_iff₀ hn]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (n : ℝ) < 4 * m := by exact_mod_cast h1
    have h2' : (4 * m : ℝ) < 3 * n := by exact_mod_cast h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor
    · have : (n : ℝ) < 4 * m := by linarith
      exact_mod_cast this
    · have : (4 * m : ℝ) < 3 * n := by linarith
      exact_mod_cast this

/-- [proved-standard; formal-checked] **The cycle has a null passage exactly when `4 ∣ n`.** -/
theorem exists_beta_eq_zero_iff [NeZero n] : (∃ k : ZMod n, beta n k.val = 0) ↔ 4 ∣ n := by
  constructor
  · rintro ⟨k, hk⟩
    rcases (beta_eq_zero_iff (ZMod.val_lt k)).mp hk with h | h <;> omega
  · intro h4
    have := NeZero.pos n
    refine ⟨((n / 4 : ℕ) : ZMod n), ?_⟩
    rw [ZMod.val_cast_of_lt (by omega)]
    exact beta_eq_zero_of this (Or.inl (by omega))

end Sign

section Cyclotomic

/-- [proved-standard; formal-checked] For `ζ` a primitive `n`-th root, `ζ^k` is a primitive
`n / gcd(k, n)`-th root. -/
theorem isPrimitiveRoot_pow {M : Type*} [CommMonoid M] {ζ : M} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (k : ℕ) : IsPrimitiveRoot (ζ ^ k) (n / Nat.gcd k n) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, Nat.gcd_zero_left, Nat.div_self hn]
    exact IsPrimitiveRoot.one
  · rw [Nat.gcd_comm, hζ.eq_orderOf, ← orderOf_pow' ζ hk.ne']
    exact IsPrimitiveRoot.orderOf _

/-- [proved-standard; formal-checked] **The cyclotomic null test**: `f(ζ^k) = 0 ⟺ Φ_d ∣ f`,
`d = n / gcd(k, n)`. -/
theorem aeval_eq_zero_iff_cyclotomic_dvd (f : ℚ[X]) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (k : ℕ) : aeval (ζ ^ k) f = 0 ↔ cyclotomic (n / Nat.gcd k n) ℚ ∣ f := by
  have hd : 0 < n / Nat.gcd k n :=
    Nat.div_pos (Nat.gcd_le_right _ hn) (Nat.gcd_pos_of_pos_right _ hn)
  rw [cyclotomic_eq_minpoly_rat (isPrimitiveRoot_pow hζ hn k) hd, minpoly.dvd_iff]

/-- [proved-standard; formal-checked] **One polynomial division decides it**:
`f(ζ^k) = 0 ⟺ f mod Φ_d = 0`. -/
theorem aeval_eq_zero_iff_modByMonic (f : ℚ[X]) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (k : ℕ) : aeval (ζ ^ k) f = 0 ↔ f %ₘ cyclotomic (n / Nat.gcd k n) ℚ = 0 := by
  rw [aeval_eq_zero_iff_cyclotomic_dvd f hζ hn k, modByMonic_eq_zero_iff_dvd (cyclotomic.monic _ ℚ)]

/-- [proved-standard; formal-checked] **The quotient is the witness**: a null passage gives
`f = Φ_d · (f div Φ_d)`. -/
theorem eq_cyclotomic_mul_divByMonic (f : ℚ[X]) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (k : ℕ) (h : aeval (ζ ^ k) f = 0) :
    f = cyclotomic (n / Nat.gcd k n) ℚ * (f /ₘ cyclotomic (n / Nat.gcd k n) ℚ) := by
  have := modByMonic_add_div f (cyclotomic (n / Nat.gcd k n) ℚ)
  rw [(aeval_eq_zero_iff_modByMonic f hζ hn k).mp h, zero_add] at this
  exact this.symm

variable [NeZero n]

/-- [proved-standard; formal-checked] A rational symbol read in `ℂ` is the symbol of the read row. -/
theorem map_symbol (c : ZMod n → ℚ) :
    (symbol c).map (algebraMap ℚ ℂ) = symbol fun j => (c j : ℂ) := by
  simp [symbol, Polynomial.map_sum]

/-- [proved-standard; formal-checked] **A rational circulant's null passages**: colour `k` reads
zero exactly when `Φ_(n / gcd(k, n))` divides the symbol. -/
theorem eval_symbol_eq_zero_iff (c : ZMod n → ℚ) (k : ZMod n) :
    (symbol fun j => (c j : ℂ)).eval (stdAddChar k) = 0 ↔
      cyclotomic (n / Nat.gcd k.val n) ℚ ∣ symbol c := by
  rw [← map_symbol, eval_map_algebraMap, stdAddChar_eq_pow]
  exact aeval_eq_zero_iff_cyclotomic_dvd _ isPrimitiveRoot_stdAddChar_one (NeZero.pos n) k.val

end Cyclotomic

section Inertia

variable {ι : Type*} [Fintype ι]

/-- [definition] The colours a real reading places on the positive side. -/
noncomputable def posSet (l : ι → ℝ) : Finset ι := univ.filter fun k => 0 < l k

/-- [definition] The colours a real reading leaves null. -/
noncomputable def nullSet (l : ι → ℝ) : Finset ι := univ.filter fun k => l k = 0

/-- [definition] The colours a real reading places on the negative side. -/
noncomputable def negSet (l : ι → ℝ) : Finset ι := univ.filter fun k => l k < 0

/-- [definition] The inertia `(p, z, q)`: the counts of the three classes. -/
noncomputable def inertia (l : ι → ℝ) : ℕ × ℕ × ℕ :=
  ((posSet l).card, (nullSet l).card, (negSet l).card)

/-- [proved-standard; formal-checked] Negation carries the positive class to the negative one. -/
theorem posSet_neg (l : ι → ℝ) : posSet (-l) = negSet l :=
  filter_congr fun k _ => by rw [Pi.neg_apply, neg_pos]

/-- [proved-standard; formal-checked] Negation keeps the null class. -/
theorem nullSet_neg (l : ι → ℝ) : nullSet (-l) = nullSet l :=
  filter_congr fun k _ => by rw [Pi.neg_apply, neg_eq_zero]

/-- [proved-standard; formal-checked] Negation carries the negative class to the positive one. -/
theorem negSet_neg (l : ι → ℝ) : negSet (-l) = posSet l :=
  filter_congr fun k _ => by rw [Pi.neg_apply, neg_lt_zero]

/-- [proved-standard; formal-checked] **The hand swaps the counts**: the inertia of `−λ` is
`(q, z, p)`. -/
theorem inertia_neg (l : ι → ℝ) :
    inertia (-l) = ((inertia l).2.2, (inertia l).2.1, (inertia l).1) := by
  rw [inertia, inertia, posSet_neg, nullSet_neg, negSet_neg]

/-- [proved-standard; formal-checked] **The split is not the hand's**: `λ` and `−λ` partition the
colours into the same three classes. -/
theorem partition_neg [DecidableEq ι] (l : ι → ℝ) :
    ({posSet (-l), nullSet (-l), negSet (-l)} : Finset (Finset ι)) =
      {posSet l, nullSet l, negSet l} := by
  rw [posSet_neg, nullSet_neg, negSet_neg]
  ext s
  simp only [mem_insert, mem_singleton]
  tauto

/-- [proved-standard; formal-checked] The three classes cover the colours: `p + z + q = |ι|`. -/
theorem inertia_card (l : ι → ℝ) :
    (inertia l).1 + (inertia l).2.1 + (inertia l).2.2 = Fintype.card ι := by
  simp only [inertia, posSet, nullSet, negSet, card_filter, ← sum_add_distrib]
  rw [Fintype.card_eq_sum_ones]
  refine sum_congr rfl fun k _ => ?_
  rcases lt_trichotomy (l k) 0 with h | h | h
  · simp [h, h.ne, lt_asymm h]
  · simp [h]
  · simp [h, h.ne', lt_asymm h]

end Inertia

section Hand

variable {R : Type*} [CommRing R]

/-- [proved-standard; formal-checked] `circ(−c) = −circ c`. -/
theorem circ_neg (c : ZMod n → R) : circ (-c) = -circ c := by
  ext i j
  rfl

variable [NeZero n]

/-- [proved-standard; formal-checked] The symbol of `−c` is `−f`. -/
theorem symbol_neg (c : ZMod n → R) : symbol (-c) = -symbol c := by
  simp [symbol, ← sum_neg_distrib]

/-- [proved-standard; formal-checked] **`−C` reads `−λ_k` at every colour.** -/
theorem eval_symbol_neg (ψ : AddChar (ZMod n) R) (c : ZMod n → R) (k : ZMod n) :
    (symbol (-c)).eval (ψ k) = -(symbol c).eval (ψ k) := by
  rw [symbol_neg, eval_neg]

/-- [proved-standard; formal-checked] The real eigenvalues of `−c` are `−λ_k`. -/
theorem eigen_neg (c : ZMod n → ℝ) : eigen (-c) = -eigen c := by
  funext k
  simp [eigen, ← sum_neg_distrib, neg_mul]

/-- [proved-standard; formal-checked] **The hand is a convention**: a symmetric real circulant and
its negation have inertia `(p, z, q)` and `(q, z, p)`. -/
theorem inertia_eigen_neg (c : ZMod n → ℝ) :
    inertia (eigen (-c)) = ((inertia (eigen c)).2.2, (inertia (eigen c)).2.1, (inertia (eigen c)).1) := by
  rw [eigen_neg, inertia_neg]

end Hand

section Eight

/-- [proved-standard; formal-checked] The `8`-cycle is negative at `k = 3, 4, 5`. -/
theorem negSet_cycle_eight : negSet (fun k : ZMod 8 => beta 8 k.val) = {3, 4, 5} := by
  rw [negSet, filter_congr fun k _ => beta_neg_iff (ZMod.val_lt k)]
  decide

/-- [proved-standard; formal-checked] The `8`-cycle is null at `k = 2, 6`. -/
theorem nullSet_cycle_eight : nullSet (fun k : ZMod 8 => beta 8 k.val) = {2, 6} := by
  rw [nullSet, filter_congr fun k _ => beta_eq_zero_iff (ZMod.val_lt k)]
  decide

/-- [proved-standard; formal-checked] The `8`-cycle is positive at `k = 0, 1, 7`. -/
theorem posSet_cycle_eight : posSet (fun k : ZMod 8 => beta 8 k.val) = {0, 1, 7} := by
  rw [posSet, filter_congr fun k _ => beta_pos_iff (ZMod.val_lt k)]
  decide

/-- [proved-standard; formal-checked] **The `8`-cycle's inertia is `(3, 2, 3)`.** -/
theorem inertia_cycle_eight : inertia (fun k : ZMod 8 => beta 8 k.val) = (3, 2, 3) := by
  rw [inertia, posSet_cycle_eight, nullSet_cycle_eight, negSet_cycle_eight]
  rfl

/-- [proved-standard; formal-checked] **The two routes agree at `k = 2`**: the cyclotomic test reads
the `8`-cycle's null passage as `Φ₄ ∣ X + X⁷`. -/
theorem cyclotomic_four_dvd_cycle_eight :
    cyclotomic 4 ℚ ∣ symbol fun j : ZMod 8 => (cycleAdj 8 j : ℚ) := by
  have h := (eval_symbol_eq_zero_iff (fun j : ZMod 8 => (cycleAdj 8 j : ℚ)) 2).mp ?_
  · exact h
  · have e : (fun j : ZMod 8 => (((cycleAdj 8 j : ℚ)) : ℂ)) = fun j => (cycleAdj 8 j : ℂ) :=
      funext fun j => Rat.cast_intCast _
    rw [e, eval_symbol_cycleAdj]
    exact_mod_cast beta_eq_zero_of (by norm_num) (Or.inl (by decide))

end Eight

end Holonics.Mathematics.CirculantInertia
