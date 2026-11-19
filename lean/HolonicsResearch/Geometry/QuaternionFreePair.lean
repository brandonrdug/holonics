import Mathlib.Algebra.Quaternion
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two coupled planes carry order: the turns by `1 + 2i` and `1 + 2j` are free in SO(3)

Source: #410's box "Two coupled planes carry order", from the record of October 22 on order as torsion, §6.6: reflections
chosen in one plane collapse (two plane turns commute, so a word reads only its parity and a signed phase sum), while
"the turns by the norm-5 quaternions `1 + 2i` and `1 + 2j` already generate a free group in SO(3)", so pump phases chosen
by the symbol on a chain of at least two coupled rings read the symbols' order.

[proved-standard; formal-checked] What is proved.

1. **The letters** (§1). Over any commutative ring the four letters `1 ± 2i`, `1 ± 2j` (`letter`) have norm five
   (`normSq_letter`), each letter's conjugate is the letter of the opposite sign (`star_letter`), and a ring map carries
   letters to letters (`qmap_letter`, with `qmap` the quaternions' map of a ring map).
2. **Rank one modulo five** (§2). In `ℍ[ZMod 5]` every letter has norm zero. For any quaternions
   `y m y = (2 Re(y m)) y − N(y) m̄` (`mul_mul_self`), so for `N(x) = 0` and `x y ≠ 0` the left annihilator of `x y` is
   that of `x` (`mul_eq_zero_of_mul_mul`): the norm-zero quaternions modulo five behave as rank-one matrices. Two letters
   multiply to a quaternion with nonzero real part unless they are inverse (`letter_mul_letter_re_ne_zero`), so the
   product of a reduced word has the left annihilator of its first letter (`annihilator_prod`) and is not zero
   (`prod_letter_ne_zero`).
3. **No reduced word is real** (§3). Over `ℤ` the product `P` of a nonempty reduced word has norm `5ⁿ`
   (`normSq_prod_letter`); were it real, `P² = 5ⁿ` with `n ≥ 1` would make five divide it, and its reduction modulo
   five would vanish. So it has a nonzero imaginary part (`prod_letter_not_real`).
4. **The free pair in the unit quaternions** (§4). The word map `F₂ → ℍ[ℝ]ˣ`, `a ↦ 1 + 2i`, `b ↦ 1 + 2j` (`wordMap`)
   sends a word to a positive multiple of its integer product (`val_wordMap_mk`), so only the empty word lands on a real
   quaternion (`eq_one_of_wordMap_real`), and the map is injective (`wordMap_injective`).
5. **The free pair in SO(3)** (§5). The rotation `v ↦ q v q̄ / N(q)` on the pure quaternions as a matrix (`rot`): its
   unnormalized matrix is multiplicative (`rotM_mul`), orthogonal up to `N²` (`rotM_mul_transpose`) with determinant
   `N³` (`det_rotM`), so `rot` lands in SO(3) and multiplies (`rot_mem`, `rot_mul`) and gives
   `rotation : ℍ[ℝ]ˣ →* SO(3)`; its kernel is the real quaternions (`rotation_eq_one_iff`). The
   two letters turn about the first and the second axis by the angle whose cosine is `−3/5` and sine `4/5`
   (`rot_letter_zero`, `rot_letter_one`), and the composite `F₂ → SO(3)` is injective (`rotation_wordMap_injective`):
   two words of different reduced form are two different rotations, so the order of the symbols is read.

Limits. The freeness is proved over `ℝ` for these two turns, through the classical reduction modulo five; the general
criterion (which pairs of rational rotations are free), the angle `arccos(−3/5)` as an irrational multiple of `π`, and
the ring chain's pump realizing the turns are not stated here. The one-plane collapse it is set against is
`Geometry/ScrewTorsion.plane_reflections_compose` and `plane_turns_commute`.

The computational object is the helical pair interaction: each ring's turn is a letter, a chain of two coupled rings
composes them as a word, and freeness says that the composite turn keeps the word's order, which a single plane's
commuting turns lose. Of the winding guide's six general objects this touches the helix (a letter is a turn), the cell
holonomy (a word's product is the holonomy round its route) and the tower thread (the reduction modulo five is a
restriction to a coarser ring); the pair, faces and placement and the tube stay attached.

Consumers: the atlas row `rotation.quaternion-free-pair` and the #410 box "Two coupled planes carry order".

No `sorry`, no `axiom`, no `native_decide`.
-/

open Quaternion

namespace Holonics.Geometry.QuaternionFreePair

/-! ## 1. The letters -/

section Letters

variable {R : Type*} [CommRing R]

/-- [definition] The quaternion with components `a, b, c, d`, typed as a Hamilton quaternion. -/
def mkQ (a b c d : R) : ℍ[R] := ⟨a, b, c, d⟩

/-- [definition] Its real part. -/
@[simp] theorem re_mkQ (a b c d : R) : (mkQ a b c d).re = a := rfl
/-- [definition] Its `i` part. -/
@[simp] theorem imI_mkQ (a b c d : R) : (mkQ a b c d).imI = b := rfl
/-- [definition] Its `j` part. -/
@[simp] theorem imJ_mkQ (a b c d : R) : (mkQ a b c d).imJ = c := rfl
/-- [definition] Its `k` part. -/
@[simp] theorem imK_mkQ (a b c d : R) : (mkQ a b c d).imK = d := rfl

/-- [definition] The sign of a letter: `2` for a generator, `−2` for its inverse direction. -/
def sgn (b : Bool) : R := cond b 2 (-2)

/-- [definition] The four letters `1 ± 2i` (`x.1 = 0`) and `1 ± 2j` (`x.1 = 1`), the sign read from `x.2`. -/
def letter (x : Fin 2 × Bool) : ℍ[R] :=
  if x.1 = 0 then mkQ 1 (sgn x.2) 0 0 else mkQ 1 0 (sgn x.2) 0

/-- [proved-standard; formal-checked] Every letter has norm five. -/
theorem normSq_letter (x : Fin 2 × Bool) : normSq (letter x : ℍ[R]) = 5 := by
  rcases x with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp only [letter, sgn] <;> rw [normSq_def'] <;> simp <;> norm_num

/-- [proved-standard; formal-checked] A letter's conjugate is the letter of the opposite sign. -/
theorem star_letter (i : Fin 2) (b : Bool) : star (letter (i, b) : ℍ[R]) = letter (i, !b) := by
  fin_cases i <;> cases b <;> ext <;> simp [letter, sgn]

/-- [definition] The quaternions' map of a ring map, componentwise. -/
def qmap {S : Type*} [CommRing S] (f : R →+* S) : ℍ[R] →+* ℍ[S] where
  toFun q := mkQ (f q.re) (f q.imI) (f q.imJ) (f q.imK)
  map_one' := by ext <;> simp
  map_mul' p q := by ext <;> simp [re_mul, imI_mul, imJ_mul, imK_mul]
  map_zero' := by ext <;> simp
  map_add' p q := by ext <;> simp

/-- [proved-standard; formal-checked] The components of a mapped quaternion. -/
theorem qmap_apply {S : Type*} [CommRing S] (f : R →+* S) (q : ℍ[R]) :
    qmap f q = mkQ (f q.re) (f q.imI) (f q.imJ) (f q.imK) := rfl

/-- [proved-standard; formal-checked] A ring map carries letters to letters. -/
theorem qmap_letter {S : Type*} [CommRing S] (f : R →+* S) (x : Fin 2 × Bool) :
    qmap f (letter x) = letter x := by
  rcases x with ⟨i, b⟩
  fin_cases i <;> cases b <;> ext <;> simp [qmap_apply, letter, sgn, map_ofNat]

end Letters

/-! ## 2. Rank one modulo five -/

section ModFive

/-- [definition] Five is prime, so `ZMod 5` is a field. -/
local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- [proved-standard; formal-checked] `y m y = (2 Re(y m)) y − N(y) m̄` for any quaternions over a commutative ring. -/
theorem mul_mul_self {R : Type*} [CommRing R] (y m : ℍ[R]) :
    y * m * y = (2 * (y * m).re) • y - normSq y • star m := by
  ext <;> simp [re_mul, imI_mul, imJ_mul, imK_mul, normSq_def'] <;> ring

/-- [proved-standard; formal-checked] A nonzero quaternion has a right factor among `1, i, j, k` that leaves a nonzero
real part. -/
theorem exists_re_mul_ne_zero {R : Type*} [CommRing R] {q : ℍ[R]} (hq : q ≠ 0) :
    ∃ z : ℍ[R], (q * z).re ≠ 0 := by
  by_contra h
  push Not at h
  apply hq
  have h1 := h 1
  have hi := h (mkQ 0 1 0 0)
  have hj := h (mkQ 0 0 1 0)
  have hk := h (mkQ 0 0 0 1)
  simp [re_mul] at h1 hi hj hk
  ext <;> simp [h1, hi, hj, hk]

/-- [proved-standard; formal-checked] For `N(x) = 0` and `x y ≠ 0`, `t x y = 0` forces `t x = 0`: modulo five the left
annihilator of `x y` is that of `x`, as for rank-one matrices. -/
theorem mul_eq_zero_of_mul_mul {x y t : ℍ[ZMod 5]} (hx : normSq x = 0) (hxy : x * y ≠ 0)
    (h : t * x * y = 0) : t * x = 0 := by
  obtain ⟨z, hz⟩ := exists_re_mul_ne_zero hxy
  have key : t * x * y * z * x = (2 * (x * (y * z)).re) • (t * x) := by
    have : t * x * y * z * x = t * (x * (y * z) * x) := by noncomm_ring
    rw [this, mul_mul_self, hx, zero_smul, sub_zero, mul_smul_comm]
  rw [h, zero_mul, zero_mul, ← mul_assoc] at key
  have h2 : (2 * (x * y * z).re : ZMod 5) ≠ 0 := mul_ne_zero (by decide) hz
  exact (smul_eq_zero.mp key.symm).resolve_left h2

/-- [proved-standard; formal-checked] Modulo five every letter has norm zero. -/
theorem normSq_letter_five (x : Fin 2 × Bool) : normSq (letter x : ℍ[ZMod 5]) = 0 := by
  rw [normSq_letter]; rfl

/-- [proved-standard; formal-checked] Two letters that are not inverse multiply, modulo five, to a quaternion with
nonzero real part (`1` across the axes, `−3` on one axis with one sign; the inverse pair gives `5 = 0`). -/
theorem letter_mul_letter_re_ne_zero {x y : Fin 2 × Bool} (h : x.1 = y.1 → x.2 = y.2) :
    ((letter x : ℍ[ZMod 5]) * letter y).re ≠ 0 := by
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  fin_cases i <;> fin_cases j <;> cases b <;> cases c <;> simp [letter, sgn, re_mul] at h ⊢ <;> decide

/-- [proved-standard; formal-checked] The product of a reduced word modulo five has the left annihilator of its first
letter. -/
theorem annihilator_prod (x : Fin 2 × Bool) (L : List (Fin 2 × Bool))
    (hL : FreeGroup.IsReduced (x :: L)) (t : ℍ[ZMod 5]) :
    t * ((x :: L).map letter).prod = 0 ↔ t * letter x = 0 := by
  induction L generalizing x t with
  | nil => simp
  | cons y L ih =>
    have hxy : x.1 = y.1 → x.2 = y.2 := (List.isChain_cons_cons.mp hL).1
    have hrest : FreeGroup.IsReduced (y :: L) := (List.isChain_cons_cons.mp hL).2
    rw [List.map_cons, List.prod_cons, ← mul_assoc, ih y hrest]
    constructor
    · intro h
      refine mul_eq_zero_of_mul_mul (normSq_letter_five x) ?_ (by rwa [mul_assoc] at h ⊢)
      intro h0
      exact letter_mul_letter_re_ne_zero hxy (by rw [h0]; rfl)
    · intro h; rw [h, zero_mul]

/-- [proved-standard; formal-checked] A letter is not zero modulo five (its real part is one). -/
theorem letter_ne_zero_five (x : Fin 2 × Bool) : (letter x : ℍ[ZMod 5]) ≠ 0 := by
  intro h
  have := congrArg QuaternionAlgebra.re h
  rcases x with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp [letter] at this

/-- [proved-standard; formal-checked] The product of a nonempty reduced word is not zero modulo five. -/
theorem prod_letter_ne_zero {L : List (Fin 2 × Bool)} (hL : FreeGroup.IsReduced L) (hne : L ≠ []) :
    (L.map letter).prod ≠ (0 : ℍ[ZMod 5]) := by
  obtain ⟨x, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  intro h
  have := (annihilator_prod x L' hL 1).mp (by rw [h, mul_zero])
  rw [one_mul] at this
  exact letter_ne_zero_five x this

end ModFive

/-! ## 3. No reduced word is real -/

section Integer

/-- [proved-standard; formal-checked] The product of a word's letters has norm `5ⁿ`, `n` its length. -/
theorem normSq_prod_letter (L : List (Fin 2 × Bool)) :
    normSq ((L.map letter).prod : ℍ[ℤ]) = 5 ^ L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, map_mul, normSq_letter, ih, List.length_cons, pow_succ, mul_comm]

/-- [proved-standard; formal-checked] A ring map carries a word's product of letters to the same product. -/
theorem qmap_prod_letter {S : Type*} [CommRing S] (f : ℤ →+* S) (L : List (Fin 2 × Bool)) :
    qmap f ((L.map letter).prod) = (L.map letter).prod := by
  induction L with
  | nil => simp
  | cons x L ih => simp [map_mul, qmap_letter, ih]

/-- [proved-standard; formal-checked] The integer product of a nonempty reduced word is not real: were its imaginary
part zero, its real part `r` would have `r² = 5ⁿ` with `n ≥ 1`, so five would divide `r` and the product would vanish
modulo five, which `prod_letter_ne_zero` refuses. -/
theorem prod_letter_not_real {L : List (Fin 2 × Bool)} (hL : FreeGroup.IsReduced L) (hne : L ≠ []) :
    ¬ (((L.map letter).prod : ℍ[ℤ]).imI = 0 ∧ ((L.map letter).prod : ℍ[ℤ]).imJ = 0 ∧
      ((L.map letter).prod : ℍ[ℤ]).imK = 0) := by
  rintro ⟨hi, hj, hk⟩
  have hN := normSq_prod_letter L
  rw [normSq_def'] at hN
  simp only [hi, hj, hk] at hN
  have hsq : ((L.map letter).prod : ℍ[ℤ]).re ^ 2 = 5 ^ L.length := by simpa using hN
  have h5 : (5 : ℤ) ∣ ((L.map letter).prod : ℍ[ℤ]).re := by
    have hd : (5 : ℤ) ∣ ((L.map letter).prod : ℍ[ℤ]).re ^ 2 := by
      rw [hsq]; exact dvd_pow_self 5 (List.length_pos_iff.mpr hne).ne'
    exact Prime.dvd_of_dvd_pow ((Int.prime_iff_natAbs_prime (k := 5)).mpr Nat.prime_five) hd
  have hzero : qmap (Int.castRingHom (ZMod 5)) ((L.map letter).prod) = 0 := by
    ext <;> simp [qmap_apply, hi, hj, hk]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr h5
  rw [qmap_prod_letter] at hzero
  exact prod_letter_ne_zero hL hne hzero

end Integer

/-! ## 4. The free pair in the unit quaternions -/

section WordMap

/-- [proved-standard; formal-checked] A letter is not zero over `ℝ`. -/
theorem letter_ne_zero_real (x : Fin 2 × Bool) : (letter x : ℍ[ℝ]) ≠ 0 := by
  intro h
  have := normSq_letter (R := ℝ) x
  rw [h, map_zero] at this
  norm_num at this

/-- [definition] The two turns as unit quaternions: `1 + 2i` and `1 + 2j`. -/
noncomputable def gen (i : Fin 2) : (ℍ[ℝ])ˣ := Units.mk0 (letter (i, true)) (letter_ne_zero_real _)

/-- [definition] The word map `F₂ → ℍ[ℝ]ˣ`, `a ↦ 1 + 2i`, `b ↦ 1 + 2j`. -/
noncomputable def wordMap : FreeGroup (Fin 2) →* (ℍ[ℝ])ˣ := FreeGroup.lift gen

/-- [definition] A letter's scale: `1` for a generator, `1/5` for an inverse (`(1 + 2i)⁻¹ = (1 − 2i)/5`). -/
noncomputable def scale (b : Bool) : ℝ := cond b 1 (1 / 5)

/-- [proved-standard; formal-checked] A letter of a word, as a unit, is its scale times the integer letter. -/
theorem val_gen_cond (i : Fin 2) (b : Bool) :
    ((cond b (gen i) (gen i)⁻¹ : (ℍ[ℝ])ˣ) : ℍ[ℝ]) = scale b • letter (i, b) := by
  cases b
  · simp only [cond_false, scale]
    rw [Units.val_inv_eq_inv_val, gen, Units.val_mk0, Quaternion.inv_def, normSq_letter, star_letter,
      Bool.not_true]
    norm_num
  · simp [gen, scale]

/-- [proved-standard; formal-checked] Scalars pass through a product: `(a x)(b y) = (a b)(x y)`. -/
theorem smul_mul_smul' (a b : ℝ) (x y : ℍ[ℝ]) : (a • x) * (b • y) = (a * b) • (x * y) := by
  ext <;> simp [re_mul, imI_mul, imJ_mul, imK_mul] <;> ring

/-- [proved-standard; formal-checked] The word map sends a word to a positive multiple of its product of letters. -/
theorem val_wordMap_mk (L : List (Fin 2 × Bool)) :
    ((wordMap (FreeGroup.mk L) : (ℍ[ℝ])ˣ) : ℍ[ℝ]) = (L.map fun x => scale x.2).prod • (L.map letter).prod := by
  rw [wordMap, FreeGroup.lift_mk]
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih, val_gen_cond, List.map_cons, List.prod_cons,
      List.map_cons, List.prod_cons]
    exact smul_mul_smul' _ _ _ _

/-- [proved-standard; formal-checked] A word's scale is positive. -/
theorem prod_scale_pos (L : List (Fin 2 × Bool)) : 0 < (L.map fun x => scale x.2).prod := by
  apply List.prod_pos
  intro a ha
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
  cases x.2 <;> norm_num [scale]

/-- [proved-standard; formal-checked] Only the empty word lands on a real quaternion. -/
theorem eq_one_of_wordMap_real (w : FreeGroup (Fin 2))
    (h : ((wordMap w : (ℍ[ℝ])ˣ) : ℍ[ℝ]).imI = 0 ∧ ((wordMap w : (ℍ[ℝ])ˣ) : ℍ[ℝ]).imJ = 0 ∧
      ((wordMap w : (ℍ[ℝ])ˣ) : ℍ[ℝ]).imK = 0) : w = 1 := by
  by_contra hw
  have hne : w.toWord ≠ [] := fun h0 => hw (FreeGroup.toWord_eq_nil_iff.mp h0)
  rw [← FreeGroup.mk_toWord (x := w), val_wordMap_mk, ← qmap_prod_letter (Int.castRingHom ℝ)] at h
  have hc := (prod_scale_pos w.toWord).ne'
  apply prod_letter_not_real FreeGroup.isReduced_toWord hne
  obtain ⟨hi, hj, hk⟩ := h
  simp only [Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul, qmap_apply,
    imI_mkQ, imJ_mkQ, imK_mkQ, smul_eq_mul, mul_eq_zero, hc, false_or, eq_intCast, Int.cast_eq_zero] at hi hj hk
  exact ⟨hi, hj, hk⟩

/-- [proved-standard; formal-checked] The word map is injective: `1 + 2i` and `1 + 2j` generate a free group of rank two
in the unit quaternions. -/
theorem wordMap_injective : Function.Injective wordMap := by
  refine (injective_iff_map_eq_one wordMap).mpr fun w hw => eq_one_of_wordMap_real w ?_
  rw [hw]
  simp

end WordMap

/-! ## 5. The free pair in SO(3) -/

section Rotation

variable {R : Type*} [CommRing R]

/-- [definition] The unnormalized matrix of `v ↦ q v q̄` on the pure quaternions, in the basis `i, j, k`. -/
def rotM (q : ℍ[R]) : Matrix (Fin 3) (Fin 3) R :=
  !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2, 2 * (q.imI * q.imJ - q.re * q.imK),
      2 * (q.imI * q.imK + q.re * q.imJ);
    2 * (q.imI * q.imJ + q.re * q.imK), q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
      2 * (q.imJ * q.imK - q.re * q.imI);
    2 * (q.imI * q.imK - q.re * q.imJ), 2 * (q.imJ * q.imK + q.re * q.imI),
      q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2]

/-- [proved-standard; formal-checked] The unnormalized matrix is multiplicative: `(p q) v (p q)‾ = p (q v q̄) p̄`. -/
theorem rotM_mul (p q : ℍ[R]) : rotM (p * q) = rotM p * rotM q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, Matrix.mul_apply, Fin.sum_univ_three, re_mul, imI_mul, imJ_mul, imK_mul] <;> ring

/-- [proved-standard; formal-checked] It is orthogonal up to `N(q)²`. -/
theorem rotM_mul_transpose (q : ℍ[R]) : rotM q * (rotM q).transpose = (normSq q) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) R) := by
  rw [normSq_def']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- [proved-standard; formal-checked] Its determinant is `N(q)³`. -/
theorem det_rotM (q : ℍ[R]) : (rotM q).det = (normSq q) ^ 3 := by
  rw [normSq_def', Matrix.det_fin_three]
  simp [rotM]
  ring

/-- [definition] The rotation of a quaternion, `v ↦ q v q̄ / N(q)` on the pure quaternions. -/
noncomputable def rot (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ := (normSq q)⁻¹ • rotM q

/-- [proved-standard; formal-checked] A nonzero quaternion's rotation lies in SO(3). -/
theorem rot_mem {q : ℍ[ℝ]} (hq : q ≠ 0) : rot q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hN : normSq q ≠ 0 := normSq_ne_zero.mpr hq
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · rw [rot, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, rotM_mul_transpose, smul_smul, smul_smul]
    have : (normSq q)⁻¹ * (normSq q)⁻¹ * normSq q ^ 2 = 1 := by field_simp
    rw [this, one_smul]
  · rw [rot, Matrix.det_smul, det_rotM, Fintype.card_fin]
    field_simp

/-- [proved-standard; formal-checked] Rotation is multiplicative. -/
theorem rot_mul (p q : ℍ[ℝ]) : rot (p * q) = rot p * rot q := by
  rw [rot, rot, rot, rotM_mul, map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv]

/-- [definition] The rotation as a group hom `ℍ[ℝ]ˣ →* SO(3)`. -/
noncomputable def rotation : (ℍ[ℝ])ˣ →* Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  MonoidHom.mk' (fun u => ⟨rot u, rot_mem u.ne_zero⟩) fun u v => Subtype.ext (by simp [rot_mul])

/-- [proved-standard; formal-checked] The rotation's kernel is the real quaternions. -/
theorem rotation_eq_one_iff (u : (ℍ[ℝ])ˣ) :
    rotation u = 1 ↔ (u : ℍ[ℝ]).imI = 0 ∧ (u : ℍ[ℝ]).imJ = 0 ∧ (u : ℍ[ℝ]).imK = 0 := by
  have hN : 0 < normSq (u : ℍ[ℝ]) := lt_of_le_of_ne normSq_nonneg (normSq_ne_zero.mpr u.ne_zero).symm
  have hrot : rotation u = 1 ↔ rot u = 1 := by
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [hrot]
  set q : ℍ[ℝ] := (u : ℍ[ℝ]) with hq
  rw [normSq_def'] at hN
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 1) 1
    simp [rot, rotM, normSq_def'] at h00 h11
    field_simp at h00 h11
    have hc : q.imJ ^ 2 + q.imK ^ 2 = 0 := by nlinarith
    have hb : q.imI ^ 2 + q.imK ^ 2 = 0 := by nlinarith
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
  · rintro ⟨hi, hj, hk⟩
    have ha : q.re ≠ 0 := by intro h0; simp [hi, hj, hk, h0] at hN
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rot, rotM, normSq_def', hi, hj, hk] <;> field_simp

/-- [proved-standard; formal-checked] `1 + 2i` turns about the first axis by the angle of cosine `−3/5`, sine `4/5`. -/
theorem rot_letter_zero : rot (letter (0, true)) = !![1, 0, 0; 0, -3/5, -4/5; 0, 4/5, -3/5] := by
  rw [rot, normSq_letter]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, letter, sgn] <;> norm_num

/-- [proved-standard; formal-checked] `1 + 2j` turns about the second axis by the same angle. -/
theorem rot_letter_one : rot (letter (1, true)) = !![-3/5, 0, 4/5; 0, 1, 0; -4/5, 0, -3/5] := by
  rw [rot, normSq_letter]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, letter, sgn] <;> norm_num

/-- [proved-standard; formal-checked] The turns by `1 + 2i` and `1 + 2j` generate a free group of rank two in SO(3): two
words of different reduced form are two different rotations. -/
theorem rotation_wordMap_injective : Function.Injective (rotation.comp wordMap) :=
  (injective_iff_map_eq_one _).mpr fun w hw =>
    eq_one_of_wordMap_real w ((rotation_eq_one_iff (wordMap w)).mp hw)

end Rotation

end Holonics.Geometry.QuaternionFreePair
