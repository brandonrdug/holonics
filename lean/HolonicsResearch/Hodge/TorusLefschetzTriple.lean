import Mathlib
import HolonicsResearch.Hodge.LefschetzFromPositivity

/-!
# The Lefschetz triple of a flat torus: hard Lefschetz on `Λ(ℝ^(2n))`

Source record: `research/records/2026-11-18_HARD_LEFSCHETZ_HOLDS_ON_A_FLAT_TORUS_LETTER_BY_LETTER_A_COVERS_CLOSED_WALKS_FALL_INTO_THEIR_HOLONOMY_CLASSES_AT_THE_HALF_AND_THE_COVERING_TREES_RETURNS_SET_THE_FLOOR_AT_THE_HALF.md`,
§3, the sequel to `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md`,
§8.3, which names a triple with a positive pairing on a cohomology as what hard Lefschetz needs.

**[definition] The model** (`agent-inferred`).  The exterior algebra `Λ(ℝ^(2n))` of the plane
pairs `(e_i, f_i)`, `i < n`, has the orthonormal basis of words `w : Fin n → Fin 4` (`Word`): at
place `i` the letter `0` is `1`, `1` is `e_i`, `2` is `f_i` and `3` is `e_i ∧ f_i`.  Its forms are
`Forms n = EuclideanSpace ℝ (Word n)`.  The flat Kähler form is `ω = Σ_i e_i ∧ f_i`; because each
`e_i ∧ f_i` is even, `ω ∧ ·` acts letter by letter with no sign: `lowerAt i` (`L_i`) turns the
letter `0` at `i` into `3`, `raiseAt i` (`Λ_i`) turns `3` back into `0`, and `weightAt i` (`H_i`)
multiplies a word by `h(w i)`, with `h 0 = 1`, `h 3 = −1`, `h 1 = h 2 = 0` (`letterWeight`).  The
move is `L = Σ_i L_i` (`lefschetz`, the cup product with `ω`), its reversal `Λ = Σ_i Λ_i`
(`dualLefschetz`) and the weight `H = Σ_i H_i` (`weight`).  Each letterwise move is read through
the involution `flip i` that exchanges the letters `0` and `3` at place `i`.

**[proved-derived; formal-checked] What is proved.**

1. **T1, the letterwise laws** (`inner_lowerAt`, `raiseAt_lowerAt_of_ne`, `raiseAt_lowerAt_self`,
   `weightAt_lowerAt_of_ne`, `weightAt_lowerAt_self`): `⟪L_i x, y⟫ = ⟪x, Λ_i y⟫`;
   `Λ_i L_j = L_j Λ_i` and `H_i L_j = L_j H_i` for `i ≠ j`; `Λ_i L_i − L_i Λ_i = H_i`;
   `H_i L_i − L_i H_i = −2 L_i`.
2. **T2, the triple** (`torusTriple`): `(L, Λ, H)` is a `Triple` of
   `Hodge/LefschetzFromPositivity` on `Forms n`, with the inner product of the forms as its
   positive pairing.
3. **T3, the weight is the codegree** (`weight_apply`, `weight_single`,
   `single_mem_formsOfDegree`, `mem_weightSpace_iff`, `weightSpace_eq_formsOfDegree`,
   `weightSpace_neg_eq_formsOfDegree`): `H` multiplies a word of
   degree `deg w` (`degree`: one for each `e_i` or `f_i`, two for each `e_i ∧ f_i`) by `n − deg w`,
   so the weight space of `m ∈ ℕ`, `m ≤ n`, is the forms of degree `n − m` (`formsOfDegree`), and
   the weight space of `−m` is the forms of degree `n + m`.
4. **T4, hard Lefschetz for the torus** (`hard_lefschetz_degree`, `iterate_injective_degree`,
   `inner_iterate_primitive_degree`, `lefschetzDegreeEquiv`, `lefschetzDegreeEquiv_apply`,
   `finrank_formsOfDegree_symm`): for `m ≤ n` and `x` of degree `n − m`, `m! ‖x‖ ≤ ‖L^m x‖`; on a
   primitive `x` (`Λ x = 0`), `⟪L^j x, L^j y⟫ = j! · m!/(m − j)! · ⟪x, y⟫` for `j ≤ m`; `L^m` is a
   linear equivalence from the forms of degree `n − m` onto the forms of degree `n + m`; so the two
   degrees have one dimension (the count of words, `C(2n, n − m) = C(2n, n + m)`, is not computed).

**Reading.**  [interpretation] `agent-inferred`.  The third record proved hard Lefschetz from the
positivity of one commutator and named, for a variety, the triple on its cohomology with a
positive pairing as what remains.  On a flat torus the triple is built here, letter by letter:
each plane pair `(e_i, f_i)` is one copy of the four-dimensional triple (a doublet `1, e_i ∧ f_i`
of weights `±1` and two singlets `e_i`, `f_i`), and the torus's triple is their sum.  The pairing
is the inner product of forms, positive from the start, so the theorem holds with its constant
`m!` and no harmonic theory beyond the flat one.

**What this does not state.**  That the de Rham cohomology of the torus `ℝ^(2n)/ℤ^(2n)` is
`Λ(ℝ^(2n))` (by the invariant forms) and that its cup product is `∧` are the standard
identifications and are not formalized; nor is the Hodge star.  Only the flat Kähler form
`Σ e_i ∧ f_i` is treated: no other Kähler class, no curved manifold, no Kähler identities on a
manifold.  The Hodge–Riemann signs against the intersection pairing `∫ α ∧ β ∧ ω^k` are not
stated: the pairing here is the inner product.

**Computational object.**  The helical pair interaction: each plane pair `(e_i, f_i)` is a pair
contact, `ω` the sum of the contacts, and the weight is the count of contacts a form leaves open
less the count it closes.  Of the winding guide's six objects: the pair (the plane pairs), faces
and placement (the degrees are faces, and `L^m` places one face onto its mirror) and the tower
thread (the torus as a transverse product of its planes).

**Consumers.**  The atlas row `hodge.torus-kahler-triple`; `Hodge/LefschetzFromPositivity`, whose
`Triple` this instantiates.

No `sorry`, no `axiom`, no `native_decide`.
-/

open RealInnerProductSpace Finset

namespace Holonics.Hodge.TorusLefschetzTriple

open Holonics.Hodge.LefschetzFromPositivity

variable {n : ℕ}

/-! ## The words, the forms and the letterwise moves -/

/-- [definition] A basis word of `Λ(ℝ^(2n))`: at place `i`, `0 = 1`, `1 = e_i`, `2 = f_i`,
`3 = e_i ∧ f_i`. -/
abbrev Word (n : ℕ) := Fin n → Fin 4

/-- [definition] The forms: `Λ(ℝ^(2n))` with its orthonormal basis of words. -/
abbrev Forms (n : ℕ) := EuclideanSpace ℝ (Word n)

/-- [definition] The involution exchanging the letters `0` and `3` at place `i`. -/
def flip (i : Fin n) : Equiv.Perm (Word n) where
  toFun w := Function.update w i (Equiv.swap (0 : Fin 4) 3 (w i))
  invFun w := Function.update w i (Equiv.swap (0 : Fin 4) 3 (w i))
  left_inv w := by simp
  right_inv w := by simp

/-- [proved-derived; formal-checked] `flip i` changes the letter at `i`. -/
@[simp] theorem flip_apply_self (i : Fin n) (w : Word n) :
    flip i w i = Equiv.swap (0 : Fin 4) 3 (w i) := by
  simp [flip]

/-- [proved-derived; formal-checked] `flip i` keeps every other letter. -/
theorem flip_apply_of_ne {i j : Fin n} (h : j ≠ i) (w : Word n) : flip i w j = w j := by
  simp [flip, Function.update_of_ne h]

/-- [proved-derived; formal-checked] `flip i` is an involution. -/
@[simp] theorem flip_flip (i : Fin n) (w : Word n) : flip i (flip i w) = w :=
  (flip i).left_inv w

/-- [proved-derived; formal-checked] Flips at two places commute. -/
theorem flip_comm {i j : Fin n} (h : i ≠ j) (w : Word n) :
    flip i (flip j w) = flip j (flip i w) := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [flip_apply_self, flip_apply_of_ne h, flip_apply_of_ne h, flip_apply_self]
  · by_cases hkj : k = j
    · subst hkj
      rw [flip_apply_of_ne hki, flip_apply_self, flip_apply_self, flip_apply_of_ne hki]
    · rw [flip_apply_of_ne hki, flip_apply_of_ne hkj, flip_apply_of_ne hkj, flip_apply_of_ne hki]

/-- [proved-derived; formal-checked] The letter `0` flips to `3` and back. -/
theorem swap_eq_three_iff (a : Fin 4) : Equiv.swap (0 : Fin 4) 3 a = 3 ↔ a = 0 := by
  fin_cases a <;> decide

/-- [proved-derived; formal-checked] The letter `3` flips to `0` and back. -/
theorem swap_eq_zero_iff (a : Fin 4) : Equiv.swap (0 : Fin 4) 3 a = 0 ↔ a = 3 := by
  fin_cases a <;> decide

/-- [definition] A gated transport: at a word where the gate holds, read the form at the flipped
word; elsewhere, zero. -/
noncomputable def gated (i : Fin n) (a : Fin 4) : Forms n →ₗ[ℝ] Forms n where
  toFun x := WithLp.toLp 2 (fun w => if w i = a then x (flip i w) else 0)
  map_add' x y := by
    ext w
    simp only [PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    ext w
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem gated_apply (i : Fin n) (a : Fin 4) (x : Forms n) (w : Word n) :
    gated i a x w = if w i = a then x (flip i w) else 0 := rfl

/-- [definition] `L_i = (e_i ∧ f_i) ∧ ·`: the letter `0` at `i` becomes `3`. -/
noncomputable def lowerAt (i : Fin n) : Forms n →ₗ[ℝ] Forms n := gated i 3

/-- [definition] `Λ_i`, the reversal of `L_i`: the letter `3` at `i` becomes `0`. -/
noncomputable def raiseAt (i : Fin n) : Forms n →ₗ[ℝ] Forms n := gated i 0

/-- [definition] The weight of a letter: `1` for `1`, `−1` for `e_i ∧ f_i`, `0` for `e_i`, `f_i`. -/
def letterWeight (a : Fin 4) : ℝ := (if a = 0 then 1 else 0) - (if a = 3 then 1 else 0)

/-- [definition] `H_i`: multiply a word by its letter's weight at `i`. -/
noncomputable def weightAt (i : Fin n) : Forms n →ₗ[ℝ] Forms n where
  toFun x := WithLp.toLp 2 (fun w => letterWeight (w i) * x w)
  map_add' x y := by
    ext w
    simp only [PiLp.add_apply]
    ring
  map_smul' c x := by
    ext w
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lowerAt_apply (i : Fin n) (x : Forms n) (w : Word n) :
    lowerAt i x w = if w i = 3 then x (flip i w) else 0 := rfl

theorem raiseAt_apply (i : Fin n) (x : Forms n) (w : Word n) :
    raiseAt i x w = if w i = 0 then x (flip i w) else 0 := rfl

theorem weightAt_apply (i : Fin n) (x : Forms n) (w : Word n) :
    weightAt i x w = letterWeight (w i) * x w := rfl

/-! ## T1. The letterwise laws -/

/-- [proved-derived; formal-checked] **T1, the reversal**: `⟪L_i x, y⟫ = ⟪x, Λ_i y⟫`. -/
theorem inner_lowerAt (i : Fin n) (x y : Forms n) :
    ⟪lowerAt i x, y⟫ = ⟪x, raiseAt i y⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, lowerAt_apply, raiseAt_apply]
  rw [← Equiv.sum_comp (flip i)]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [flip_apply_self, swap_eq_three_iff, flip_flip]
  split_ifs <;> ring

/-- [proved-derived; formal-checked] **T1**: the moves at two places commute. -/
theorem raiseAt_lowerAt_of_ne {i j : Fin n} (h : i ≠ j) (x : Forms n) :
    raiseAt i (lowerAt j x) = lowerAt j (raiseAt i x) := by
  ext w
  rw [raiseAt_apply, lowerAt_apply, lowerAt_apply, raiseAt_apply, flip_apply_of_ne h.symm,
    flip_apply_of_ne h, flip_comm h]
  split_ifs <;> rfl

/-- [proved-derived; formal-checked] **T1**: at one place, `Λ_i L_i − L_i Λ_i = H_i`. -/
theorem raiseAt_lowerAt_self (i : Fin n) (x : Forms n) :
    raiseAt i (lowerAt i x) - lowerAt i (raiseAt i x) = weightAt i x := by
  ext w
  rw [PiLp.sub_apply, raiseAt_apply, lowerAt_apply, lowerAt_apply, raiseAt_apply, weightAt_apply]
  simp only [flip_apply_self, flip_flip, letterWeight]
  generalize w i = a
  fin_cases a <;> simp

/-- [proved-derived; formal-checked] **T1**: the weight at one place commutes with the move at
another. -/
theorem weightAt_lowerAt_of_ne {i j : Fin n} (h : i ≠ j) (x : Forms n) :
    weightAt i (lowerAt j x) = lowerAt j (weightAt i x) := by
  ext w
  rw [weightAt_apply, lowerAt_apply, lowerAt_apply, weightAt_apply, flip_apply_of_ne h]
  split_ifs <;> ring

/-- [proved-derived; formal-checked] **T1**: at one place, `H_i L_i − L_i H_i = −2 L_i`. -/
theorem weightAt_lowerAt_self (i : Fin n) (x : Forms n) :
    weightAt i (lowerAt i x) - lowerAt i (weightAt i x) = (-2 : ℝ) • lowerAt i x := by
  ext w
  rw [PiLp.sub_apply, PiLp.smul_apply, weightAt_apply, lowerAt_apply, lowerAt_apply,
    weightAt_apply, flip_apply_self, smul_eq_mul, letterWeight, letterWeight]
  generalize w i = a
  fin_cases a <;> simp
  ring

/-! ## T2. The triple -/

/-- [definition] `L = ω ∧ ·`, with `ω = Σ_i e_i ∧ f_i`. -/
noncomputable def lefschetz (n : ℕ) : Forms n →ₗ[ℝ] Forms n := ∑ i, lowerAt i

/-- [definition] `Λ = Σ_i Λ_i`, the reversal of `L`. -/
noncomputable def dualLefschetz (n : ℕ) : Forms n →ₗ[ℝ] Forms n := ∑ i, raiseAt i

/-- [definition] `H = Σ_i H_i`. -/
noncomputable def weight (n : ℕ) : Forms n →ₗ[ℝ] Forms n := ∑ i, weightAt i

/-- [proved-derived; formal-checked] `L` is the sum of its letterwise moves. -/
theorem lefschetz_apply (x : Forms n) : lefschetz n x = ∑ i, lowerAt i x := by
  simp [lefschetz]

theorem dualLefschetz_apply (x : Forms n) : dualLefschetz n x = ∑ i, raiseAt i x := by
  simp [dualLefschetz]

theorem weight_apply' (x : Forms n) : weight n x = ∑ i, weightAt i x := by
  simp [weight]

/-- [proved-derived; formal-checked] `⟪L x, y⟫ = ⟪x, Λ y⟫`. -/
theorem inner_lefschetz (x y : Forms n) :
    ⟪lefschetz n x, y⟫ = ⟪x, dualLefschetz n y⟫ := by
  rw [lefschetz_apply, dualLefschetz_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun i _ => inner_lowerAt i x y

/-- [proved-derived; formal-checked] `Λ L − L Λ = H`. -/
theorem comm_lefschetz (x : Forms n) :
    dualLefschetz n (lefschetz n x) - lefschetz n (dualLefschetz n x) = weight n x := by
  simp only [lefschetz_apply, dualLefschetz_apply, weight_apply', map_sum]
  rw [Finset.sum_comm (f := fun j i => raiseAt i (lowerAt j x)), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · exact raiseAt_lowerAt_self i x
  · intro j _ hji
    rw [raiseAt_lowerAt_of_ne (Ne.symm hji), sub_self]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- [proved-derived; formal-checked] `H L − L H = −2 L`. -/
theorem lower_lefschetz (x : Forms n) :
    weight n (lefschetz n x) - lefschetz n (weight n x) = (-2 : ℝ) • lefschetz n x := by
  simp only [lefschetz_apply, weight_apply', map_sum, Finset.smul_sum]
  rw [Finset.sum_comm (f := fun j i => weightAt i (lowerAt j x)), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · exact weightAt_lowerAt_self i x
  · intro j _ hji
    rw [weightAt_lowerAt_of_ne (Ne.symm hji), sub_self]
  · intro h
    exact absurd (Finset.mem_univ i) h

variable (n) in
/-- [proved-derived; formal-checked] **T2, the torus's Lefschetz triple**: `(L, Λ, H)` on the
forms, with the forms' inner product as its positive pairing. -/
noncomputable def torusTriple : Triple (Forms n) where
  U := lefschetz n
  D := dualLefschetz n
  H := weight n
  adj := inner_lefschetz
  comm := comm_lefschetz
  lower := lower_lefschetz

/-! ## T3. The weight is the codegree -/

/-- [definition] The degree of a letter: `0` for `1`, `1` for `e_i` and `f_i`, `2` for
`e_i ∧ f_i`. -/
def letterDegree (a : Fin 4) : ℕ := if a = 0 then 0 else if a = 3 then 2 else 1

/-- [definition] The degree of a word, the degree of its form in `Λ(ℝ^(2n))`. -/
def degree (w : Word n) : ℕ := ∑ i, letterDegree (w i)

/-- [proved-derived; formal-checked] A letter's weight is one less its degree. -/
theorem letterWeight_eq (a : Fin 4) : letterWeight a = 1 - (letterDegree a : ℝ) := by
  fin_cases a <;> norm_num [letterWeight, letterDegree, Fin.ext_iff]

/-- [proved-derived; formal-checked] **T3**: `H` is diagonal on the words, and multiplies the word
`w` by its codegree `n − deg w`. -/
theorem weight_apply (x : Forms n) (w : Word n) :
    weight n x w = ((n : ℝ) - degree w) * x w := by
  rw [weight_apply', WithLp.ofLp_sum, Finset.sum_apply]
  simp only [weightAt_apply, ← Finset.sum_mul, letterWeight_eq, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, degree,
    Nat.cast_sum]

/-- [proved-derived; formal-checked] **T3 on a basis word**:
`H (single w c) = (n − deg w) • single w c`. -/
theorem weight_single (v : Word n) (c : ℝ) :
    weight n (PiLp.single 2 v c) = ((n : ℝ) - degree v) • PiLp.single 2 v c := by
  ext w
  rw [weight_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero, mul_zero]

variable (n) in
/-- [definition] The forms of degree `k`: those that vanish on every word of another degree. -/
def formsOfDegree (k : ℕ) : Submodule ℝ (Forms n) where
  carrier := {x | ∀ w, degree w ≠ k → x w = 0}
  zero_mem' w _ := rfl
  add_mem' {x y} hx hy w hw := by
    rw [PiLp.add_apply, hx w hw, hy w hw, add_zero]
  smul_mem' c x hx w hw := by
    rw [PiLp.smul_apply, hx w hw, smul_zero]

theorem mem_formsOfDegree {k : ℕ} {x : Forms n} :
    x ∈ formsOfDegree n k ↔ ∀ w, degree w ≠ k → x w = 0 := Iff.rfl

/-- [proved-derived; formal-checked] A basis word is a form of its own degree. -/
theorem single_mem_formsOfDegree (v : Word n) (c : ℝ) :
    PiLp.single 2 v c ∈ formsOfDegree n (degree v) := by
  intro w hw
  rw [PiLp.single_apply, if_neg]
  rintro rfl
  exact hw rfl

/-- [proved-derived; formal-checked] **T3**: a form has weight `m` exactly when it vanishes on
every word whose codegree is not `m`. -/
theorem mem_weightSpace_iff (m : ℝ) (x : Forms n) :
    x ∈ (torusTriple n).weightSpace m ↔ ∀ w, x w ≠ 0 → (n : ℝ) - degree w = m := by
  rw [Triple.mem_weightSpace]
  change weight n x = m • x ↔ _
  constructor
  · intro h w hw
    have := congrArg (fun y : Forms n => y w) h
    simp only [weight_apply, PiLp.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hw this
  · intro h
    ext w
    rw [weight_apply, PiLp.smul_apply, smul_eq_mul]
    by_cases hw : x w = 0
    · rw [hw, mul_zero, mul_zero]
    · rw [h w hw]

/-- [proved-derived; formal-checked] The codegree read in `ℕ`, for `m ≤ n`. -/
theorem codegree_eq_iff {m : ℕ} (hm : m ≤ n) (d : ℕ) : (n : ℝ) - d = m ↔ d = n - m := by
  constructor
  · intro h
    have : (d : ℝ) = ((n - m : ℕ) : ℝ) := by rw [Nat.cast_sub hm]; linarith
    exact_mod_cast this
  · rintro rfl
    rw [Nat.cast_sub hm]
    ring

/-- [proved-derived; formal-checked] **T3**: for `m ≤ n` the weight space of `m` is the forms of
degree `n − m`. -/
theorem weightSpace_eq_formsOfDegree {m : ℕ} (hm : m ≤ n) :
    (torusTriple n).weightSpace (m : ℝ) = formsOfDegree n (n - m) := by
  ext x
  rw [mem_weightSpace_iff, mem_formsOfDegree]
  refine forall_congr' fun w => ?_
  rw [codegree_eq_iff hm, not_imp_comm]

/-- [proved-derived; formal-checked] **T3**: the weight space of `−m` is the forms of degree
`n + m`. -/
theorem weightSpace_neg_eq_formsOfDegree (m : ℕ) :
    (torusTriple n).weightSpace (-(m : ℝ)) = formsOfDegree n (n + m) := by
  ext x
  rw [mem_weightSpace_iff, mem_formsOfDegree]
  refine forall_congr' fun w => ?_
  have key : (n : ℝ) - degree w = -(m : ℝ) ↔ degree w = n + m := by
    constructor
    · intro h
      have : (degree w : ℝ) = ((n + m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · intro h
      rw [h]
      push_cast
      ring
  rw [key, not_imp_comm]

/-! ## T4. Hard Lefschetz for the torus -/

/-- [proved-derived; formal-checked] **T4, hard Lefschetz with its constant**: for `m ≤ n` and a
form `x` of degree `n − m`, `m! ‖x‖ ≤ ‖L^m x‖`. -/
theorem hard_lefschetz_degree {m : ℕ} (hm : m ≤ n) {x : Forms n}
    (hx : x ∈ formsOfDegree n (n - m)) :
    (m.factorial : ℝ) * ‖x‖ ≤ ‖(lefschetz n)^[m] x‖ :=
  (torusTriple n).hard_lefschetz m
    (Triple.mem_weightSpace.mp ((weightSpace_eq_formsOfDegree hm).symm ▸ hx))

/-- [proved-derived; formal-checked] **T4**: `L^m` kills no nonzero form of degree `n − m`. -/
theorem iterate_injective_degree {m : ℕ} (hm : m ≤ n) {x : Forms n}
    (hx : x ∈ formsOfDegree n (n - m)) (h : (lefschetz n)^[m] x = 0) : x = 0 :=
  (torusTriple n).eq_zero_of_iterate_eq_zero m
    (Triple.mem_weightSpace.mp ((weightSpace_eq_formsOfDegree hm).symm ▸ hx)) h

/-- [proved-derived; formal-checked] **T4, the Hodge–Riemann identity on primitives**: for `m ≤ n`,
`x` of degree `n − m` with `Λ x = 0`, and `j ≤ m`,
`⟪L^j x, L^j y⟫ = j! · m!/(m − j)! · ⟪x, y⟫`. -/
theorem inner_iterate_primitive_degree {m : ℕ} (hm : m ≤ n) {x : Forms n}
    (hx : x ∈ formsOfDegree n (n - m)) (hD : dualLefschetz n x = 0) (y : Forms n) {j : ℕ}
    (hj : j ≤ m) :
    ⟪(lefschetz n)^[j] x, (lefschetz n)^[j] y⟫ =
      ((j.factorial : ℝ) * (m.descFactorial j : ℝ)) * ⟪x, y⟫ :=
  (torusTriple n).inner_iterate_primitive_nat m
    (Triple.mem_weightSpace.mp ((weightSpace_eq_formsOfDegree hm).symm ▸ hx)) hD y hj

/-- [definition] **T4, hard Lefschetz as an isomorphism**: for `m ≤ n`, `L^m` from the forms of
degree `n − m` onto the forms of degree `n + m`. -/
noncomputable def lefschetzDegreeEquiv {m : ℕ} (hm : m ≤ n) :
    formsOfDegree n (n - m) ≃ₗ[ℝ] formsOfDegree n (n + m) :=
  (LinearEquiv.ofEq _ _ (weightSpace_eq_formsOfDegree hm).symm).trans
    (((torusTriple n).lefschetzEquiv m).trans
      (LinearEquiv.ofEq _ _ (weightSpace_neg_eq_formsOfDegree m)))

/-- [proved-derived; formal-checked] The isomorphism is `L^m`. -/
theorem lefschetzDegreeEquiv_apply {m : ℕ} (hm : m ≤ n) (x : formsOfDegree n (n - m)) :
    (lefschetzDegreeEquiv hm x : Forms n) = (lefschetz n ^ m) x := rfl

/-- [proved-derived; formal-checked] **T4**: for `m ≤ n` the forms of degree `n − m` and `n + m`
have one dimension. -/
theorem finrank_formsOfDegree_symm {m : ℕ} (hm : m ≤ n) :
    Module.finrank ℝ (formsOfDegree n (n - m)) = Module.finrank ℝ (formsOfDegree n (n + m)) :=
  (lefschetzDegreeEquiv hm).finrank_eq

/-! ## Audit -/

section Audit

#print axioms inner_lowerAt
#print axioms raiseAt_lowerAt_of_ne
#print axioms raiseAt_lowerAt_self
#print axioms weightAt_lowerAt_of_ne
#print axioms weightAt_lowerAt_self
#print axioms inner_lefschetz
#print axioms comm_lefschetz
#print axioms lower_lefschetz
#print axioms torusTriple
#print axioms weight_apply
#print axioms weight_single
#print axioms mem_weightSpace_iff
#print axioms weightSpace_eq_formsOfDegree
#print axioms weightSpace_neg_eq_formsOfDegree
#print axioms hard_lefschetz_degree
#print axioms iterate_injective_degree
#print axioms inner_iterate_primitive_degree
#print axioms lefschetzDegreeEquiv
#print axioms lefschetzDegreeEquiv_apply
#print axioms finrank_formsOfDegree_symm

end Audit

end Holonics.Hodge.TorusLefschetzTriple
