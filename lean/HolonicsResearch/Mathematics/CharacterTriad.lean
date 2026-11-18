import Mathlib

/-!
# A law of composition across a place is held by triads, its characters

[proved-standard] The source is the triad record of November 12
(`research/records/2026-11-12_THE_LAW_ACROSS_A_PLACE_IS_HELD_BY_A_PUMPED_CONTACT_A_TRIAD_IS_A_CHARACTER_OF_A_LAW_OF_COMPOSITION_AND_ITS_THREE_LEGS_EXCHANGE_EQUAL_QUANTA.md`,
§3.1; atlas `code.triad-character-of-composition`). A place stands between a left reading `L` and a right reading `R`,
and the law across it is `x = L + R` in a finite abelian group. A character `ψ` gives the complex triad
`ψ(x) · conj ψ(L) · conj ψ(R)`: a left, a letter's and a right reading multiplied.

What is proved.

1. **On any finite abelian group** the triad of a character is the character of `x − L − R` (`triad_eq`), it reads one
   on the law (`triad_on_law`), its phase adds across its legs (`phase_adds`), and the characters' triads hold the law:
   `[x = L + R] = (1/|G|) Σ_ψ ψ(x) conj ψ(L) conj ψ(R)` (`composition_by_characters`). The triads of `ψ` and `ψ⁻¹`
   are conjugate (`triad_inv`), so the real parts hold it (`composition_by_real_parts`).
2. **On `ℤ/n`** with `χ_k(m) = ω^(km)` for a primitive `n`-th root of unity `ω`:
   `[x = L + R] = (1/n) Σ_k χ_k(x) conj χ_k(L) conj χ_k(R)` (`composition_zmod`); the terms for `k` and `n − k` are
   conjugate (`term_neg`); and the real parts of `⌊n/2⌋ + 1` triads hold the law, each counted once where `k = −k`
   and twice elsewhere (`composition_by_half_the_triads`, on `fold`, `fold_image` and `fold_fibre_card`). The triad at
   `k = 0` is the constant one (`term_zero`), so `⌊n/2⌋` triads read anything: four on `ℤ/8`.
3. **With `L` and `R` fair and independent every pair term reads nothing.** Each pair `(L, x)` and each pair `(R, x)`
   is met by one pair `(L, R)` (`left_and_sum_meet_once`, `right_and_sum_meet_once`), so the counts multiply
   (`left_pair_reads_nothing`, `right_pair_reads_nothing`): `x` is independent of `L` alone and of `R` alone, while
   `(L, R)` fixes `x`.

Limits. Statement 3 is independence in its counting form on the uniform law of `(L, R)`; the mutual informations
`I(x; L) = I(x; R) = 0` and `I(x; L, R) = H(x)` follow from it and are not stated with an entropy. A law of composition
that is not a group's (text) has no such finite character sum; how much of it a count of triads holds is the record's
ruler and is not a theorem here.

The computational object is the helical pair interaction: a triad is a pumped contact, the product of two pair
readings with the place's own. Of the winding guide's six general objects this touches the pair (the legs `L` and `R`
against the place), the helix (a character is a turn whose phase adds) and faces and placement (the indicator is the
face of the law); cell holonomy, the tube and the tower thread stay attached.

Consumers: #410's box "A law of composition across a place is held by triads, its characters"; atlas
`code.triad-character-of-composition` and `contact.pair-product-owes-site-leg`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.CharacterTriad

open Finset
open scoped ComplexConjugate

/-! ## 1. Any finite abelian group -/

section Group

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The triad of a character at a place: the letter's reading against the left's and the right's. -/
noncomputable def triad (ψ : AddChar G ℂ) (x L R : G) : ℂ := ψ x * conj (ψ L) * conj (ψ R)

/-- [proved-standard] **A triad is one character of the place's defect**: `ψ(x) conj ψ(L) conj ψ(R) = ψ(x − L − R)`. -/
theorem triad_eq (ψ : AddChar G ℂ) (x L R : G) : triad ψ x L R = ψ (x - L - R) := by
  unfold triad
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  abel

omit [Fintype G] in
/-- [proved-standard] **The phase adds across the legs**: `ψ(L + R) = ψ(L) ψ(R)`. -/
theorem phase_adds (ψ : AddChar G ℂ) (L R : G) : ψ (L + R) = ψ L * ψ R :=
  AddChar.map_add_eq_mul ψ L R

/-- [proved-standard] **On the law every triad reads one.** -/
theorem triad_on_law (ψ : AddChar G ℂ) (L R : G) : triad ψ (L + R) L R = 1 := by
  rw [triad_eq]
  have h : L + R - L - R = 0 := by abel
  rw [h, AddChar.map_zero_eq_one]

/-- [proved-standard] **The triads of a character and of its inverse are conjugate.** -/
theorem triad_inv (ψ : AddChar G ℂ) (x L R : G) : triad ψ⁻¹ x L R = conj (triad ψ x L R) := by
  rw [triad_eq, triad_eq, AddChar.inv_apply, AddChar.map_neg_eq_conj]

variable [DecidableEq G]

/-- [proved-standard] **The characters' triads hold the law of composition**:
`[x = L + R] = (1/|G|) Σ_ψ ψ(x) conj ψ(L) conj ψ(R)`. -/
theorem composition_by_characters (x L R : G) :
    (if x = L + R then (1 : ℂ) else 0) = (1 / (Fintype.card G : ℂ)) * ∑ ψ : AddChar G ℂ, triad ψ x L R := by
  simp_rw [triad_eq]
  rw [AddChar.sum_apply_eq_ite]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hiff : x - L - R = 0 ↔ x = L + R := by
    rw [sub_sub, sub_eq_zero]
  by_cases h : x = L + R
  · rw [if_pos h, if_pos (hiff.mpr h)]
    field_simp
  · rw [if_neg h, if_neg (mt hiff.mp h)]
    simp

/-- [proved-standard] **The real parts of the triads hold the law.** -/
theorem composition_by_real_parts (x L R : G) :
    (if x = L + R then (1 : ℝ) else 0) = (1 / (Fintype.card G : ℝ)) * ∑ ψ : AddChar G ℂ, (triad ψ x L R).re := by
  have h := congrArg Complex.re (composition_by_characters x L R)
  have hcoef : (1 / (Fintype.card G : ℂ)) = ((1 / (Fintype.card G : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcoef, Complex.re_ofReal_mul, Complex.re_sum] at h
  rw [← h]
  split_ifs <;> simp

/-! ### Fair and independent legs -/

/-- [proved-standard] **A left reading and a sum are met by one pair**: for every `l` and `s` one pair `(L, R)` has
`L = l` and `L + R = s`. -/
theorem left_and_sum_meet_once (l s : G) : #{p : G × G | p.1 = l ∧ p.1 + p.2 = s} = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨(l, s - l), ?_⟩
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, by abel⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, by abel⟩

/-- [proved-standard] **A right reading and a sum are met by one pair.** -/
theorem right_and_sum_meet_once (r s : G) : #{p : G × G | p.2 = r ∧ p.1 + p.2 = s} = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨(s - r, r), ?_⟩
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨by abel, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, by abel⟩

/-- [proved-standard] Each value of the sum is met by `|G|` pairs: the sum of fair independent legs is fair. -/
theorem sum_fibre_card (s : G) : #{p : G × G | p.1 + p.2 = s} = Fintype.card G := by
  have himage : ({p : G × G | p.1 + p.2 = s} : Finset (G × G)) = Finset.univ.image fun a : G => (a, s - a) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro rfl
      exact ⟨a, rfl, by abel⟩
    · rintro ⟨c, rfl, rfl⟩
      abel
  rw [himage, Finset.card_image_of_injective _ fun a b h => (Prod.mk.inj h).1, Finset.card_univ]

omit [AddCommGroup G] in
/-- [proved-standard] Each left reading is met by `|G|` pairs. -/
theorem left_fibre_card (l : G) : #{p : G × G | p.1 = l} = Fintype.card G := by
  have himage : ({p : G × G | p.1 = l} : Finset (G × G)) = Finset.univ.image fun b : G => (l, b) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro rfl
      exact ⟨b, rfl, rfl⟩
    · rintro ⟨c, rfl, rfl⟩
      rfl
  rw [himage, Finset.card_image_of_injective _ fun a b h => (Prod.mk.inj h).2, Finset.card_univ]

omit [AddCommGroup G] in
/-- [proved-standard] Each right reading is met by `|G|` pairs. -/
theorem right_fibre_card (r : G) : #{p : G × G | p.2 = r} = Fintype.card G := by
  have himage : ({p : G × G | p.2 = r} : Finset (G × G)) = Finset.univ.image fun a : G => (a, r) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro rfl
      exact ⟨a, rfl, rfl⟩
    · rintro ⟨c, rfl, rfl⟩
      rfl
  rw [himage, Finset.card_image_of_injective _ fun a b h => (Prod.mk.inj h).1, Finset.card_univ]

/-- [proved-standard] **The pair of the left leg and the place reads nothing**: under fair independent legs the count of
`(L = l, x = s)` times the count of all pairs is the count of `L = l` times the count of `x = s`. -/
theorem left_pair_reads_nothing (l s : G) :
    #{p : G × G | p.1 = l ∧ p.1 + p.2 = s} * Fintype.card (G × G) =
      #{p : G × G | p.1 = l} * #{p : G × G | p.1 + p.2 = s} := by
  rw [left_and_sum_meet_once, left_fibre_card, sum_fibre_card, Fintype.card_prod, one_mul]

/-- [proved-standard] **The pair of the right leg and the place reads nothing.** -/
theorem right_pair_reads_nothing (r s : G) :
    #{p : G × G | p.2 = r ∧ p.1 + p.2 = s} * Fintype.card (G × G) =
      #{p : G × G | p.2 = r} * #{p : G × G | p.1 + p.2 = s} := by
  rw [right_and_sum_meet_once, right_fibre_card, sum_fibre_card, Fintype.card_prod, one_mul]

end Group

/-! ## 2. The chart on `ℤ/n` -/

section ZModChart

variable {n : ℕ} [NeZero n]

/-- The character `χ_k(m) = ω^(km)` of `ℤ/n`, the product taken on the least residues. -/
noncomputable def chi (ω : ℂ) (k m : ZMod n) : ℂ := ω ^ (k.val * m.val)

/-- The `k`-th term of the law: `χ_k(x) conj χ_k(L) conj χ_k(R)`. -/
noncomputable def term (ω : ℂ) (k x L R : ZMod n) : ℂ := chi ω k x * conj (chi ω k L) * conj (chi ω k R)

/-- [proved-standard] `χ_k(m)` is the root's character at the product `k·m` of `ℤ/n`. -/
theorem chi_eq_zmodChar {ω : ℂ} (hω : ω ^ n = 1) (k m : ZMod n) : chi ω k m = AddChar.zmodChar n hω (k * m) := by
  rw [AddChar.zmodChar_apply, ZMod.val_mul, ← pow_eq_pow_mod _ hω]
  rfl

/-- [proved-standard] **The phase adds across the legs**: `χ_k(L + R) = χ_k(L) χ_k(R)`. -/
theorem chi_add {ω : ℂ} (hω : ω ^ n = 1) (k a b : ZMod n) : chi ω k (a + b) = chi ω k a * chi ω k b := by
  rw [chi_eq_zmodChar hω, chi_eq_zmodChar hω, chi_eq_zmodChar hω, mul_add, AddChar.map_add_eq_mul]

/-- [proved-standard] `χ_(n−k) = conj χ_k`. -/
theorem chi_neg {ω : ℂ} (hω : ω ^ n = 1) (k m : ZMod n) : chi ω (-k) m = conj (chi ω k m) := by
  rw [chi_eq_zmodChar hω, chi_eq_zmodChar hω, neg_mul, AddChar.map_neg_eq_conj]

/-- [proved-standard] A term is the root's character at `k (x − L − R)`. -/
theorem term_eq {ω : ℂ} (hω : ω ^ n = 1) (k x L R : ZMod n) :
    term ω k x L R = AddChar.zmodChar n hω (k * (x - L - R)) := by
  unfold term
  rw [chi_eq_zmodChar hω, chi_eq_zmodChar hω, chi_eq_zmodChar hω, ← AddChar.map_neg_eq_conj,
    ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- [proved-standard] **The terms for `k` and `n − k` are conjugate.** -/
theorem term_neg {ω : ℂ} (hω : ω ^ n = 1) (k x L R : ZMod n) : term ω (-k) x L R = conj (term ω k x L R) := by
  rw [term_eq hω, term_eq hω, neg_mul, AddChar.map_neg_eq_conj]

/-- [proved-standard] On the law every term reads one. -/
theorem term_on_law {ω : ℂ} (hω : ω ^ n = 1) (k L R : ZMod n) : term ω k (L + R) L R = 1 := by
  rw [term_eq hω]
  have h : k * (L + R - L - R) = 0 := by ring
  rw [h, AddChar.map_zero_eq_one]

omit [NeZero n] in
/-- [proved-standard] **The triad at `k = 0` is the constant one**, so the triads that read anything number `⌊n/2⌋`:
four on `ℤ/8`, the count at which the record's ruler held `x = L + R mod 8` whole. -/
theorem term_zero (ω : ℂ) (x L R : ZMod n) : term ω 0 x L R = 1 := by
  simp [term, chi]

/-- [proved-standard] **The characters of `ℤ/n` hold its law of composition**: with `ω` a primitive `n`-th root of
unity, `[x = L + R] = (1/n) Σ_k χ_k(x) conj χ_k(L) conj χ_k(R)`. -/
theorem composition_zmod {ω : ℂ} (hω : IsPrimitiveRoot ω n) (x L R : ZMod n) :
    (if x = L + R then (1 : ℂ) else 0) = (1 / (n : ℂ)) * ∑ k : ZMod n, term ω k x L R := by
  have hpow : ω ^ n = 1 := ((IsPrimitiveRoot.iff_def ω n).mp hω).left
  have hprim := AddChar.zmodChar_primitive_of_primitive_root n hω
  simp_rw [term_eq hpow]
  rw [AddChar.sum_mulShift (x - L - R) hprim, ZMod.card]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hiff : x - L - R = 0 ↔ x = L + R := by
    rw [sub_sub, sub_eq_zero]
  by_cases h : x = L + R
  · rw [if_pos h, if_pos (hiff.mpr h)]
    field_simp
  · rw [if_neg h, if_neg (mt hiff.mp h)]
    simp

/-- [proved-standard] **The real parts of the terms hold the law.** -/
theorem composition_zmod_real {ω : ℂ} (hω : IsPrimitiveRoot ω n) (x L R : ZMod n) :
    (if x = L + R then (1 : ℝ) else 0) = (1 / (n : ℝ)) * ∑ k : ZMod n, (term ω k x L R).re := by
  have h := congrArg Complex.re (composition_zmod hω x L R)
  have hcoef : (1 / (n : ℂ)) = ((1 / (n : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcoef, Complex.re_ofReal_mul, Complex.re_sum] at h
  rw [← h]
  split_ifs <;> simp

/-! ### The fold of `ℤ/n` by `k ↦ n − k` -/

/-- The fold of `ℤ/n` by negation: the lesser of the least residues of `k` and of `−k`. -/
def fold (k : ZMod n) : ℕ := min k.val (n - k.val)

/-- [proved-standard] The fold lands in `0, …, ⌊n/2⌋`. -/
theorem fold_le (k : ZMod n) : fold k ≤ n / 2 := by
  unfold fold
  have := ZMod.val_lt k
  omega

/-- [proved-standard] The fold reads `k` and `−k` alike. -/
theorem fold_neg (k : ZMod n) : fold (-k) = fold k := by
  unfold fold
  rw [ZMod.neg_val]
  split_ifs with h
  · subst h
    simp
  · have hlt := ZMod.val_lt k
    have hpos : 0 < k.val := Nat.pos_of_ne_zero fun h0 => h ((ZMod.val_eq_zero k).mp h0)
    omega

/-- [proved-standard] The fold fixes `0, …, ⌊n/2⌋`. -/
theorem fold_natCast {j : ℕ} (hj : j ≤ n / 2) : fold (j : ZMod n) = j := by
  unfold fold
  have hn : 0 < n := NeZero.pos n
  rw [ZMod.val_natCast_of_lt (by omega)]
  omega

/-- [proved-standard] **A fibre of the fold is a class `{k, −k}`.** -/
theorem fold_eq_iff {j : ℕ} (hj : j ≤ n / 2) (k : ZMod n) : fold k = j ↔ k = (j : ZMod n) ∨ k = -(j : ZMod n) := by
  constructor
  · intro h
    unfold fold at h
    have hlt := ZMod.val_lt k
    rcases Nat.le_total k.val (n - k.val) with hle | hle
    · left
      rw [Nat.min_eq_left hle] at h
      rw [← h, ZMod.natCast_zmod_val]
    · right
      rw [Nat.min_eq_right hle] at h
      rw [← h, Nat.cast_sub hlt.le, ZMod.natCast_self, ZMod.natCast_zmod_val]
      simp
  · rintro (rfl | rfl)
    · exact fold_natCast hj
    · rw [fold_neg]
      exact fold_natCast hj

/-- [proved-standard] **The fold has `⌊n/2⌋ + 1` classes.** -/
theorem fold_image : (Finset.univ.image (fold : ZMod n → ℕ)) = Finset.range (n / 2 + 1) := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    have := fold_le k
    omega
  · intro hj
    exact ⟨(j : ZMod n), fold_natCast (by omega)⟩

/-- [proved-standard] The count of classes of `k ↦ n − k` on `ℤ/n` is `⌊n/2⌋ + 1`. -/
theorem fold_classes_card : (Finset.univ.image (fold : ZMod n → ℕ)).card = n / 2 + 1 := by
  rw [fold_image, Finset.card_range]

/-- [proved-standard] **A class holds one member where `k = −k` and two elsewhere**: the fibre over `j ≤ ⌊n/2⌋` has
one member when `j = 0` or `2j = n`, and two otherwise. -/
theorem fold_fibre_card {j : ℕ} (hj : j ≤ n / 2) :
    #{k : ZMod n | fold k = j} = if j = 0 ∨ 2 * j = n then 1 else 2 := by
  have hn : 0 < n := NeZero.pos n
  have hset : ({k : ZMod n | fold k = j} : Finset (ZMod n)) = {(j : ZMod n), -(j : ZMod n)} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    exact fold_eq_iff hj k
  have hself : (j : ZMod n) = -(j : ZMod n) ↔ j = 0 ∨ 2 * j = n := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    constructor
    · intro hdvd
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · exact Or.inl h0
      · right
        have hle := Nat.le_of_dvd (by omega) hdvd
        omega
    · rintro (rfl | h)
      · simp
      · rw [← two_mul, h]
  rw [hset]
  by_cases h : j = 0 ∨ 2 * j = n
  · rw [if_pos h, ← hself.mpr h]
    simp
  · rw [if_neg h]
    exact Finset.card_pair fun heq => h (hself.mp heq)

/-- [proved-standard] **A sum that reads `k` and `−k` alike is a sum over the fold's classes.** -/
theorem sum_fold (f : ZMod n → ℝ) (hf : ∀ k, f (-k) = f k) :
    ∑ k : ZMod n, f k =
      ∑ j ∈ Finset.range (n / 2 + 1), (if j = 0 ∨ 2 * j = n then (1 : ℝ) else 2) * f (j : ZMod n) := by
  have hmaps : ∀ k ∈ (Finset.univ : Finset (ZMod n)), fold k ∈ Finset.range (n / 2 + 1) := by
    intro k _
    have := fold_le k
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n / 2 := by
    have := Finset.mem_range.mp hj
    omega
  have hconst : ∀ k ∈ ({k : ZMod n | fold k = j} : Finset (ZMod n)), f k = f (j : ZMod n) := by
    intro k hk
    rcases (fold_eq_iff hj' k).mp (Finset.mem_filter.mp hk).2 with rfl | rfl
    · rfl
    · exact hf _
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, fold_fibre_card hj']
  split_ifs <;> simp

/-- [proved-standard] **The real parts of `⌊n/2⌋ + 1` complex triads hold the law**: the terms `k = 0, …, ⌊n/2⌋`,
each counted once where `k = −k` and twice elsewhere. -/
theorem composition_by_half_the_triads {ω : ℂ} (hω : IsPrimitiveRoot ω n) (x L R : ZMod n) :
    (if x = L + R then (1 : ℝ) else 0) =
      (1 / (n : ℝ)) * ∑ j ∈ Finset.range (n / 2 + 1),
        (if j = 0 ∨ 2 * j = n then (1 : ℝ) else 2) * (term ω (j : ZMod n) x L R).re := by
  have hpow : ω ^ n = 1 := ((IsPrimitiveRoot.iff_def ω n).mp hω).left
  rw [composition_zmod_real hω x L R]
  congr 1
  refine sum_fold (fun k => (term ω k x L R).re) fun k => ?_
  rw [term_neg hpow, Complex.conj_re]

end ZModChart

end Holonics.Mathematics.CharacterTriad
