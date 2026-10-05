import Holonics.Compression.Core.Cost

/-!
# A located code's length is invariant under relabelling; a residue chart's is not

[definition] A **code** assigns each class of a finite alphabet its codeword (`Code`); the code of a
passage is its classes' codewords in passage order (`encode`), and its length is the passage's
description length (`codeLength`, the sum of codeword lengths, `codeLength_eq_sum`). **Relabelling**
by a permutation `π` of the classes carries the passage `x` to `π∘x` and a code `c` to `c∘π⁻¹`, the
class `π a` taking `a`'s codeword (`relabel`). Exactly, with no logarithm: the Kraft sum
`Σ_a 2^(−ℓ_a)` is an exact rational (`kraftSum`), a class law `p` gives a passage its mass
`Π_k p(x_k)` (`passageMass`), and a code's dyadic law `2^(−ℓ)` gives the passage the mass
`2^(−L(x))` (`passageMass_dyadic`): the code length is the exponent of the passage's dyadic mass,
its `−log₂`.

[definition] A **coder** locates a code from the passage it reads (`Coder`); it is **carried** when
the code it locates on `π∘x` is the code it locates on `x`, relabelled by `π` (`Carried`): the
labels enter only the boundary's decoder. This is the relabelling law of the located route
(Rust `compression::keys::transport`, `TransportLocation`, `located_code`; record
`2026-10-05_THE_LOCATED_TRANSPORT…` §8 item 3 and §10 item 6), whose first half, "the survivors on
`π∘x` are those on `x` carried by `π`", is the hypothesis `Carried`.

[proved-derived; formal-checked] What is proved (#374 §8 item 3, #379 item 6).
1. **Relabelling the passage and the code by the same `π` changes no bit** (`encode_relabel`), so
   every passage's code length is unchanged (`codeLength_relabel`); the code stays prefix-free
   (`prefixFree_relabel`), its Kraft sum is unchanged (`kraftSum_relabel`), and so is every
   passage's mass under a relabelled class law (`passageMass_relabel`).
2. **A carried coder's code is invariant**: its bits and its length on `π∘x` are those on `x`
   (`carried_encode`, `carried_codeLength`). Two carried coders: codewords chosen by a class's
   first occurrence in the passage (`firstOccurrence_carried`, the located route's gauge
   representative orders the classes this way), and lengths read from the class's occurrence count
   (`countLengths_carried`, `totalLength_relabel`).
3. **A uniform width is invariant even in a residue chart** (`uniform_codeLength_relabel`): the
   literal code (`Core/Cost.literalCode`, each class's index in fixed width) keeps its length under
   every relabelling (`literalCode_length_relabel`).

[counterexample; formal-checked] **The residue chart is not carried** (`residue*`). On the three
classes `ℤ/3` (`Fin 3`), the prefix code `0 ↦ 0`, `1 ↦ 10`, `2 ↦ 11` chosen by the class's numeric
residue (`residueCode`, prefix-free, Kraft sum `1`) is kept on the numeric values when the ring
turns `u ↦ u + 1`. The one-class passage `0` costs `1` bit and its turned passage `1` costs `2`
(`residue_codeLength_moves`); its dyadic mass moves from `1/2` to `1/4` (`residue_mass_moves`);
so the constant coder of the residue chart is not carried (`residue_not_carried`).

Owed in #62: that the located route's survivors on `π∘x` are those on `x` carried by `π` (the
hypothesis `Carried` for `TransportLocation` itself), which needs the location's law stated in Lean.
-/

namespace Holonics.Compression.Relabelling

open Holonics.Compression.Core.Cost

/-- [definition] **A code**: each class's codeword. -/
abbrev Code (A : Type*) := A → List Bool

variable {A : Type*}

/-- [definition] The code of a passage: its classes' codewords in passage order. -/
def encode (c : Code A) (x : List A) : List Bool := x.flatMap c

/-- [definition] **The passage's code length** (its description length in this code). -/
def codeLength (c : Code A) (x : List A) : ℕ := (encode c x).length

theorem codeLength_cons (c : Code A) (a : A) (x : List A) :
    codeLength c (a :: x) = (c a).length + codeLength c x := by
  simp [codeLength, encode]

/-- [proved-derived; formal-checked] The code length is the sum of the codewords' lengths. -/
theorem codeLength_eq_sum (c : Code A) (x : List A) :
    codeLength c x = (x.map fun a => (c a).length).sum := by
  induction x with
  | nil => simp [codeLength, encode]
  | cons a x ih => rw [codeLength_cons, ih, List.map_cons, List.sum_cons]

/-- [definition] A code is **prefix-free** when no class's codeword begins another class's. -/
def PrefixFree (c : Code A) : Prop := ∀ a b, c a <+: c b → a = b

/-- [definition] **Relabelling a code** by `π`: the class `π a` takes `a`'s codeword. -/
def relabel (π : Equiv.Perm A) (c : Code A) : Code A := fun b => c (π.symm b)

@[simp] theorem relabel_apply (π : Equiv.Perm A) (c : Code A) (a : A) :
    relabel π c (π a) = c a := by
  simp [relabel]

/-- [proved-derived; formal-checked] **Relabelling the passage and the code by the same `π` changes
no bit.** -/
theorem encode_relabel (π : Equiv.Perm A) (c : Code A) (x : List A) :
    encode (relabel π c) (x.map π) = encode c x := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    simp only [encode, List.map_cons, List.flatMap_cons, relabel_apply] at ih ⊢
    rw [ih]

/-- [proved-derived; formal-checked] **The code length is invariant under relabelling.** -/
theorem codeLength_relabel (π : Equiv.Perm A) (c : Code A) (x : List A) :
    codeLength (relabel π c) (x.map π) = codeLength c x := by
  rw [codeLength, encode_relabel, codeLength]

/-- [proved-derived; formal-checked] Relabelling keeps a code prefix-free, and only a prefix-free
code relabels to one. -/
theorem prefixFree_relabel (π : Equiv.Perm A) (c : Code A) :
    PrefixFree (relabel π c) ↔ PrefixFree c := by
  constructor
  · intro h a b hab
    exact π.injective (h (π a) (π b) (by simpa using hab))
  · intro h a b hab
    exact π.symm.injective (h (π.symm a) (π.symm b) hab)

/-- [definition] **The Kraft sum** of codeword lengths, `Σ_a 2^(−ℓ_a)`, an exact rational. -/
def kraftSum [Fintype A] (ℓ : A → ℕ) : ℚ := ∑ a, (1 / 2 : ℚ) ^ ℓ a

/-- [proved-derived; formal-checked] **The Kraft sum is invariant under relabelling.** -/
theorem kraftSum_relabel [Fintype A] (π : Equiv.Perm A) (ℓ : A → ℕ) :
    kraftSum (fun b => ℓ (π.symm b)) = kraftSum ℓ :=
  Equiv.sum_comp π.symm fun a => (1 / 2 : ℚ) ^ ℓ a

/-- [definition] **The passage's mass** under a class law `p`, `Π_k p(x_k)`; its description length
is `−log₂` of it. -/
def passageMass (p : A → ℚ) (x : List A) : ℚ := (x.map p).prod

/-- [proved-derived; formal-checked] **The passage's mass is invariant under relabelling** the
passage and the class law by the same `π`. -/
theorem passageMass_relabel (π : Equiv.Perm A) (p : A → ℚ) (x : List A) :
    passageMass (fun b => p (π.symm b)) (x.map π) = passageMass p x := by
  simp [passageMass, List.map_map, Function.comp_def]

/-- [proved-derived; formal-checked] **The code length is the exponent of the passage's dyadic
mass**: under a code's dyadic law `2^(−ℓ)`, the passage has mass `2^(−L(x))`. -/
theorem passageMass_dyadic (c : Code A) (x : List A) :
    passageMass (fun a => (1 / 2 : ℚ) ^ (c a).length) x = (1 / 2 : ℚ) ^ codeLength c x := by
  induction x with
  | nil => simp [passageMass, codeLength, encode]
  | cons a x ih =>
    rw [codeLength_cons, pow_add, ← ih]
    simp [passageMass]

/-! ## Located codes -/

/-- [definition] **A coder** locates a code from the passage it reads. -/
abbrev Coder (A : Type*) := List A → Code A

/-- [definition] A coder is **carried** by relabelling when the code it locates on `π∘x` is the code
it locates on `x`, relabelled by `π`. -/
def Carried (K : Coder A) : Prop :=
  ∀ (π : Equiv.Perm A) (x : List A), K (x.map π) = relabel π (K x)

/-- [proved-derived; formal-checked] **A carried coder's bits are invariant under relabelling.** -/
theorem carried_encode {K : Coder A} (hK : Carried K) (π : Equiv.Perm A) (x : List A) :
    encode (K (x.map π)) (x.map π) = encode (K x) x := by
  rw [hK, encode_relabel]

/-- [proved-derived; formal-checked] **A located code's length is invariant under relabelling.** -/
theorem carried_codeLength {K : Coder A} (hK : Carried K) (π : Equiv.Perm A) (x : List A) :
    codeLength (K (x.map π)) (x.map π) = codeLength (K x) x := by
  rw [codeLength, carried_encode hK, codeLength]

theorem idxOf_map_perm [DecidableEq A] (π : Equiv.Perm A) (x : List A) (a : A) :
    (x.map π).idxOf (π a) = x.idxOf a := by
  induction x with
  | nil => simp
  | cons b x ih =>
    by_cases hb : b = a
    · subst hb
      rw [List.map_cons, List.idxOf_cons_eq _ rfl, List.idxOf_cons_eq _ rfl]
    · have hπ : π b ≠ π a := fun h => hb (π.injective h)
      rw [List.map_cons, List.idxOf_cons_ne _ hπ, List.idxOf_cons_ne _ hb, ih]

/-- [definition] **The first-occurrence coder**: a class's codeword is chosen by the place of its
first occurrence in the passage, `w(idx_x(a))`. -/
def firstOccurrence [DecidableEq A] (w : ℕ → List Bool) : Coder A :=
  fun x a => w (x.idxOf a)

/-- [proved-derived; formal-checked] **The first-occurrence coder is carried**: a class's first
occurrence in `π∘x` is the first occurrence of its preimage in `x`. -/
theorem firstOccurrence_carried [DecidableEq A] (w : ℕ → List Bool) :
    Carried (firstOccurrence (A := A) w) := by
  intro π x
  funext b
  simp only [firstOccurrence, relabel]
  conv_lhs => rw [← π.apply_symm_apply b]
  rw [idxOf_map_perm]

/-- [definition] A length assignment located from the passage. -/
abbrev LengthCoder (A : Type*) := List A → A → ℕ

/-- [definition] A located length assignment is carried by relabelling. -/
def LengthCarried (L : LengthCoder A) : Prop :=
  ∀ (π : Equiv.Perm A) (x : List A) (a : A), L (x.map π) (π a) = L x a

/-- [definition] The passage's total length under a located length assignment. -/
def totalLength (L : LengthCoder A) (x : List A) : ℕ := (x.map (L x)).sum

/-- [proved-derived; formal-checked] **A carried length assignment's total is invariant.** -/
theorem totalLength_relabel {L : LengthCoder A} (hL : LengthCarried L) (π : Equiv.Perm A)
    (x : List A) : totalLength L (x.map π) = totalLength L x := by
  simp [totalLength, List.map_map, Function.comp_def, hL π x]

/-- [proved-derived; formal-checked] **Lengths read from the occurrence count are carried**: any
length chosen from a class's count and the passage's length moves with the labels. -/
theorem countLengths_carried [DecidableEq A] (f : ℕ → ℕ → ℕ) :
    LengthCarried (fun (x : List A) a => f (x.count a) x.length) := by
  intro π x a
  simp [List.count_map_of_injective _ _ π.injective]

/-- [proved-derived; formal-checked] **A uniform width is invariant under relabelling**, whatever
chart assigns the codewords. -/
theorem uniform_codeLength_relabel {c c' : Code A} {w : ℕ} (hc : ∀ a, (c a).length = w)
    (hc' : ∀ a, (c' a).length = w) (π : Equiv.Perm A) (x : List A) :
    codeLength c' (x.map π) = codeLength c x := by
  rw [codeLength_eq_sum, codeLength_eq_sum, List.map_map]
  simp [Function.comp_def, hc, hc']

/-- [proved-derived; formal-checked] **The literal code's length is invariant under relabelling**
(`Core/Cost.literalCode_length`: fixed width `⌈log₂ |A|⌉` per class). -/
theorem literalCode_length_relabel [Fintype A] (π : Equiv.Perm A) (x : List A) :
    (literalCode (x.map π)).length = (literalCode x).length := by
  rw [literalCode_length, literalCode_length, literalBits, literalBits, List.length_map]

/-! ## The residue chart on `ℤ/3` -/

/-- [definition] **The residue chart** on three classes: the codeword is chosen by the class's
numeric residue, `0 ↦ 0`, `1 ↦ 10`, `2 ↦ 11`. -/
def residueCode : Code (Fin 3) := ![[false], [true, false], [true, true]]

/-- [definition] The ring's turn `u ↦ u + 1` on `ℤ/3`. -/
def turn : Equiv.Perm (Fin 3) := Equiv.addRight 1

theorem residueCode_prefixFree : PrefixFree residueCode := by
  unfold PrefixFree
  decide

theorem residueCode_kraftSum : kraftSum (fun a => (residueCode a).length) = 1 := by
  simp [kraftSum, Fin.sum_univ_three, residueCode]
  norm_num

/-- [counterexample; formal-checked] **The residue chart's code length moves under the ring's
turn**: the passage `0` costs one bit, its turned passage `1` costs two. -/
theorem residue_codeLength_moves :
    codeLength residueCode ([0].map turn) = 2 ∧ codeLength residueCode [0] = 1 := by
  decide

/-- [counterexample; formal-checked] Its dyadic mass moves from `1/2` to `1/4`. -/
theorem residue_mass_moves :
    passageMass (fun a => (1 / 2 : ℚ) ^ (residueCode a).length) ([0].map turn) = 1 / 4 ∧
      passageMass (fun a => (1 / 2 : ℚ) ^ (residueCode a).length) [0] = 1 / 2 := by
  rw [passageMass_dyadic, passageMass_dyadic, residue_codeLength_moves.1,
    residue_codeLength_moves.2]
  norm_num

/-- [counterexample; formal-checked] **The residue chart is not carried**: kept on the numeric
values, it is not the turned code. -/
theorem residue_not_carried : ¬ Carried (fun _ : List (Fin 3) => residueCode) := by
  intro h
  have := congrFun (h turn []) 0
  revert this
  decide

section Audit

#print axioms encode_relabel
#print axioms codeLength_relabel
#print axioms prefixFree_relabel
#print axioms kraftSum_relabel
#print axioms passageMass_relabel
#print axioms passageMass_dyadic
#print axioms carried_codeLength
#print axioms firstOccurrence_carried
#print axioms totalLength_relabel
#print axioms countLengths_carried
#print axioms literalCode_length_relabel
#print axioms residueCode_prefixFree
#print axioms residueCode_kraftSum
#print axioms residue_codeLength_moves
#print axioms residue_mass_moves
#print axioms residue_not_carried

end Audit

end Holonics.Compression.Relabelling
