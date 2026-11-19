import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.LinearCombination
import Holonics.Geometry.PhaseCarry

/-!
# Faces are read on cycles: the carry is the Bockstein of the phase, the `th` seam is a class, and selection splits by Hodge parts

[proved-standard] The source is #410's box "Faces read on cycles" (record
`research/records/2026-10-24_FACES_ARE_READ_ON_CYCLES_A_FACE_IS_A_COHOMOLOGY_CLASS_THE_CARRY_IS_ITS_BOCKSTEIN_AND_FRICTION_KEEPS_ONLY_THE_HARMONIC_PART.md`,
§§2, 3, 4, 7 and 9; atlas `face.carry-bockstein`, `lang.seam-class`, `contact.kunneth-interaction-rank`,
`norm.replicator-hodge-parts`). The box's fluid clauses, the viscous step and the HPP collision, are
`Physics/Fluid/FrictionKeepsHarmonic`.

What is proved.

1. **The carry is a 2-cocycle of order `n`** (§1). On `ℤ/n` the carry of the digit lift is
   `carry a b = ⌊(a + b)/n⌋` on the representatives `0 … n − 1`, the repository's `Geometry/PhaseCarry.carry`
   (`carry_eq_phaseCarry`). The lift fails by it, `(a + b) + n·carry a b = a + b` on the digits
   (`val_add_add_carry`), so `n·carry` is the coboundary of the digit itself (`n_mul_carry`,
   `δb(a, b) = b(a) + b(b) − b(a + b)`), and it is a cocycle (`carry_cocycle`). **Read on the lap**: the lap
   `a → a + 1` carries once, `Σ_a carry(a, 1) = 1` (`sum_carry_lap`), while every integer coboundary reads
   `n·b(1)` on it (`sum_delta_lap`). So `k·carry` is an integer coboundary exactly when `n ∣ k`
   (`smul_carry_coboundary_iff`): the class has order `n` in `H²(ℤ/n; ℤ)`, and no integer re-reading of the digit
   removes the carry (`carry_not_coboundary`, `smul_carry_not_coboundary` for `0 < k < n`). **A real chart erases
   it**: over `ℚ` the carry is the coboundary of the phase `a/n` (`carry_eq_phase_coboundary`).
2. **The `th` seam is a rational class of the face monoid** (§2). Over the letters `{t, h, a}`, the count of `th`
   obeys `count(x ++ y) = count x + count y + s(face x, face y)` with `s = [x ends t][y starts h]`
   (`thCount_append`), the face of a word being its first and last letter (`face`, with `face_append`: the face of a
   join is the product `(f, l)(f′, l′) = (f, l′)` of the face monoid `{ε} ∪ {t, h, a}²`, `faceMul`, associative with
   unit `ε`). Upstairs the seam is a coboundary of the count (`seam_eq_count_coboundary`); on the faces it is a
   2-cocycle (`seam_cocycle`, read from the words) and is no rational coboundary: the 2-cycle
   `[at|ha] + [aa|aa] − [at|at] − [ha|ha]` reads `0` on every coboundary and `1` on the seam (`cert_coboundary`,
   `cert_seam`, `seam_not_coboundary`).
3. **The four-cycle reads the Künneth cross part** (§3). For a table `G` on `X × Y`, its cross part
   `G − (row mean) − (column mean) + (mean)` (`cross`) has the same unit four-cycles as `G` (`square_cross`), and these
   are three equivalent: every four-cycle vanishes, the cross part vanishes, and `G` is a sum `u(x) + v(y)`
   (`square_zero_iff_separable`, `cross_zero_iff_separable`). **The interaction rank** is the least number of rank-one
   bilinear terms: a table of rank `r` is a sum of `r` products `a_k(x) b_k(y)` (`exists_sum_rankOne`), and a sum of
   `r` such products has rank at most `r` (`rank_le_of_sum_rankOne`).
4. **Selection splits by Hodge parts** (§4). Under the replicator `ẋ_i = x_i((Ax)_i − xᵀAx)` (`replicator`), the
   simplex is kept (`sum_replicator`); an antisymmetric payoff reads `xᵀKx = 0` (`dot_mulVec_antisymm`) and, with
   zero column sums, conserves `Σ log x_i` along every positive solution (`replicator_log_conserved`, the harmonic
   part's conserved face); a symmetric payoff raises the mean fitness `xᵀSx` at twice the fitness variance
   `2 Σ x_i((Sx)_i − xᵀSx)²` on the simplex (`replicator_mean_rate`, Fisher, from the identity `fisher_identity`).

Limits. The bitwise census of §2 (`a + b = (a ⊕ b) + 2(a ∧ b)` on all byte pairs, the ripple adder, XOR's and `+`'s
plural bits) and the ranks of the face tables of §3 (9, 9, 7, 1, 0, 4, 1, 1, 1) stay checked by the record's
receipts; the coboundary system's ranks 10 and 11 on the face monoid are replaced here by the certificate cycle,
which proves the same refusal. The replicator statements are pointwise derivative identities along a given
solution, not an existence theorem for the flow, and the HodgeRank reading of pairwise comparisons is the record's.
The seam's sign: in the carry's convention `δb(x, y) = b(x) + b(y) − b(xy)` the seam is `δ(−count)`; a class and
its negative are one refusal.

The computational object is the helical pair interaction: a face is read where two operands meet at a contact, the
carry is what the contact owes the winding when the phase is lifted, and the seam is what a join owes the count.
Of the winding guide's six general objects this touches the helix (the carry as the winding's defect), the pair
(the seam at a join of two words), faces and placement (the face monoid, the Künneth summands) and cell holonomy
(a class read on a lap or a certificate cycle); the tube and the tower thread stay attached.

Consumers: the atlas rows `face.carry-bockstein`, `lang.seam-class`, `contact.kunneth-interaction-rank`,
`norm.replicator-hodge-parts`, and the #410 box "Faces read on cycles".

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.FacesOnCycles

open Finset

/-! ## 1. The carry is the Bockstein of the phase -/

section Carry

variable {n : ℕ} [NeZero n]

/-- [definition] The carry of the digit lift on `ℤ/n`: `⌊(a + b)/n⌋` on the representatives `0 … n − 1`. -/
def carry (a b : ZMod n) : ℤ := (((a.val + b.val) / n : ℕ) : ℤ)

/-- [definition] The integer coboundary of a function on `ℤ/n`: `δb(a, b) = b(a) + b(b) − b(a + b)`. -/
def delta (f : ZMod n → ℤ) (a b : ZMod n) : ℤ := f a + f b - f (a + b)

/-- [definition] The digit, the integer lift of a residue to `0 … n − 1`. -/
def digit (a : ZMod n) : ℤ := (a.val : ℤ)

/-- [proved-standard; formal-checked] The carry is the repository's `Geometry/PhaseCarry.carry` on the digits. -/
theorem carry_eq_phaseCarry (a b : ZMod n) :
    carry a b = (Holonics.Geometry.PhaseCarry.carry n a.val b.val : ℤ) := by
  unfold carry Holonics.Geometry.PhaseCarry.carry
  rw [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)]

/-- [proved-standard; formal-checked] The lift fails by the carry: `(a + b) + n·carry a b = a + b` on the digits. -/
theorem val_add_add_carry (a b : ZMod n) :
    (((a + b).val : ℕ) : ℤ) + n * carry a b = a.val + b.val := by
  unfold carry
  rw [ZMod.val_add]
  exact_mod_cast Nat.mod_add_div (a.val + b.val) n

/-- [proved-standard; formal-checked] `n·carry` is the coboundary of the digit itself. -/
theorem n_mul_carry (a b : ZMod n) : (n : ℤ) * carry a b = delta digit a b := by
  unfold delta digit
  linear_combination val_add_add_carry a b

/-- [proved-standard; formal-checked] The carry is a 2-cocycle:
`carry(a, b) + carry(a + b, c) = carry(b, c) + carry(a, b + c)`. -/
theorem carry_cocycle (a b c : ZMod n) :
    carry a b + carry (a + b) c = carry b c + carry a (b + c) := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h1 := val_add_add_carry a b
  have h2 := val_add_add_carry (a + b) c
  have h3 := val_add_add_carry b c
  have h4 := val_add_add_carry a (b + c)
  rw [add_assoc a b c] at h2
  apply mul_left_cancel₀ hn
  linear_combination (h1 + h2) - (h3 + h4)

/-- [proved-standard; formal-checked] **Every integer coboundary reads `n·b(1)` on the lap** `a → a + 1`. -/
theorem sum_delta_lap (f : ZMod n → ℤ) : ∑ a : ZMod n, delta f a 1 = n * f 1 := by
  unfold delta
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hshift : ∑ a : ZMod n, f (a + 1) = ∑ a : ZMod n, f a :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [hshift, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

/-- [proved-standard; formal-checked] **The lap carries once**: `Σ_a carry(a, 1) = 1`. -/
theorem sum_carry_lap [Fact (1 < n)] : ∑ a : ZMod n, carry a 1 = 1 := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  apply mul_left_cancel₀ hn
  rw [Finset.mul_sum]
  simp_rw [n_mul_carry]
  rw [sum_delta_lap]
  simp [digit, ZMod.val_one]

/-- [proved-standard; formal-checked] **The class has order `n`**: `k·carry` is an integer coboundary exactly when
`n ∣ k`. -/
theorem smul_carry_coboundary_iff [Fact (1 < n)] (k : ℤ) :
    (∃ f : ZMod n → ℤ, ∀ a b, k * carry a b = delta f a b) ↔ (n : ℤ) ∣ k := by
  constructor
  · rintro ⟨f, hf⟩
    have h := sum_delta_lap f
    simp_rw [← hf] at h
    rw [← Finset.mul_sum, sum_carry_lap, mul_one] at h
    exact ⟨f 1, h⟩
  · rintro ⟨m, rfl⟩
    refine ⟨fun a => m * digit a, fun a b => ?_⟩
    have h := n_mul_carry a b
    unfold delta digit at *
    linear_combination m * h

/-- [proved-standard; formal-checked] No integer re-reading of the digit removes the carry. -/
theorem carry_not_coboundary [Fact (1 < n)] : ¬ ∃ f : ZMod n → ℤ, ∀ a b, carry a b = delta f a b := by
  rintro ⟨f, hf⟩
  have h : (n : ℤ) ∣ 1 := (smul_carry_coboundary_iff 1).1 ⟨f, fun a b => by rw [one_mul]; exact hf a b⟩
  have h1 : n ∣ 1 := by exact_mod_cast h
  have := (Fact.out : 1 < n)
  have := Nat.le_of_dvd one_pos h1
  omega

/-- [proved-standard; formal-checked] Nor any multiple `k·carry` with `0 < k < n`. -/
theorem smul_carry_not_coboundary [Fact (1 < n)] {k : ℤ} (hk0 : 0 < k) (hkn : k < n) :
    ¬ ∃ f : ZMod n → ℤ, ∀ a b, k * carry a b = delta f a b := by
  rintro h
  have hd := (smul_carry_coboundary_iff k).1 h
  have := Int.le_of_dvd hk0 hd
  omega

/-- [proved-standard; formal-checked] **A real chart erases the carry**: over `ℚ` it is the coboundary of the
phase `a ↦ a/n`. -/
theorem carry_eq_phase_coboundary (a b : ZMod n) :
    (carry a b : ℚ) = (a.val : ℚ) / n + (b.val : ℚ) / n - ((a + b).val : ℚ) / n := by
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h : (((a + b).val : ℕ) : ℚ) + n * carry a b = a.val + b.val := by
    exact_mod_cast val_add_add_carry a b
  field_simp
  linear_combination h

end Carry

/-! ## 2. The `th` seam is a rational class of the face monoid -/

section Seam

/-- [definition] The letters `t`, `h` and `a`. -/
inductive Letter
  | t
  | h
  | a
  deriving DecidableEq

/-- [definition] A face of a word: `none` for the empty word `ε`, else its first and last letter. -/
abbrev Face := Option (Letter × Letter)

/-- [definition] The face monoid's product `(f, l)(f′, l′) = (f, l′)`, with unit `ε`. -/
def faceMul : Face → Face → Face
  | none, y => y
  | x, none => x
  | some (f, _), some (_, l) => some (f, l)

/-- [proved-standard; formal-checked] `ε` is a unit on both sides. -/
theorem faceMul_none_left (x : Face) : faceMul none x = x := by cases x <;> rfl

/-- [proved-standard; formal-checked] `ε` is a unit on both sides. -/
theorem faceMul_none_right (x : Face) : faceMul x none = x := by
  rcases x with _ | ⟨f, l⟩ <;> rfl

/-- [proved-standard; formal-checked] The face monoid's product is associative. -/
theorem faceMul_assoc (x y z : Face) : faceMul (faceMul x y) z = faceMul x (faceMul y z) := by
  rcases x with _ | ⟨f, l⟩ <;> rcases y with _ | ⟨f', l'⟩ <;> rcases z with _ | ⟨f'', l''⟩ <;> rfl

/-- [definition] The last letter of `x :: r`. -/
def lastFrom : Letter → List Letter → Letter
  | x, [] => x
  | _, y :: r => lastFrom y r

/-- [definition] The face of a word. -/
def face : List Letter → Face
  | [] => none
  | x :: r => some (x, lastFrom x r)

/-- [definition] The count of `th` in a word. -/
def thCount : List Letter → ℤ
  | [] => 0
  | x :: r => (if x = Letter.t ∧ r.head? = some Letter.h then 1 else 0) + thCount r

/-- [definition] The seam `s(x, y) = [x ends t][y starts h]`, a function of the two faces. -/
def seam : Face → Face → ℤ
  | some (_, Letter.t), some (Letter.h, _) => 1
  | _, _ => 0

/-- [proved-standard; formal-checked] The last letter of a join is the second word's last letter. -/
theorem lastFrom_append_cons (c : Letter) (r : List Letter) (e : Letter) (y : List Letter) :
    lastFrom c (r ++ e :: y) = lastFrom e y := by
  induction r generalizing c with
  | nil => rfl
  | cons d r ih => exact ih d

/-- [proved-standard; formal-checked] The face of a join is the product of the faces. -/
theorem face_append (x y : List Letter) : face (x ++ y) = faceMul (face x) (face y) := by
  cases x with
  | nil => exact (faceMul_none_left _).symm
  | cons c r =>
    cases y with
    | nil => simp [face, faceMul]
    | cons e y => simp [face, faceMul, lastFrom_append_cons]

/-- [proved-standard; formal-checked] The seam after a face ending `l`: `[l = t][the word starts h]`. -/
theorem seam_face_left (f l : Letter) (y : List Letter) :
    seam (some (f, l)) (face y) = if l = Letter.t ∧ y.head? = some Letter.h then 1 else 0 := by
  cases y with
  | nil => cases l <;> rfl
  | cons e y => cases l <;> cases e <;> rfl

/-- [proved-standard; formal-checked] The seam reads only the first face's last letter. -/
theorem seam_first_irrel (f f' : Letter) {l : Letter} (z : Face) :
    seam (some (f, l)) z = seam (some (f', l)) z := by
  rcases z with _ | ⟨g, m⟩ <;> cases l <;> (try cases g) <;> rfl

/-- [proved-standard; formal-checked] **The count of `th` across a join**:
`count(x ++ y) = count x + count y + s(face x, face y)`. -/
theorem thCount_append (x y : List Letter) :
    thCount (x ++ y) = thCount x + thCount y + seam (face x) (face y) := by
  induction x with
  | nil => simp [thCount, face, seam]
  | cons c r ih =>
    cases r with
    | nil =>
      have e1 : thCount ([c] ++ y)
          = (if c = Letter.t ∧ y.head? = some Letter.h then 1 else 0) + thCount y := rfl
      have e2 : thCount [c] = 0 := by simp [thCount]
      have e3 : face [c] = some (c, c) := rfl
      rw [e1, e2, e3, seam_face_left]
      ring
    | cons d r' =>
      have l1 : thCount (c :: d :: r' ++ y)
          = (if c = Letter.t ∧ some d = some Letter.h then 1 else 0) + thCount (d :: r' ++ y) := rfl
      have l2 : thCount (c :: d :: r')
          = (if c = Letter.t ∧ some d = some Letter.h then 1 else 0) + thCount (d :: r') := rfl
      have f1 : face (c :: d :: r') = some (c, lastFrom d r') := rfl
      have f2 : face (d :: r') = some (d, lastFrom d r') := rfl
      rw [l1, l2, ih, f1, f2, seam_first_irrel c d]
      ring

/-- [proved-standard; formal-checked] **Upstairs the seam is a coboundary of the count**:
`s(face x, face y) = count(x ++ y) − count x − count y`. -/
theorem seam_eq_count_coboundary (x y : List Letter) :
    seam (face x) (face y) = thCount (x ++ y) - thCount x - thCount y := by
  rw [thCount_append]; ring

/-- [proved-standard; formal-checked] Every face is the face of a word. -/
theorem exists_word (x : Face) : ∃ w, face w = x := by
  rcases x with _ | ⟨f, l⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[f, l], rfl⟩

/-- [proved-standard; formal-checked] **The seam is a 2-cocycle of the face monoid**, read from the words:
`s(x, y) + s(xy, z) = s(y, z) + s(x, yz)`. -/
theorem seam_cocycle (x y z : Face) :
    seam x y + seam (faceMul x y) z = seam y z + seam x (faceMul y z) := by
  obtain ⟨u, rfl⟩ := exists_word x
  obtain ⟨v, rfl⟩ := exists_word y
  obtain ⟨w, rfl⟩ := exists_word z
  have h1 := thCount_append (u ++ v) w
  have h2 := thCount_append u (v ++ w)
  rw [thCount_append u v, face_append] at h1
  rw [thCount_append v w, face_append] at h2
  rw [List.append_assoc] at h1
  linarith

/-- [definition] A rational coboundary on the face monoid: `δb(x, y) = b(x) + b(y) − b(xy)`. -/
def faceDelta (b : Face → ℚ) (x y : Face) : ℚ := b x + b y - b (faceMul x y)

/-- [definition] The certificate 2-cycle `[at|ha] + [aa|aa] − [at|at] − [ha|ha]`, read on a 2-cochain. -/
def cert (φ : Face → Face → ℚ) : ℚ :=
  φ (some (Letter.a, Letter.t)) (some (Letter.h, Letter.a))
    + φ (some (Letter.a, Letter.a)) (some (Letter.a, Letter.a))
    - φ (some (Letter.a, Letter.t)) (some (Letter.a, Letter.t))
    - φ (some (Letter.h, Letter.a)) (some (Letter.h, Letter.a))

/-- [proved-standard; formal-checked] Every rational coboundary reads `0` on the certificate. -/
theorem cert_coboundary (b : Face → ℚ) : cert (faceDelta b) = 0 := by
  simp only [cert, faceDelta, faceMul]
  ring

/-- [proved-standard; formal-checked] The seam reads `1` on the certificate. -/
theorem cert_seam : cert (fun x y => (seam x y : ℚ)) = 1 := by
  simp [cert, seam]

/-- [proved-standard; formal-checked] **The seam is no rational coboundary** of the face monoid: it is a class. -/
theorem seam_not_coboundary : ¬ ∃ b : Face → ℚ, ∀ x y, (seam x y : ℚ) = faceDelta b x y := by
  rintro ⟨b, hb⟩
  have h : (fun x y => (seam x y : ℚ)) = faceDelta b := funext fun x => funext fun y => hb x y
  have := cert_seam
  rw [h, cert_coboundary] at this
  exact zero_ne_one this

end Seam

/-! ## 3. The four-cycle reads the Künneth cross part, and the interaction rank counts rank-one contacts -/

section Kunneth

variable {X Y : Type*} [Fintype X] [Fintype Y]

set_option linter.unusedSectionVars false

/-- [definition] The unit four-cycle of a table: `□G = G(x, y) − G(x′, y) − G(x, y′) + G(x′, y′)`. -/
def square (G : X → Y → ℚ) (x x' : X) (y y' : Y) : ℚ := G x y - G x' y - G x y' + G x' y'

/-- [definition] A row's mean. -/
def rowMean (G : X → Y → ℚ) (x : X) : ℚ := (∑ y, G x y) / Fintype.card Y

/-- [definition] A column's mean. -/
def colMean (G : X → Y → ℚ) (y : Y) : ℚ := (∑ x, G x y) / Fintype.card X

/-- [definition] The table's mean. -/
def mean (G : X → Y → ℚ) : ℚ := (∑ x, ∑ y, G x y) / (Fintype.card X * Fintype.card Y)

/-- [definition] The Künneth cross part `V_X ⊗ V_Y` of a table: what is left after the constant, the row part and the
column part (the analysis of variance's interaction). -/
def cross (G : X → Y → ℚ) (x : X) (y : Y) : ℚ := G x y - rowMean G x - colMean G y + mean G

/-- [proved-standard; formal-checked] **The four-cycle annihilates the first three summands**: the cross part has the
table's four-cycles. -/
theorem square_cross (G : X → Y → ℚ) (x x' : X) (y y' : Y) :
    square (cross G) x x' y y' = square G x x' y y' := by
  simp only [square, cross]
  ring

/-- [proved-standard; formal-checked] Every four-cycle vanishes exactly when the table is a sum `u(x) + v(y)`. -/
theorem square_zero_iff_separable [Nonempty X] [Nonempty Y] (G : X → Y → ℚ) :
    (∀ x x' y y', square G x x' y y' = 0) ↔ ∃ u : X → ℚ, ∃ v : Y → ℚ, ∀ x y, G x y = u x + v y := by
  constructor
  · intro h
    obtain ⟨x₀⟩ := ‹Nonempty X›
    obtain ⟨y₀⟩ := ‹Nonempty Y›
    refine ⟨fun x => G x y₀, fun y => G x₀ y - G x₀ y₀, fun x y => ?_⟩
    have := h x x₀ y y₀
    simp only [square] at this
    linarith
  · rintro ⟨u, v, huv⟩ x x' y y'
    simp only [square, huv]
    ring

/-- [proved-standard; formal-checked] **The cross part vanishes exactly when the table is a sum `u(x) + v(y)`**, so
(with `square_zero_iff_separable`) every four-cycle vanishes iff the Künneth cross part vanishes. -/
theorem cross_zero_iff_separable [Nonempty X] [Nonempty Y] (G : X → Y → ℚ) :
    (∀ x y, cross G x y = 0) ↔ ∃ u : X → ℚ, ∃ v : Y → ℚ, ∀ x y, G x y = u x + v y := by
  constructor
  · intro h
    refine ⟨fun x => rowMean G x, fun y => colMean G y - mean G, fun x y => ?_⟩
    have := h x y
    simp only [cross] at this
    linarith
  · rintro ⟨u, v, huv⟩ x y
    have hX : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hY : (Fintype.card Y : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hr : rowMean G x = u x + (∑ y, v y) / Fintype.card Y := by
      simp only [rowMean, huv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hc : colMean G y = (∑ x, u x) / Fintype.card X + v y := by
      simp only [colMean, huv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hm : mean G = (∑ x, u x) / Fintype.card X + (∑ y, v y) / Fintype.card Y := by
      simp only [mean, huv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum]
      field_simp
    simp only [cross, hr, hc, hm, huv]
    ring

open Matrix in
/-- [proved-standard; formal-checked] A sum of `r` rank-one bilinear terms `Σ_k a_k(x) b_k(y)` has rank at most `r`. -/
theorem rank_le_of_sum_rankOne {r : ℕ} (M : Matrix X Y ℚ) (a : Fin r → X → ℚ) (b : Fin r → Y → ℚ)
    (h : ∀ x y, M x y = ∑ k, a k x * b k y) : M.rank ≤ r := by
  have hM : M = (Matrix.of fun x k => a k x) * (Matrix.of fun k y => b k y) := by
    ext x y
    simp [Matrix.mul_apply, h]
  rw [hM]
  calc _ ≤ (Matrix.of fun x k => a k x).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin r) := Matrix.rank_le_card_width _
    _ = r := Fintype.card_fin r

open Matrix in
/-- [proved-standard; formal-checked] **A table of rank `r` is a sum of `r` rank-one bilinear terms**, read on a basis
of its column space; with `rank_le_of_sum_rankOne`, the interaction rank is the least number of rank-one contacts
that read a face from its operands' classes. -/
theorem exists_sum_rankOne [DecidableEq Y] (M : Matrix X Y ℚ) :
    ∃ (a : Fin M.rank → X → ℚ) (b : Fin M.rank → Y → ℚ), ∀ x y, M x y = ∑ k, a k x * b k y := by
  classical
  let W := LinearMap.range M.mulVecLin
  have hW : Module.finrank ℚ W = M.rank := rfl
  let e := (Module.finBasis ℚ W).reindex (finCongr hW)
  let col : Y → W := fun y => ⟨M *ᵥ Pi.single y 1, ⟨Pi.single y 1, rfl⟩⟩
  refine ⟨fun k x => (e k : X → ℚ) x, fun k y => e.repr (col y) k, fun x y => ?_⟩
  have hx := congrArg (fun w : W => (w : X → ℚ) x) (e.sum_repr (col y))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
  have hc : (col y : X → ℚ) x = M x y := by
    simp [col, Matrix.mulVec, dotProduct, Pi.single_apply]
  show M x y = ∑ k, (e k : X → ℚ) x * e.repr (col y) k
  rw [← hc, ← hx]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end Kunneth

/-! ## 4. Selection splits by Hodge parts -/

section Replicator

variable {ι : Type*} [Fintype ι]

open Matrix

/-- [definition] The replicator's vector field `ẋ_i = x_i((Ax)_i − xᵀAx)`. -/
noncomputable def replicator (A : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  x i * ((A *ᵥ x) i - x ⬝ᵥ (A *ᵥ x))

/-- [proved-standard; formal-checked] The replicator keeps the simplex: on `Σ x_i = 1` its rates sum to zero. -/
theorem sum_replicator (A : Matrix ι ι ℝ) (x : ι → ℝ) (hx : ∑ i, x i = 1) :
    ∑ i, replicator A x i = 0 := by
  simp only [replicator, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx, one_mul]
  exact sub_self _

/-- [proved-standard; formal-checked] An antisymmetric payoff reads `xᵀKx = 0`. -/
theorem dot_mulVec_antisymm (K : Matrix ι ι ℝ) (hK : Kᵀ = -K) (x : ι → ℝ) : x ⬝ᵥ (K *ᵥ x) = 0 := by
  have h : x ⬝ᵥ (Kᵀ *ᵥ x) = x ⬝ᵥ (K *ᵥ x) := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
  rw [hK, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

/-- [proved-standard; formal-checked] **The harmonic part cycles on a conserved face**: under an antisymmetric
payoff with zero column sums (rock-paper-scissors), `Σ log x_i` is constant along every positive solution of the
replicator. -/
theorem replicator_log_conserved {K : Matrix ι ι ℝ} (hK : Kᵀ = -K) (hcol : ∀ j, ∑ i, K i j = 0)
    {x : ℝ → ι → ℝ} {t : ℝ} (hpos : ∀ i, 0 < x t i)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (replicator K (x t) i) t) :
    HasDerivAt (fun s => ∑ i, Real.log (x s i)) 0 t := by
  refine (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hx i).log (hpos i).ne')).congr_deriv ?_
  have hq : ∀ i, replicator K (x t) i / x t i = (K *ᵥ x t) i := by
    intro i
    simp only [replicator, dot_mulVec_antisymm K hK, sub_zero]
    exact mul_div_cancel_left₀ _ (hpos i).ne'
  simp_rw [hq]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, hcol]

/-- [proved-standard; formal-checked] Fisher's identity on the simplex: `Σ_i (Sx)_i ẋ_i = Σ_i x_i((Sx)_i − xᵀSx)²`,
the fitness variance. -/
theorem fisher_identity (S : Matrix ι ι ℝ) (x : ι → ℝ) (hx : ∑ i, x i = 1) :
    ∑ i, (S *ᵥ x) i * replicator S x i = ∑ i, x i * ((S *ᵥ x) i - x ⬝ᵥ (S *ᵥ x)) ^ 2 := by
  set m := x ⬝ᵥ (S *ᵥ x) with hm
  have key : ∑ i, x i * ((S *ᵥ x) i - m) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx, one_mul]
    rw [hm]
    exact sub_self _
  calc ∑ i, (S *ᵥ x) i * replicator S x i
      = ∑ i, (x i * ((S *ᵥ x) i - m) ^ 2 + m * (x i * ((S *ᵥ x) i - m))) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [replicator, ← hm]
        ring
    _ = ∑ i, x i * ((S *ᵥ x) i - m) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, key, mul_zero, add_zero]

/-- [proved-standard; formal-checked] **The exact part is a gradient**: under a symmetric payoff on the simplex the
mean fitness `xᵀSx` rises at twice the fitness variance, `d/dt xᵀSx = 2 Σ_i x_i((Sx)_i − xᵀSx)²` (Fisher). -/
theorem replicator_mean_rate {S : Matrix ι ι ℝ} (hS : Sᵀ = S) {x : ℝ → ι → ℝ} {t : ℝ}
    (hsum : ∑ i, x t i = 1) (hx : ∀ i, HasDerivAt (fun s => x s i) (replicator S (x t) i) t) :
    HasDerivAt (fun s => x s ⬝ᵥ (S *ᵥ x s))
      (2 * ∑ i, x t i * ((S *ᵥ x t) i - x t ⬝ᵥ (S *ᵥ x t)) ^ 2) t := by
  have hSx : ∀ i, HasDerivAt (fun s => (S *ᵥ x s) i)
      ((S *ᵥ fun j => replicator S (x t) j) i) t := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum (fun j _ => (hx j).const_mul (S i j))
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hx i).fun_mul (hSx i))
  refine h.congr_deriv ?_
  have hsym : ∑ i, x t i * (S *ᵥ fun j => replicator S (x t) j) i
      = ∑ i, (S *ᵥ x t) i * replicator S (x t) i := by
    change x t ⬝ᵥ (S *ᵥ fun j => replicator S (x t) j) = (S *ᵥ x t) ⬝ᵥ fun j => replicator S (x t) j
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, dotProduct_comm]
  rw [Finset.sum_add_distrib, hsym, ← fisher_identity S (x t) hsum]
  have hcomm : ∑ i, replicator S (x t) i * (S *ᵥ x t) i = ∑ i, (S *ᵥ x t) i * replicator S (x t) i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hcomm]
  ring

end Replicator

end Holonics.Compression.FacesOnCycles
