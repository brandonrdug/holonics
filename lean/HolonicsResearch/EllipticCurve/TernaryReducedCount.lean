import HolonicsResearch.EllipticCurve.FamilyTunnellThetaCarrier

/-!
# The ternary counts of the Tunnell carrier, read one coordinate at a time

`FamilyThetaWaldspurgerBridge` and `FamilyTunnellThetaCarrier` define the four populations of the Tunnell carrier as
filters of the whole cube `[-B, B]³`, `B = ⌊√n⌋`: the thin form `2x² + y² + 8z²`, the thick form `2x² + y² + 32z²`
and their two level-four corrections `4x² + 2y² + 8z²`, `4x² + 2y² + 32z²`. A count read off that cube visits
`(2B + 1)³` triples, sixteen million at `n = 5⁶`, and the proofs that read the carrier's coefficients at
`n = 15625` and its neighbours closed by `native_decide`, which trusts the compiler (`Lean.ofReduceBool`).

This file reads the same counts with the last coordinate solved: for each `(x, y)` the `z` with `c z² = m` are
counted by the square root of `m / c` (`squareFibreCount`: none, one at `m = 0`, or the pair `±s`). The count is
then a double sum over the box, which the kernel evaluates; the theorems below equate each population's card with
its double sum, so the values are read by the kernel on the very objects the carrier's theorems are about.

[proved-derived; formal-checked] What is proved.

1. **A square's fibre in a box** (`card_filter_sq`): for `c > 0`, the number of `z ∈ [-B, B]` with `c z² = m` is
   `squareFibreCount c B m`.
2. **A triple filter is a double sum of fibres** (`card_filter_triple`, `card_diagonal`): a filter of `X × Y × Z` has
   card `Σ_x Σ_y #(Z filtered at (x, y))`, and for a predicate that solves `c z² = F x y` the inner count is the fibre.
3. **A tight box per coordinate** (`card_filter_triple_xz`, `lt_of_not_mem_tight`, `card_tight`): for the forms
   `a x² + y² + c z²` with the middle coordinate solved, the outer sums need only `|x| ≤ ⌊√(n/a)⌋` and
   `|z| ≤ ⌊√(n/c)⌋` (`tightCount`); outside those boxes `a x²` or `c z²` already exceeds `n` and the fibre is empty.
4. **The four populations** (`thinThetaCoefficient_eq_tight`, `thickThetaCoefficient_eq_tight`,
   `levelThinCoefficient_eq_reduced`, `levelThickCoefficient_eq_reduced`, `fullTunnellThetaCoefficient_eq_reduced`,
   `fullTunnellThetaCoefficient_eq_reducedOdd`): each coefficient of the carrier is its double sum, at every `n`; the
   thin and thick populations by their tight boxes, the level corrections over the whole square `[-B, B]²`.
5. **The carrier's coefficients at the squares the lift and the Hecke defects read** (`fullTunnell_at_*`), closed by
   `decide +kernel`: `2, 0, 2, 0, −6, 0, 2, 0` at `1, 4, …, 64`, `−6` at `81`, `2` at `625`, `−6` at `729` and `26` at
   `15625`, the last two on the odd branch, where the level corrections vanish.

Limits. The reduction is of counting, not of the forms: the theorems are about the populations as defined, with
their box `⌊√n⌋`. Nothing here is a theorem about the Shimura lift or the Hecke operators; those files consume the
values. The level corrections still visit the whole square `[-B, B]²` and are read only at small `n`; at
`n = 15625` the odd branch reads the thin and thick counts alone, over `177 · 89` and `177 · 45` pairs.

The computational object is the helical pair interaction: a population is the fibre of a quadratic face over a
lattice of addresses, and solving one coordinate is reading that face's last place by its root. Of the winding
guide's six general objects this touches faces and placement (the quadratic face and its fibre); the helix, the pair,
cell holonomy, the tube and the tower thread stay attached.

Consumers: `FamilyTunnellShimuraLift.shimuraHeckeDifference_zero_through_sturm_aperture` and
`FamilyTunnellHeckeIntertwining.tunnellHalfIntegralHeckeDefect_{three,five}_first_orbit`, which this file moves off
`native_decide`; atlas `bsd.shimura-lift-coefficients`, `bsd.shimura-local-recurrence`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.EllipticCurve.TernaryReducedCount

open Finset
open Holonics.EllipticCurve.LatticeCount
open Holonics.EllipticCurve.FamilyThetaWaldspurgerBridge
open Holonics.EllipticCurve.FamilyTunnellThetaCarrier

/-! ## 1. A square's fibre in a box -/

/-- [definition] The number of `z ∈ [-B, B]` with `c z² = m`: none when `m < 0`, the one `z = 0` when `m = 0`, and
the pair `±s` when `m = c s²` with `0 < s ≤ B`. The square root is the kernel-reducible `Nat.sqrt`. -/
def squareFibreCount (c B : ℕ) (m : ℤ) : ℕ :=
  if m < 0 then 0 else if m = 0 then 1 else
    if m.toNat % c = 0 ∧ Nat.sqrt (m.toNat / c) * Nat.sqrt (m.toNat / c) = m.toNat / c ∧
      Nat.sqrt (m.toNat / c) ≤ B then 2 else 0

/-- [proved-derived; formal-checked] **A square's fibre in a box.** -/
theorem card_filter_sq (c B : ℕ) (hc : 0 < c) (m : ℤ) :
    ((boxZ B).filter (fun z => (c : ℤ) * z ^ 2 = m)).card = squareFibreCount c B m := by
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  unfold squareFibreCount
  rw [theReducibleBoxIsTheInterval]
  split_ifs with hneg hzero hsq
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z _ h
    nlinarith [sq_nonneg z]
  · subst hzero
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext z
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      have : z ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h (ne_of_gt hc')
        · exact h
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    · rintro rfl
      refine ⟨⟨by omega, by omega⟩, by ring⟩
  · obtain ⟨hmod, hss, hle⟩ := hsq
    have hm0 : 0 ≤ m := le_of_not_gt hneg
    set q := m.toNat / c with hq
    set s := Nat.sqrt q with hs
    have hmnat : m.toNat = c * q := by
      have := Nat.div_add_mod m.toNat c
      rw [hmod, add_zero] at this
      exact this.symm
    have hm : m = (c : ℤ) * (s : ℤ) ^ 2 := by
      have h1 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
      rw [← h1, hmnat, ← hss]
      push_cast
      ring
    have hspos : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · exfalso; apply hzero; rw [hm, h]; simp
      · exact h
    have hset : (Finset.Icc (-(B : ℤ)) (B : ℤ)).filter (fun z => (c : ℤ) * z ^ 2 = m) =
        {(s : ℤ), -(s : ℤ)} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        rw [hm] at h
        have h2 : z ^ 2 = (s : ℤ) ^ 2 := mul_left_cancel₀ (ne_of_gt hc') h
        exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
      · have hsB : (s : ℤ) ≤ B := by exact_mod_cast hle
        rintro (rfl | rfl)
        · exact ⟨⟨by omega, hsB⟩, hm.symm⟩
        · exact ⟨⟨by omega, by omega⟩, by rw [hm]; ring⟩
    rw [hset, Finset.card_pair]
    have : (0 : ℤ) < s := by exact_mod_cast hspos
    omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z hz h
    apply hsq
    have hm0 : 0 ≤ m := le_of_not_gt hneg
    rw [Finset.mem_Icc] at hz
    have hmnat : m.toNat = c * (z.natAbs * z.natAbs) := by
      have : (m.toNat : ℤ) = ((c * (z.natAbs * z.natAbs) : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hm0, ← h]
        push_cast
        rw [← sq, sq_abs]
      exact_mod_cast this
    have hdiv : m.toNat / c = z.natAbs * z.natAbs := by
      rw [hmnat, Nat.mul_div_cancel_left _ hc]
    refine ⟨by rw [hmnat]; simp, ?_, ?_⟩
    · rw [hdiv, Nat.sqrt_eq]
    · rw [hdiv, Nat.sqrt_eq]
      omega

/-! ## 2. A triple filter is a double sum of fibres -/

/-- [proved-derived; formal-checked] The card of a filter of a triple product is the double sum of its fibres in the
last coordinate. -/
theorem card_filter_triple (X Y Z : Finset ℤ) (P : ℤ × ℤ × ℤ → Prop) [DecidablePred P] :
    ((X ×ˢ Y ×ˢ Z).filter P).card =
      ∑ x ∈ X, ∑ y ∈ Y, (Z.filter (fun z => P (x, y, z))).card := by
  simp only [Finset.card_filter, Finset.sum_product]

/-- [proved-derived; formal-checked] For a predicate that solves `c z² = F x y` in the last coordinate, the card over
the cube `[-B, B]³` is the double sum of square fibres. -/
theorem card_diagonal (B c : ℕ) (hc : 0 < c) (F : ℤ → ℤ → ℤ) (P : ℤ × ℤ × ℤ → Prop)
    [DecidablePred P] (hP : ∀ t, P t ↔ (c : ℤ) * t.2.2 ^ 2 = F t.1 t.2.1) :
    (((boxZ B) ×ˢ (boxZ B) ×ˢ (boxZ B)).filter P).card =
      ∑ x ∈ boxZ B, ∑ y ∈ boxZ B, squareFibreCount c B (F x y) := by
  rw [card_filter_triple]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← card_filter_sq c B hc]
  congr 1
  exact Finset.filter_congr fun z _ => hP (x, y, z)

/-- [proved-derived; formal-checked] The same card with the middle coordinate solved: the double sum runs over the
first and the last coordinate. -/
theorem card_filter_triple_xz (X Y Z : Finset ℤ) (P : ℤ × ℤ × ℤ → Prop) [DecidablePred P] :
    ((X ×ˢ Y ×ˢ Z).filter P).card =
      ∑ x ∈ X, ∑ z ∈ Z, (Y.filter (fun y => P (x, y, z))).card := by
  rw [card_filter_triple]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- [proved-derived; formal-checked] A negative target has an empty fibre. -/
theorem squareFibreCount_of_neg (c B : ℕ) {m : ℤ} (hm : m < 0) : squareFibreCount c B m = 0 := by
  simp [squareFibreCount, hm]

/-- [proved-derived; formal-checked] Boxes nest. -/
theorem boxZ_mono {B B' : ℕ} (h : B' ≤ B) : boxZ B' ⊆ boxZ B := by
  intro x hx
  rw [theReducibleBoxIsTheInterval, Finset.mem_Icc] at hx ⊢
  constructor <;> omega

/-- [proved-derived; formal-checked] Outside the box `⌊√(n/a)⌋` the term `a x²` already exceeds `n`. -/
theorem lt_of_not_mem_tight {a n : ℕ} (ha : 0 < a) {x : ℤ} (hx : x ∉ boxZ (Nat.sqrt (n / a))) :
    (n : ℤ) < a * x ^ 2 := by
  rw [theReducibleBoxIsTheInterval, Finset.mem_Icc] at hx
  have hs : Nat.sqrt (n / a) + 1 ≤ x.natAbs := by omega
  have h1 : n / a < (Nat.sqrt (n / a) + 1) * (Nat.sqrt (n / a) + 1) := Nat.lt_succ_sqrt (n / a)
  have h2 : (Nat.sqrt (n / a) + 1) * (Nat.sqrt (n / a) + 1) ≤ x.natAbs * x.natAbs :=
    Nat.mul_le_mul hs hs
  have h3 : n < a * (n / a + 1) := Nat.lt_mul_div_succ n ha
  have h4 : n < a * (x.natAbs * x.natAbs) := by
    calc n < a * (n / a + 1) := h3
      _ ≤ a * (x.natAbs * x.natAbs) := Nat.mul_le_mul_left a (by omega)
  have h5 : ((a * (x.natAbs * x.natAbs) : ℕ) : ℤ) = a * x ^ 2 := by
    push_cast
    rw [← sq, sq_abs]
  rw [← h5]
  exact_mod_cast h4

/-- [definition] The double sum of a form `a x² + y² + c z² = n` with the middle coordinate solved and the outer two
on their own tight boxes `⌊√(n/a)⌋`, `⌊√(n/c)⌋`. -/
def tightCount (a c n : ℕ) : ℕ :=
  ∑ x ∈ boxZ (Nat.sqrt (n / a)), ∑ z ∈ boxZ (Nat.sqrt (n / c)),
    squareFibreCount 1 (Nat.sqrt n) ((n : ℤ) - a * x ^ 2 - c * z ^ 2)

/-- [proved-derived; formal-checked] **The tight reading.** A population of `a x² + y² + c z² = n` on the cube
`⌊√n⌋` has the card of its tight double sum. -/
theorem card_tight (a c n : ℕ) (ha : 0 < a) (hc : 0 < c) (P : ℤ × ℤ × ℤ → Prop) [DecidablePred P]
    (hP : ∀ t, P t ↔ (a : ℤ) * t.1 ^ 2 + t.2.1 ^ 2 + c * t.2.2 ^ 2 = n) :
    (((boxZ (Nat.sqrt n)) ×ˢ (boxZ (Nat.sqrt n)) ×ˢ (boxZ (Nat.sqrt n))).filter P).card =
      tightCount a c n := by
  rw [card_filter_triple_xz]
  have hinner : ∀ x z : ℤ, ((boxZ (Nat.sqrt n)).filter (fun y => P (x, y, z))).card =
      squareFibreCount 1 (Nat.sqrt n) ((n : ℤ) - a * x ^ 2 - c * z ^ 2) := by
    intro x z
    rw [← card_filter_sq 1 (Nat.sqrt n) (by norm_num)]
    congr 1
    refine Finset.filter_congr fun y _ => ?_
    rw [hP]
    constructor <;> intro h <;> push_cast at h ⊢ <;> linarith
  simp_rw [hinner]
  unfold tightCount
  calc ∑ x ∈ boxZ (Nat.sqrt n), ∑ z ∈ boxZ (Nat.sqrt n),
        squareFibreCount 1 (Nat.sqrt n) ((n : ℤ) - a * x ^ 2 - c * z ^ 2)
      = ∑ x ∈ boxZ (Nat.sqrt n), ∑ z ∈ boxZ (Nat.sqrt (n / c)),
          squareFibreCount 1 (Nat.sqrt n) ((n : ℤ) - a * x ^ 2 - c * z ^ 2) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        symm
        apply Finset.sum_subset (boxZ_mono (Nat.sqrt_le_sqrt (Nat.div_le_self n c)))
        intro z _ hz
        apply squareFibreCount_of_neg
        have := lt_of_not_mem_tight hc hz
        nlinarith [sq_nonneg x]
    _ = ∑ x ∈ boxZ (Nat.sqrt (n / a)), ∑ z ∈ boxZ (Nat.sqrt (n / c)),
          squareFibreCount 1 (Nat.sqrt n) ((n : ℤ) - a * x ^ 2 - c * z ^ 2) := by
        symm
        apply Finset.sum_subset (boxZ_mono (Nat.sqrt_le_sqrt (Nat.div_le_self n a)))
        intro x _ hx
        refine Finset.sum_eq_zero fun z _ => squareFibreCount_of_neg _ _ ?_
        have := lt_of_not_mem_tight ha hx
        nlinarith [sq_nonneg z]

/-! ## 3. The four populations as double sums -/

/-- [definition] The double sum of a diagonal ternary form `a x² + b y² + c z² = n` over the carrier's box
`⌊√n⌋`. -/
def reducedCount (a b c n : ℕ) : ℕ :=
  ∑ x ∈ boxZ (Nat.sqrt n), ∑ y ∈ boxZ (Nat.sqrt n),
    squareFibreCount c (Nat.sqrt n) ((n : ℤ) - a * x ^ 2 - b * y ^ 2)

/-- [proved-derived; formal-checked] The thin coefficient is its tight double sum. -/
theorem thinThetaCoefficient_eq_tight (n : ℕ) :
    thinThetaCoefficient n = tightCount 2 8 n := by
  unfold thinThetaCoefficient canonicalThinPopulation SolFr
  rw [card_tight 2 8 n (by norm_num) (by norm_num)]
  intro t; push_cast; rfl

/-- [proved-derived; formal-checked] The thick coefficient is its tight double sum. -/
theorem thickThetaCoefficient_eq_tight (n : ℕ) :
    thickThetaCoefficient n = tightCount 2 32 n := by
  unfold thickThetaCoefficient canonicalThickPopulation
  rw [card_tight 2 32 n (by norm_num) (by norm_num)]
  intro t; push_cast; rfl

/-- [proved-derived; formal-checked] The level-four thin correction is its double sum. -/
theorem levelThinCoefficient_eq_reduced (n : ℕ) :
    levelThinCoefficient n = reducedCount 4 2 8 n := by
  unfold levelThinCoefficient levelThinPopulation levelThinQuadraticForm reducedCount
  rw [card_diagonal (Nat.sqrt n) 8 (by norm_num) (fun x y => (n : ℤ) - 4 * x ^ 2 - 2 * y ^ 2)]
  · norm_num
  · intro t; constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

/-- [proved-derived; formal-checked] The level-four thick correction is its double sum. -/
theorem levelThickCoefficient_eq_reduced (n : ℕ) :
    levelThickCoefficient n = reducedCount 4 2 32 n := by
  unfold levelThickCoefficient levelThickPopulation levelThickQuadraticForm reducedCount
  rw [card_diagonal (Nat.sqrt n) 32 (by norm_num) (fun x y => (n : ℤ) - 4 * x ^ 2 - 2 * y ^ 2)]
  · norm_num
  · intro t; constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

/-- [definition] The complete level-128 coefficient read through the four double sums. -/
def reducedFullTunnell (n : ℕ) : ℤ :=
  2 * (tightCount 2 32 n : ℤ) - tightCount 2 8 n -
    2 * (reducedCount 4 2 32 n : ℤ) + reducedCount 4 2 8 n

/-- [definition] The odd-branch coefficient `2 · thick − thin` read through its two double sums. -/
def reducedOddTunnell (n : ℕ) : ℤ :=
  2 * (tightCount 2 32 n : ℤ) - tightCount 2 8 n

/-- [proved-derived; formal-checked] The complete coefficient of the carrier is its reduced reading at every `n`. -/
theorem fullTunnellThetaCoefficient_eq_reduced (n : ℕ) :
    fullTunnellThetaCoefficient n = reducedFullTunnell n := by
  rw [fullTunnellThetaCoefficient, tunnellThetaCoefficient, thinThetaCoefficient_eq_tight,
    thickThetaCoefficient_eq_tight, levelThinCoefficient_eq_reduced,
    levelThickCoefficient_eq_reduced, reducedFullTunnell]

/-- [proved-derived; formal-checked] On the odd branch the coefficient is the reduced `2 · thick − thin`. -/
theorem fullTunnellThetaCoefficient_eq_reducedOdd {n : ℕ} (hn : Odd n) :
    fullTunnellThetaCoefficient n = reducedOddTunnell n := by
  rw [fullTunnellThetaCoefficient_eq_tunnellThetaCoefficient_of_odd hn, tunnellThetaCoefficient,
    thinThetaCoefficient_eq_tight, thickThetaCoefficient_eq_tight, reducedOddTunnell]

/-! ## 4. The coefficients the lift and the Hecke defects read, in the kernel -/

/-- [proved-derived; formal-checked] The carrier's coefficients at the squares `1, 4, …, 64`, the inputs of the
Shimura lift's first eight coefficients. -/
theorem fullTunnell_at_small_squares :
    fullTunnellThetaCoefficient 1 = 2 ∧ fullTunnellThetaCoefficient 4 = 0 ∧
      fullTunnellThetaCoefficient 9 = 2 ∧ fullTunnellThetaCoefficient 16 = 0 ∧
      fullTunnellThetaCoefficient 25 = -6 ∧ fullTunnellThetaCoefficient 36 = 0 ∧
      fullTunnellThetaCoefficient 49 = 2 ∧ fullTunnellThetaCoefficient 64 = 0 := by
  simp only [fullTunnellThetaCoefficient_eq_reduced]
  decide +kernel

/-- [proved-derived; formal-checked] At `81 = 3⁴`. -/
theorem fullTunnell_at_81 : fullTunnellThetaCoefficient 81 = -6 := by
  rw [fullTunnellThetaCoefficient_eq_reducedOdd (by decide)]
  decide +kernel

/-- [proved-derived; formal-checked] At `625 = 5⁴`. -/
theorem fullTunnell_at_625 : fullTunnellThetaCoefficient 625 = 2 := by
  rw [fullTunnellThetaCoefficient_eq_reducedOdd (by decide)]
  decide +kernel

/-- [proved-derived; formal-checked] At `729 = 3⁶`. -/
theorem fullTunnell_at_729 : fullTunnellThetaCoefficient 729 = -6 := by
  rw [fullTunnellThetaCoefficient_eq_reducedOdd (by decide)]
  decide +kernel

/-- [proved-derived; formal-checked] The thin count at `15625 = 5⁶`: 250 triples, read on `177 · 89` pairs where the
cube holds `251³`, sixteen million. -/
theorem thin_at_15625 : tightCount 2 8 15625 = 250 := by
  decide +kernel

/-- [proved-derived; formal-checked] The thick count at `15625`: 138 triples, on `177 · 45` pairs. -/
theorem thick_at_15625 : tightCount 2 32 15625 = 138 := by
  decide +kernel

/-- [proved-derived; formal-checked] At `15625 = 5⁶`: `2 · 138 − 250 = 26`. -/
theorem fullTunnell_at_15625 : fullTunnellThetaCoefficient 15625 = 26 := by
  rw [fullTunnellThetaCoefficient_eq_reducedOdd (by decide), reducedOddTunnell, thin_at_15625,
    thick_at_15625]
  norm_num

end Holonics.EllipticCurve.TernaryReducedCount
