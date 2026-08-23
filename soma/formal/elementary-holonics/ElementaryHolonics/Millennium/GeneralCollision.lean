import ElementaryHolonics.Millennium.GeneralHalving
import ElementaryHolonics.Millennium.FamilyDivisorRank

/-!
# GeneralCollision: the descent bound on every full-2-torsion curve

The three pieces are in place on `y² = x(x−a)(x−b)`: the face is a homomorphism
(`GeneralHom`), its kernel is exactly the doubles (`GeneralHalving`), and its image
is supported on the divisors of `a·b·(a−b)` (`GeneralSupport`).  They compose into the
descent bound.

* **`sameClassDouble`** — two points with the same class differ by a double.
* **`theClassesCollideOnEveryFullTwoTorsionCurve`** — any family of more than
  `(2·τ)²` points contains two whose difference is a double, where `τ` counts the
  signed divisors of `a·b·(a−b)`.

This is the two-descent bound for **every elliptic curve over `ℚ` with full rational
two-torsion** — a two-parameter family of unbounded rank, not a one-parameter slice.
Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralCollision

open WeierstrassCurve.Affine
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace
open Soma.Holonics.Millennium.GeneralHom
open Soma.Holonics.Millennium.GeneralHalving
open Soma.Holonics.Millennium.GeneralSupport

variable {a b : ℤ}

private lemma sqcls_trans' {u v w : ℚ} (h₁ : Descent.SqCls u v) (h₂ : Descent.SqCls v w) :
    Descent.SqCls u w := by
  obtain ⟨c, hc, hv⟩ := h₁
  obtain ⟨d, hd, hw⟩ := h₂
  exact ⟨c * d, mul_ne_zero hc hd, by rw [hv, hw]; ring⟩

private lemma sqcls_mul' {u v w z : ℚ} (h₁ : Descent.SqCls u w) (h₂ : Descent.SqCls v z) :
    Descent.SqCls (u * v) (w * z) := by
  obtain ⟨c, hc, hu⟩ := h₁
  obtain ⟨d, hd, hv⟩ := h₂
  exact ⟨c * d, mul_ne_zero hc hd, by rw [hu, hv]; ring⟩

private lemma sqcls_self_one {u : ℚ} (hu : u ≠ 0) : Descent.SqCls (u * u) 1 :=
  ⟨u, hu, by ring⟩

/-- The slots of a negated point agree with the slots of the point. -/
private lemma slotOne_neg (P : (E ((a : ℚ)) ((b : ℚ))).Point) :
    slotOne ((a : ℚ)) ((b : ℚ)) (-P) = slotOne ((a : ℚ)) ((b : ℚ)) P := by
  rcases P with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, neg_zero]
  · rw [Point.neg_some]
    rfl

private lemma slotTwo_neg (P : (E ((a : ℚ)) ((b : ℚ))).Point) :
    slotTwo ((a : ℚ)) ((b : ℚ)) (-P) = slotTwo ((a : ℚ)) ((b : ℚ)) P := by
  rcases P with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, neg_zero]
  · rw [Point.neg_some]
    rfl

/-- **SAME CLASS MEANS THE DIFFERENCE IS A DOUBLE**: the face is a homomorphism and
its kernel is the doubles, so two points carrying the same pair of classes differ by a
double. -/
theorem sameClassDouble (ha0 : (a : ℚ) ≠ 0) (hb0 : (b : ℚ) ≠ 0)
    (hab0 : (a : ℚ) - (b : ℚ) ≠ 0)
    (X R : (E ((a : ℚ)) ((b : ℚ))).Point)
    (hc₁ : Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) X)
      (slotOne ((a : ℚ)) ((b : ℚ)) R))
    (hc₂ : Descent.SqCls (slotTwo ((a : ℚ)) ((b : ℚ)) X)
      (slotTwo ((a : ℚ)) ((b : ℚ)) R)) :
    ∃ Q : (E ((a : ℚ)) ((b : ℚ))).Point, X - R = Q + Q := by
  obtain ⟨hom1, hom2⟩ :=
    theFaceIsAHomomorphismOnEveryFullTwoTorsionCurve ha0 hb0 hab0 X (-R)
  rw [slotOne_neg, ← sub_eq_add_neg] at hom1
  rw [slotTwo_neg, ← sub_eq_add_neg] at hom2
  have k1 : Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) (X - R)) 1 := by
    refine sqcls_trans' hom1 ?_
    refine sqcls_trans' (sqcls_mul' hc₁ (Descent.sqClsRefl _)) ?_
    exact sqcls_self_one (slotOne_ne ha0 hb0 R)
  have k2 : Descent.SqCls (slotTwo ((a : ℚ)) ((b : ℚ)) (X - R)) 1 := by
    refine sqcls_trans' hom2 ?_
    refine sqcls_trans' (sqcls_mul' hc₂ (Descent.sqClsRefl _)) ?_
    exact sqcls_self_one (slotTwo_ne ha0 hab0 R)
  obtain ⟨Q, hQ⟩ :=
    theKernelIsTheDoublesOnEveryFullTwoTorsionCurve ha0 hb0 hab0 (X - R) k1 k2
  exact ⟨Q, hQ.symm⟩


/-! ## 2. The class map and the pigeonhole -/

/-- The signed divisors of a modulus. -/
def signed (K : ℕ) : Finset ℤ :=
  K.divisors.image (fun k : ℕ => (k : ℤ)) ∪ K.divisors.image (fun k : ℕ => -(k : ℤ))

lemma mem_signed {K : ℕ} (hK : K ≠ 0) {d : ℤ} (hd0 : d ≠ 0) (hdvd : d.natAbs ∣ K) :
    d ∈ signed K := by
  have hmem : d.natAbs ∈ K.divisors := Nat.mem_divisors.mpr ⟨hdvd, hK⟩
  unfold signed
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  rcases Int.natAbs_eq d with h | h
  · exact Or.inl ⟨d.natAbs, hmem, h.symm⟩
  · exact Or.inr ⟨d.natAbs, hmem, h.symm⟩

lemma signed_card_le (K : ℕ) : (signed K).card ≤ 2 * K.divisors.card := by
  unfold signed
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := Finset.card_image_le (s := K.divisors) (f := fun k : ℕ => (k : ℤ))
  have h2 := Finset.card_image_le (s := K.divisors) (f := fun k : ℕ => -(k : ℤ))
  omega


/-- The class of a point: the pair of supported slot classes. -/
def classOf (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab0 : a - b ≠ 0)
    (P : (E ((a : ℚ)) ((b : ℚ))).Point) : ℤ × ℤ :=
  ((theSlotClassesAreSupportedOnEveryFullTwoTorsionCurve ha0 hb0 hab0 P).choose,
   (theSlotClassesAreSupportedOnEveryFullTwoTorsionCurve ha0 hb0 hab0
      P).choose_spec.choose)

lemma classOf_spec (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab0 : a - b ≠ 0)
    (P : (E ((a : ℚ)) ((b : ℚ))).Point) :
    (classOf ha0 hb0 hab0 P).1 ≠ 0 ∧ (classOf ha0 hb0 hab0 P).2 ≠ 0 ∧
    (classOf ha0 hb0 hab0 P).1.natAbs ∣ (a * b * (a - b)).natAbs ∧
    (classOf ha0 hb0 hab0 P).2.natAbs ∣ (a * b * (a - b)).natAbs ∧
    Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) P)
      (((classOf ha0 hb0 hab0 P).1 : ℤ) : ℚ) ∧
    Descent.SqCls (slotTwo ((a : ℚ)) ((b : ℚ)) P)
      (((classOf ha0 hb0 hab0 P).2 : ℤ) : ℚ) :=
  (theSlotClassesAreSupportedOnEveryFullTwoTorsionCurve ha0 hb0 hab0
    P).choose_spec.choose_spec

private lemma sqcls_symm' {u v : ℚ} (h : Descent.SqCls u v) (hu : u ≠ 0) :
    Descent.SqCls v u := by
  obtain ⟨c, hc, hv⟩ := h
  refine ⟨1 / c, one_div_ne_zero hc, ?_⟩
  rw [hv]
  field_simp

/-- **THE CLASSES COLLIDE ON EVERY FULL-TWO-TORSION CURVE**: any family of more than
`(2·τ(|ab(a−b)|))²` points contains two whose difference is a double.  This is the
two-descent bound for **every** elliptic curve over `ℚ` with full rational
two-torsion. -/
theorem theClassesCollideOnEveryFullTwoTorsionCurve
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) {α : Type} [Fintype α]
    (hcard : 4 * (a * b * (a - b)).natAbs.divisors.card
      * (a * b * (a - b)).natAbs.divisors.card < Fintype.card α)
    (f : α → (E ((a : ℚ)) ((b : ℚ))).Point) :
    ∃ p q, p ≠ q ∧ ∃ Q : (E ((a : ℚ)) ((b : ℚ))).Point, f p - f q = Q + Q := by
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast ha
  have hbq : ((b : ℚ)) ≠ 0 := by exact_mod_cast hb
  have habq : ((a : ℚ)) - ((b : ℚ)) ≠ 0 := by
    intro hc
    refine hab ?_
    have : ((a : ℚ)) = ((b : ℚ)) := by linarith
    have hz : (a : ℤ) = b := by exact_mod_cast this
    omega
  set K : ℕ := (a * b * (a - b)).natAbs with hK
  have hK0 : K ≠ 0 := by
    rw [hK, Int.natAbs_ne_zero]
    exact mul_ne_zero (mul_ne_zero ha hb) hab
  set box : Finset (ℤ × ℤ) :=
    signed K ×ˢ signed K with hbox
  have hmaps : ∀ p : α, classOf ha hb hab (f p) ∈ box := by
    intro p
    obtain ⟨h10, h20, h1d, h2d, -, -⟩ := classOf_spec ha hb hab (f p)
    rw [hbox, Finset.mem_product]
    exact ⟨mem_signed hK0 h10 h1d, mem_signed hK0 h20 h2d⟩
  have hboxcard : box.card ≤ 4 * K.divisors.card * K.divisors.card := by
    rw [hbox, Finset.card_product]
    have h := signed_card_le K
    calc (signed K).card * (signed K).card
        ≤ (2 * K.divisors.card) * (2 * K.divisors.card) := Nat.mul_le_mul h h
      _ = 4 * K.divisors.card * K.divisors.card := by ring
  have hlt : box.card < Fintype.card α := by omega
  have hcard2 : Fintype.card (↥box) < Fintype.card α := by
    rw [Fintype.card_coe]
    exact hlt
  obtain ⟨p, q, hpq, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p : α => (⟨classOf ha hb hab (f p), hmaps p⟩ : ↥box)) hcard2
  have hfab : classOf ha hb hab (f p) = classOf ha hb hab (f q) :=
    congrArg Subtype.val hg
  obtain ⟨-, -, -, -, hs1, hs2⟩ := classOf_spec ha hb hab (f p)
  obtain ⟨-, -, -, -, ht1, ht2⟩ := classOf_spec ha hb hab (f q)
  rw [← hfab] at ht1 ht2
  have hq1 : slotOne ((a : ℚ)) ((b : ℚ)) (f q) ≠ 0 := slotOne_ne haq hbq (f q)
  have hq2 : slotTwo ((a : ℚ)) ((b : ℚ)) (f q) ≠ 0 := slotTwo_ne haq habq (f q)
  exact ⟨p, q, hpq,
    sameClassDouble haq hbq habq (f p) (f q)
      (sqcls_trans' hs1 (sqcls_symm' ht1 hq1))
      (sqcls_trans' hs2 (sqcls_symm' ht2 hq2))⟩

end Soma.Holonics.Millennium.GeneralCollision
