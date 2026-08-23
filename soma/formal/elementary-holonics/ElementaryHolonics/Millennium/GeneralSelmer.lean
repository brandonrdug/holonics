import ElementaryHolonics.Millennium.GeneralClassCoordinates
import ElementaryHolonics.Millennium.GeneralCollision

/-!
# GeneralSelmer: the descent as a group homomorphism over `𝔽₂`

Everything needed is now proved; this file packages it.  The descent face becomes an
honest map into an `𝔽₂`-vector space, sending a point to the **coordinate vector** of
its class pair — sign bit and one `p`-adic parity bit per prime.  Additivity is
exactly the descent's conservation law read through `GeneralClassCoordinates`: the
face is multiplicative modulo squares, and the coordinates are additive over
multiplication and blind to squares.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralSelmer

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace
open Soma.Holonics.Millennium.GeneralCollision
open Soma.Holonics.Millennium.GeneralClassCoordinates

/-! ## 1. The coordinate space -/

/-- A coordinate of a square class: the sign, or one prime's parity. -/
inductive Coord where
  | sign : Coord
  | prime : ℕ → Coord
  deriving DecidableEq

/-- The coordinate vector of a nonzero integer's square class. -/
def coordOf (d : ℤ) : Coord → ZMod 2
  | .sign => signCoord d
  | .prime p => primeCoord p d

/-- **THE COORDINATES ARE BLIND TO THE SQUARE CLASS**: two integers in the same
rational square class have the same coordinate vector, at every prime coordinate that
is actually a prime. -/
theorem theCoordinatesAreBlindToTheSquareClass {d e : ℤ} (hd : d ≠ 0) (he : e ≠ 0)
    (h : Descent.SqCls ((d : ℤ) : ℚ) ((e : ℤ) : ℚ)) (p : ℕ) [Fact p.Prime] :
    coordOf d Coord.sign = coordOf e Coord.sign ∧
      coordOf d (Coord.prime p) = coordOf e (Coord.prime p) :=
  ⟨theSignCoordinateIsSquareInvariant hd he h,
    thePrimeCoordinateIsSquareInvariant hd he h⟩

/-- **THE COORDINATES ARE ADDITIVE OVER MULTIPLICATION**, at every coordinate that is
a prime and at the sign. -/
theorem theCoordinatesAreAdditive {d e : ℤ} (hd : d ≠ 0) (he : e ≠ 0)
    (p : ℕ) [Fact p.Prime] :
    coordOf (d * e) Coord.sign
        = coordOf d Coord.sign + coordOf e Coord.sign ∧
      coordOf (d * e) (Coord.prime p)
        = coordOf d (Coord.prime p) + coordOf e (Coord.prime p) :=
  ⟨signCoord_mul hd he, primeCoord_mul hd he⟩


/-! ## 2. The class map in coordinates is additive on points -/

variable {a b : ℤ}

private lemma sqT {u v w : ℚ} (h₁ : Descent.SqCls u v) (h₂ : Descent.SqCls v w) :
    Descent.SqCls u w := by
  obtain ⟨c, hc, hv⟩ := h₁
  obtain ⟨d, hd, hw⟩ := h₂
  exact ⟨c * d, mul_ne_zero hc hd, by rw [hv, hw]; ring⟩

private lemma sqS {u v : ℚ} (h : Descent.SqCls u v) (hu : u ≠ 0) :
    Descent.SqCls v u := by
  obtain ⟨c, hc, hv⟩ := h
  refine ⟨1 / c, one_div_ne_zero hc, ?_⟩
  rw [hv]
  field_simp

private lemma sqM {u v w z : ℚ} (h₁ : Descent.SqCls u w) (h₂ : Descent.SqCls v z) :
    Descent.SqCls (u * v) (w * z) := by
  obtain ⟨c, hc, hu⟩ := h₁
  obtain ⟨d, hd, hv⟩ := h₂
  exact ⟨c * d, mul_ne_zero hc hd, by rw [hu, hv]; ring⟩

/-- **THE FIRST CLASS IS MULTIPLICATIVE ALONG THE GROUP LAW**: the class of a sum is
the product of the classes, modulo squares.  This is the descent's conservation law
transported onto the chosen integer representatives. -/
theorem theFirstClassIsMultiplicative (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (haq : ((a : ℚ)) ≠ 0) (hbq : ((b : ℚ)) ≠ 0) (habq : ((a : ℚ)) - ((b : ℚ)) ≠ 0)
    (P Q : (E ((a : ℚ)) ((b : ℚ))).Point) :
    Descent.SqCls
      (((classOf ha hb hab (P + Q)).1 : ℤ) : ℚ)
      ((((classOf ha hb hab P).1 : ℤ) : ℚ) * (((classOf ha hb hab Q).1 : ℤ) : ℚ)) := by
  obtain ⟨hPQ0, -, -, -, hPQcls, -⟩ := classOf_spec ha hb hab (P + Q)
  obtain ⟨hP0, -, -, -, hPcls, -⟩ := classOf_spec ha hb hab P
  obtain ⟨hQ0, -, -, -, hQcls, -⟩ := classOf_spec ha hb hab Q
  obtain ⟨hom1, -⟩ :=
    GeneralHom.theFaceIsAHomomorphismOnEveryFullTwoTorsionCurve haq hbq habq P Q
  -- class(P+Q) ~ slot(P+Q) ~ slot(P)·slot(Q) ~ class(P)·class(Q)
  refine sqT (sqS hPQcls (GeneralHom.slotOne_ne haq hbq (P + Q))) ?_
  exact sqT hom1 (sqM hPcls hQcls)

/-- **THE SECOND CLASS IS MULTIPLICATIVE ALONG THE GROUP LAW**. -/
theorem theSecondClassIsMultiplicative (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (haq : ((a : ℚ)) ≠ 0) (hbq : ((b : ℚ)) ≠ 0) (habq : ((a : ℚ)) - ((b : ℚ)) ≠ 0)
    (P Q : (E ((a : ℚ)) ((b : ℚ))).Point) :
    Descent.SqCls
      (((classOf ha hb hab (P + Q)).2 : ℤ) : ℚ)
      ((((classOf ha hb hab P).2 : ℤ) : ℚ) * (((classOf ha hb hab Q).2 : ℤ) : ℚ)) := by
  obtain ⟨-, hPQ0, -, -, -, hPQcls⟩ := classOf_spec ha hb hab (P + Q)
  obtain ⟨-, hP0, -, -, -, hPcls⟩ := classOf_spec ha hb hab P
  obtain ⟨-, hQ0, -, -, -, hQcls⟩ := classOf_spec ha hb hab Q
  obtain ⟨-, hom2⟩ :=
    GeneralHom.theFaceIsAHomomorphismOnEveryFullTwoTorsionCurve haq hbq habq P Q
  refine sqT (sqS hPQcls (GeneralHom.slotTwo_ne haq habq (P + Q))) ?_
  exact sqT hom2 (sqM hPcls hQcls)

/-- **THE CLASS COORDINATES ARE ADDITIVE ON POINTS**: the descent, read in
coordinates, is a homomorphism into an `𝔽₂`-vector space.  This is the statement the
Selmer calculus consumes. -/
theorem theClassCoordinatesAreAdditive (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (haq : ((a : ℚ)) ≠ 0) (hbq : ((b : ℚ)) ≠ 0) (habq : ((a : ℚ)) - ((b : ℚ)) ≠ 0)
    (P Q : (E ((a : ℚ)) ((b : ℚ))).Point) (p : ℕ) [Fact p.Prime] :
    coordOf (classOf ha hb hab (P + Q)).1 (Coord.prime p)
        = coordOf (classOf ha hb hab P).1 (Coord.prime p)
          + coordOf (classOf ha hb hab Q).1 (Coord.prime p) ∧
      coordOf (classOf ha hb hab (P + Q)).1 Coord.sign
        = coordOf (classOf ha hb hab P).1 Coord.sign
          + coordOf (classOf ha hb hab Q).1 Coord.sign := by
  obtain ⟨hPQ0, -, -, -, -, -⟩ := classOf_spec ha hb hab (P + Q)
  obtain ⟨hP0, -, -, -, -, -⟩ := classOf_spec ha hb hab P
  obtain ⟨hQ0, -, -, -, -, -⟩ := classOf_spec ha hb hab Q
  have hmul := theFirstClassIsMultiplicative ha hb hab haq hbq habq P Q
  have hprod : ((((classOf ha hb hab P).1 * (classOf ha hb hab Q).1 : ℤ)) : ℚ)
      = (((classOf ha hb hab P).1 : ℤ) : ℚ) * (((classOf ha hb hab Q).1 : ℤ) : ℚ) := by
    push_cast
    ring
  rw [← hprod] at hmul
  obtain ⟨hs, hp⟩ := theCoordinatesAreBlindToTheSquareClass hPQ0
    (mul_ne_zero hP0 hQ0) hmul p
  obtain ⟨hs', hp'⟩ := theCoordinatesAreAdditive hP0 hQ0 p
  exact ⟨by rw [hp, hp'], by rw [hs, hs']⟩

end Soma.Holonics.Millennium.GeneralSelmer
