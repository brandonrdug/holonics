import ElementaryHolonics.Millennium.GeneralSelmer
import ElementaryHolonics.Millennium.GeneralMordell
import ElementaryHolonics.Millennium.Separation

/-!
# PrimeAxes: the primes are the axes, and the rank is a dimension

A prime is a **free generator**: `ℚ⁺` is the free abelian group on the primes, so
modulo squares `ℚ*/(ℚ*)²` is a free `𝔽₂`-vector space whose basis is the primes
together with one sign axis.  `GeneralClassCoordinates` supplies those coordinates and
`GeneralSelmer` proves the descent face additive in them.  This file closes the
picture:

* **`theFaceIsSupportedOnThePrimeAxes`** — only the primes of bad reduction are
  occupied, so the face lands in a finite-dimensional subspace;
* **`theCoordinateVectorDeterminesTheSquareClass`** — the coordinates *separate*
  classes, so the primes are a **complete** set of axes and not merely a spanning
  family.  This is the injectivity that blindness alone does not give;
* **`theClassesCollideByDimension`** — the pigeonhole against `2^(2(ω+1))` rather
  than against `4τ²`;
* **`theQuotientIsBoundedByThePrimeAxisDimension`** — weak Mordell–Weil as a
  dimension count;
* **`theRankIsBoundedByTheOccupiedPrimeAxes`** — the rank bound itself.

Since `τ(K) ≥ 2^ω(K)` always, with equality exactly for squarefree `K`, every bound
here is at least as sharp as the divisor-count bound it replaces, and strictly sharper
whenever the discriminant carries a repeated prime.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.PrimeAxes

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace
open Soma.Holonics.Millennium.GeneralCollision
open Soma.Holonics.Millennium.GeneralClassCoordinates
open Soma.Holonics.Millennium.GeneralSelmer
open DirectSum

variable {a b : ℤ}

/-- The prime axes the curve's descent can occupy: the primes of bad reduction. -/
def axes (a b : ℤ) : Finset ℕ := (a * b * (a - b)).natAbs.primeFactors

/-- **THE FACE IS SUPPORTED ON THE PRIME AXES**: off the primes of bad reduction
every coordinate of both descent slots vanishes. -/
theorem theFaceIsSupportedOnThePrimeAxes (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (P : (E ((a : ℚ)) ((b : ℚ))).Point) (l : ℕ) [Fact l.Prime] (hl : l ∉ axes a b) :
    coordOf (classOf ha hb hab P).1 (Coord.prime l) = 0 ∧
      coordOf (classOf ha hb hab P).2 (Coord.prime l) = 0 := by
  have hl' : l.Prime := Fact.out
  have hK0 : (a * b * (a - b)).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact mul_ne_zero (mul_ne_zero ha hb) hab
  have hnd : ¬ l ∣ (a * b * (a - b)).natAbs := by
    intro hdvd
    exact hl (Nat.mem_primeFactors.mpr ⟨hl', hdvd, hK0⟩)
  obtain ⟨h10, h20, hd1, hd2, -, -⟩ := classOf_spec ha hb hab P
  have hn1 : ¬ l ∣ (classOf ha hb hab P).1.natAbs := fun h => hnd (h.trans hd1)
  have hn2 : ¬ l ∣ (classOf ha hb hab P).2.natAbs := fun h => hnd (h.trans hd2)
  constructor
  · show primeCoord l (classOf ha hb hab P).1 = 0
    unfold primeCoord padicValInt
    rw [padicValNat.eq_zero_of_not_dvd hn1]
    rfl
  · show primeCoord l (classOf ha hb hab P).2 = 0
    unfold primeCoord padicValInt
    rw [padicValNat.eq_zero_of_not_dvd hn2]
    rfl



/-- **THE COORDINATE VECTOR DETERMINES THE SQUARE CLASS**: blindness says the
coordinate map is well defined; this says it is injective.  The primes are a
**complete** set of axes for `ℚ*/(ℚ*)²`, not merely a spanning family. -/
theorem theCoordinateVectorDeterminesTheSquareClass {d e : ℤ} (hd : d ≠ 0) (he : e ≠ 0)
    (hs : coordOf d Coord.sign = coordOf e Coord.sign)
    (hp : ∀ p : ℕ, p.Prime → coordOf d (Coord.prime p) = coordOf e (Coord.prime p)) :
    Descent.SqCls ((d : ℤ) : ℚ) ((e : ℤ) : ℚ) := by
  -- 1. same sign bit and both nonzero force a positive product
  have hpos : 0 < d * e := by
    have hs' : signCoord d = signCoord e := hs
    unfold signCoord at hs'
    rcases lt_or_gt_of_ne hd with hdn | hdp
    · rw [if_pos hdn] at hs'
      have hen : e < 0 := by
        by_contra hc
        rw [if_neg hc] at hs'
        exact absurd hs' (by decide)
      exact mul_pos_of_neg_of_neg hdn hen
    · rw [if_neg (not_lt.mpr hdp.le)] at hs'
      have hep : 0 < e := by
        rcases lt_or_gt_of_ne he with hc | hc
        · rw [if_pos hc] at hs'; exact absurd hs'.symm (by decide)
        · exact hc
      exact mul_pos hdp hep
  have hde0 : d * e ≠ 0 := hpos.ne'
  -- 2. same prime parity bits make every exponent of the product even
  have hnabs : (d * e).natAbs = d.natAbs * e.natAbs := Int.natAbs_mul d e
  have hd0 : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
  have he0 : e.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr he
  have heven : ∀ l : ℕ, l.Prime → Even (padicValNat l (d * e).natAbs) := by
    intro l hl
    haveI : Fact l.Prime := ⟨hl⟩
    have hcoord : ((padicValInt l d : ℕ) : ZMod 2) = ((padicValInt l e : ℕ) : ZMod 2) :=
      hp l hl
    have hpar : padicValInt l d % 2 = padicValInt l e % 2 := by
      have := (ZMod.natCast_eq_natCast_iff' (padicValInt l d) (padicValInt l e) 2).mp hcoord
      simpa using this
    rw [hnabs, padicValNat.mul hd0 he0]
    show Even (padicValInt l d + padicValInt l e)
    rw [Nat.even_add, Nat.even_iff, Nat.even_iff]
    omega
  -- 3. the squarefree part is trivial, so the product is a perfect square
  obtain ⟨sfA, sfB, hab, hsq⟩ := Nat.sq_mul_squarefree (d * e).natAbs
  have hn0 : (d * e).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hde0
  have ha0 : sfA ≠ 0 := by
    intro hc; rw [hc, mul_zero] at hab; exact hn0 hab.symm
  have hb0 : sfB ≠ 0 := by
    intro hc; rw [hc] at hab; simp at hab; exact hn0 hab.symm
  have hA1 : sfA = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro l hl hdvd
    have hle1 : sfA.factorization l ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one ha0).mp hsq l
    have hpos1 : 0 < sfA.factorization l := Nat.Prime.factorization_pos_of_dvd hl ha0 hdvd
    have hev := heven l hl
    rw [← hab, ← Nat.factorization_def _ hl] at hev
    rw [Nat.factorization_mul (pow_ne_zero 2 hb0) ha0, Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hev
    obtain ⟨k, hk⟩ := hev
    omega
  have hsquare : (d * e).natAbs = sfB ^ 2 := by rw [← hab, hA1, mul_one]
  have hZ : d * e = (sfB : ℤ) ^ 2 := by
    have h1 : ((d * e).natAbs : ℤ) = d * e := Int.natAbs_of_nonneg hpos.le
    rw [hsquare] at h1
    push_cast at h1
    linarith
  -- 4. the class witness
  refine ⟨(sfB : ℚ) / (e : ℚ), ?_, ?_⟩
  · have heQ : ((e : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr he
    have hbQ : ((sfB : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
    exact div_ne_zero hbQ (by exact_mod_cast heQ)
  · have heQ : ((e : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr he
    have hZQ : ((d : ℤ) : ℚ) * ((e : ℤ) : ℚ) = ((sfB : ℕ) : ℚ) ^ 2 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hZ
    field_simp
    linear_combination hZQ




private lemma sqTr {u v w : ℚ} (h₁ : Descent.SqCls u v) (h₂ : Descent.SqCls v w) :
    Descent.SqCls u w := by
  obtain ⟨c, hc, hv⟩ := h₁
  obtain ⟨d, hd, hw⟩ := h₂
  exact ⟨c * d, mul_ne_zero hc hd, by rw [hv, hw]; ring⟩

private lemma sqSy {u v : ℚ} (h : Descent.SqCls u v) (hu : u ≠ 0) :
    Descent.SqCls v u := by
  obtain ⟨c, hc, hv⟩ := h
  refine ⟨1 / c, one_div_ne_zero hc, ?_⟩
  rw [hv]
  field_simp

/-- The coordinate vector of a point's descent face: one bit per slot per axis,
plus one sign bit per slot. -/
def faceVec (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (P : (E ((a : ℚ)) ((b : ℚ))).Point) :
    Bool × Option {l // l ∈ axes a b} → ZMod 2
  | (false, none)   => coordOf (classOf ha hb hab P).1 Coord.sign
  | (false, some l) => coordOf (classOf ha hb hab P).1 (Coord.prime l.1)
  | (true,  none)   => coordOf (classOf ha hb hab P).2 Coord.sign
  | (true,  some l) => coordOf (classOf ha hb hab P).2 (Coord.prime l.1)

/-- **THE CLASSES COLLIDE BY DIMENSION**: the pigeonhole runs against the dimension
of the coordinate space, not against a divisor count.  Since `τ(K) ≥ 2^ω(K)` with
equality only for squarefree `K`, this is at least as sharp as the divisor bound and
strictly sharper whenever `K` carries a repeated prime. -/
theorem theClassesCollideByDimension (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    {α : Type} [Fintype α]
    (hcard : 2 ^ (2 * ((axes a b).card + 1)) < Fintype.card α)
    (f : α → (E ((a : ℚ)) ((b : ℚ))).Point) :
    ∃ p q, p ≠ q ∧ ∃ Q : (E ((a : ℚ)) ((b : ℚ))).Point, f p - f q = Q + Q := by
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast ha
  have hbq : ((b : ℚ)) ≠ 0 := by exact_mod_cast hb
  have habq : ((a : ℚ)) - ((b : ℚ)) ≠ 0 := by
    intro hc
    refine hab ?_
    have h1 : ((a : ℚ)) = ((b : ℚ)) := by linarith
    have hz : (a : ℤ) = b := by exact_mod_cast h1
    omega
  -- (A) the coordinate space has dimension 2*(|axes|+1)
  have hdim : Fintype.card (Bool × Option {l // l ∈ axes a b} → ZMod 2)
      = 2 ^ (2 * ((axes a b).card + 1)) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_option, Fintype.card_coe]
  have hlt : Fintype.card (Bool × Option {l // l ∈ axes a b} → ZMod 2)
      < Fintype.card α := by rw [hdim]; exact hcard
  obtain ⟨p, q, hpq, hvec⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p : α => faceVec ha hb hab (f p)) hlt
  refine ⟨p, q, hpq, ?_⟩
  -- (B) equal vectors force equal square classes at every coordinate
  have hcoord : ∀ (l : ℕ), l.Prime →
      coordOf (classOf ha hb hab (f p)).1 (Coord.prime l)
        = coordOf (classOf ha hb hab (f q)).1 (Coord.prime l) ∧
      coordOf (classOf ha hb hab (f p)).2 (Coord.prime l)
        = coordOf (classOf ha hb hab (f q)).2 (Coord.prime l) := by
    intro l hl
    haveI : Fact l.Prime := ⟨hl⟩
    by_cases hmem : l ∈ axes a b
    · have h1 := congrFun hvec (false, some ⟨l, hmem⟩)
      have h2 := congrFun hvec (true, some ⟨l, hmem⟩)
      simp only [faceVec] at h1 h2
      exact ⟨h1, h2⟩
    · obtain ⟨z1, z2⟩ := theFaceIsSupportedOnThePrimeAxes ha hb hab (f p) l hmem
      obtain ⟨w1, w2⟩ := theFaceIsSupportedOnThePrimeAxes ha hb hab (f q) l hmem
      exact ⟨by rw [z1, w1], by rw [z2, w2]⟩
  have hs1 : coordOf (classOf ha hb hab (f p)).1 Coord.sign
      = coordOf (classOf ha hb hab (f q)).1 Coord.sign := by
    have h := congrFun hvec (false, none); simpa only [faceVec] using h
  have hs2 : coordOf (classOf ha hb hab (f p)).2 Coord.sign
      = coordOf (classOf ha hb hab (f q)).2 Coord.sign := by
    have h := congrFun hvec (true, none); simpa only [faceVec] using h
  obtain ⟨hp10, hp20, -, -, hps1, hps2⟩ := classOf_spec ha hb hab (f p)
  obtain ⟨hq10, hq20, -, -, hqs1, hqs2⟩ := classOf_spec ha hb hab (f q)
  have hc1 := theCoordinateVectorDeterminesTheSquareClass hp10 hq10 hs1
    (fun l hl => (hcoord l hl).1)
  have hc2 := theCoordinateVectorDeterminesTheSquareClass hp20 hq20 hs2
    (fun l hl => (hcoord l hl).2)
  -- chain slot ~ class ~ class ~ slot
  have hslot1 : Descent.SqCls (slotOne ((a : ℚ)) ((b : ℚ)) (f p))
      (slotOne ((a : ℚ)) ((b : ℚ)) (f q)) :=
    sqTr (sqTr hps1 hc1) (sqSy hqs1 (GeneralHom.slotOne_ne haq hbq (f q)))
  have hslot2 : Descent.SqCls (slotTwo ((a : ℚ)) ((b : ℚ)) (f p))
      (slotTwo ((a : ℚ)) ((b : ℚ)) (f q)) :=
    sqTr (sqTr hps2 hc2) (sqSy hqs2 (GeneralHom.slotTwo_ne haq habq (f q)))
  exact sameClassDouble haq hbq habq (f p) (f q) hslot1 hslot2




/-- **THE QUOTIENT IS BOUNDED BY THE PRIME-AXIS DIMENSION**: one bit per slot per
bad prime plus one sign bit per slot.  The descent read as linear algebra over `𝔽₂`. -/
theorem theQuotientIsBoundedByThePrimeAxisDimension
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) :
    Nat.card ((E ((a : ℚ)) ((b : ℚ))).Point ⧸ twoE ((a : ℚ)) ((b : ℚ)))
      ≤ 2 ^ (2 * ((axes a b).card + 1)) := by
  let G := (E ((a : ℚ)) ((b : ℚ))).Point
  let H : AddSubgroup G := twoE ((a : ℚ)) ((b : ℚ))
  let Q := G ⧸ H
  let N : ℕ := 2 ^ (2 * ((axes a b).card + 1))
  letI : Finite Q := theWeakMordellWeilTheoremOnEveryFullTwoTorsionCurve ha hb hab
  letI : Fintype Q := Fintype.ofFinite Q
  change Nat.card Q ≤ N
  by_contra hle
  have hcard : N < Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]; omega
  obtain ⟨p, q, hpq, W, hW⟩ :=
    theClassesCollideByDimension ha hb hab
      (hcard := by simpa [N, Q, G, H] using hcard)
      (fun c : Q => Quotient.out c)
  apply hpq
  have hmem : Quotient.out p - Quotient.out q ∈ H := by
    change ∃ W, W + W = Quotient.out p - Quotient.out q
    exact ⟨W, hW.symm⟩
  have heq : (Quotient.mk'' (Quotient.out p) : Q) = Quotient.mk'' (Quotient.out q) :=
    (QuotientAddGroup.eq).mpr (by
      rw [neg_add_eq_sub]
      have hneg : Quotient.out q - Quotient.out p
          = -(Quotient.out p - Quotient.out q) := by abel
      rw [hneg]
      exact H.neg_mem hmem)
  calc
    p = Quotient.mk'' (Quotient.out p) := (Quotient.out_eq' p).symm
    _ = Quotient.mk'' (Quotient.out q) := heq
    _ = q := Quotient.out_eq' q





set_option maxHeartbeats 2000000 in
/-- TARGET 3: the rank is bounded by the size of the ambient prime-axis receiver.  This is an
upper bound, not an equality and not a computation of an occupied subspace's dimension. -/
theorem theRankIsBoundedByTheOccupiedPrimeAxes (r : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0)
    (hr : 2 * ((axes a b).card + 1) < r) :
    ¬ Soma.Holonics.Millennium.UniversalBSD.RankAtLeastOn
        (E ((a : ℚ)) ((b : ℚ))) r := by
  intro hR
  unfold Soma.Holonics.Millennium.UniversalBSD.RankAtLeastOn
    Soma.Holonics.Millennium.UniversalBSD.IndependentModTorsionOn
    Soma.Holonics.Millennium.UniversalBSD.IsTorsionOn at hR
  obtain ⟨Pts, hind⟩ := hR
  haveI : AddGroup.FG ((E ((a : ℚ)) ((b : ℚ))).Point) :=
    GeneralMordell.theMordellWeilTheoremOnEveryFullTwoTorsionCurve ha hb hab
  obtain ⟨m, ι, hι, qq, hqq, e, ⟨F⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod ((E ((a : ℚ)) ((b : ℚ))).Point)
  haveI := hι
  haveI : ∀ i, NeZero (qq i ^ e i) := fun i => ⟨pow_ne_zero _ (hqq i).pos.ne'⟩
  haveI : Finite (⨁ i, ZMod (qq i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have htor : ∀ X : (E ((a : ℚ)) ((b : ℚ))).Point, (F X).1 = 0 →
      ∃ k : ℕ, 0 < k ∧ k • X = 0 := by
    intro X hX
    refine ⟨Nat.card (⨁ i, ZMod (qq i ^ e i)), Nat.card_pos, ?_⟩
    apply F.injective
    rw [map_nsmul, map_zero]
    have h2 : (Nat.card (⨁ i, ZMod (qq i ^ e i))) • F X
        = ((Nat.card (⨁ i, ZMod (qq i ^ e i))) • (F X).1,
           (Nat.card (⨁ i, ZMod (qq i ^ e i))) • (F X).2) := rfl
    rw [h2, hX, smul_zero, card_nsmul_eq_zero']
    rfl
  -- the free parts are independent, so the free rank dominates `r`
  set v : Fin r → (Fin m →₀ ℤ) := fun i => (F (Pts i)).1 with hv
  have hindZ : ∀ c : Fin r → ℤ, (∑ i, c i • v i) = 0 → ∀ i, c i = 0 := by
    intro c hczero i
    refine hind c ?_ i
    apply htor
    have hmap : F (∑ i, c i • Pts i) = ∑ i, c i • F (Pts i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul]
    have h1 : (F (∑ i, c i • Pts i)).1 = ∑ i, c i • v i := by
      rw [hmap]
      have h2 := map_sum (AddMonoidHom.fst (Fin m →₀ ℤ) (⨁ i, ZMod (qq i ^ e i)))
        (fun i => c i • F (Pts i)) Finset.univ
      calc (∑ i, c i • F (Pts i)).1
          = ∑ i, (c i • F (Pts i)).1 := h2
        _ = ∑ i, c i • v i :=
            Finset.sum_congr rfl fun j _ => by rw [Prod.smul_fst]
    rw [h1, hczero]
  set castHom : (Fin m →₀ ℤ) →+ (Fin m →₀ ℚ) :=
    Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ) with hcastHom
  have hcastInj : Function.Injective castHom := by
    intro g h hgh
    ext j
    have h1 := DFunLike.congr_fun hgh j
    rw [hcastHom] at h1
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
      Int.coe_castAddHom] at h1
    exact_mod_cast h1
  set w : Fin r → (Fin m →₀ ℚ) := fun i => castHom (v i) with hw
  have hindW : LinearIndependent ℚ w := by
    rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    refine hindZ c ?_ i
    apply hcastInj
    rw [map_sum, map_zero]
    have hterm : ∀ j : Fin r, castHom (c j • v j) = c j • w j := by
      intro j
      rw [map_zsmul, hw]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    exact hc
  have hrm : r ≤ m := by
    have h1 := hindW.fintype_card_le_finrank
    rw [Module.finrank_finsupp_self] at h1
    simpa using h1
  -- the sign-vector free parts
  set wv : (Fin r → Bool) → (Fin m →₀ ℤ) := fun ε =>
    ∑ i : Fin r, if ε i then Finsupp.single (Fin.castLE hrm i) (1 : ℤ) else 0
    with hwv
  have hwv_apply : ∀ (ε : Fin r → Bool) (i : Fin r),
      wv ε (Fin.castLE hrm i) = if ε i then 1 else 0 := by
    intro ε i
    rw [hwv]
    simp only
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single i]
    · by_cases hbb : ε i
      · rw [if_pos hbb, if_pos hbb, Finsupp.single_eq_same]
      · rw [if_neg hbb, if_neg hbb, Finsupp.coe_zero, Pi.zero_apply]
    · intro j _ hji
      by_cases hbb : ε j
      · rw [if_pos hbb]
        exact Finsupp.single_eq_of_ne
          (fun hc => hji (Fin.castLE_injective hrm hc).symm)
      · rw [if_neg hbb, Finsupp.coe_zero, Pi.zero_apply]
    · intro habs
      exact absurd (Finset.mem_univ i) habs
  -- the colliding family of `2^r` points
  obtain ⟨ε, δ, hne, Q, hQ⟩ :=
    theClassesCollideByDimension ha hb hab
      (α := Fin r → Bool)
      (by
        simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        exact Nat.pow_lt_pow_right (by norm_num) hr)
      (fun ε => F.symm (wv ε, 0))
  -- the difference of two sign vectors is even at every coordinate
  have hfree : wv ε - wv δ = (2 : ℤ) • (F Q).1 := by
    have h1 : F (F.symm (wv ε, 0) - F.symm (wv δ, 0)) = F (Q + Q) := by rw [hQ]
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, map_add] at h1
    have h2 := congrArg Prod.fst h1
    simp only [Prod.fst_sub, Prod.fst_add] at h2
    rw [h2]
    module
  -- but it is odd at a coordinate where the signs differ
  obtain ⟨i, hi⟩ : ∃ i : Fin r, ε i ≠ δ i := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  have hodd := congrArg (fun g => g (Fin.castLE hrm i)) hfree
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul] at hodd
  rw [hwv_apply, hwv_apply] at hodd
  rcases Bool.eq_false_or_eq_true (ε i) with hε | hε <;>
    rcases Bool.eq_false_or_eq_true (δ i) with hδ | hδ <;>
      rw [hε, hδ] at hodd hi <;> simp at hodd hi <;> omega

/-! ## The prime axes as a receiver family -/

/-- The **prime-axis receiver family** on the nonzero integers: one reading per prime,
plus the sign reading. -/
def coordReceiver : Separation.ReceiverFamily ℤ (ZMod 2) :=
  {f | f = (fun d => coordOf d Coord.sign) ∨
    ∃ p : ℕ, p.Prime ∧ f = (fun d => coordOf d (Coord.prime p))}

/-- **THE SQUARE CLASS IS EXACTLY THE COLLAPSE OF THE PRIME-AXIS RECEIVER.**  What the
prime readings cannot distinguish is precisely a square class — so the descent's classes
are a collapsed population in the sense of `Separation`, and a separating prime is its
shortest distinguishing word. -/
theorem theSquareClassIsTheCollapseOfThePrimeAxisReceiver {d e : ℤ}
    (hd : d ≠ 0) (he : e ≠ 0) :
    Separation.collapseOf coordReceiver d e ↔ Descent.SqCls ((d : ℤ) : ℚ) ((e : ℤ) : ℚ) := by
  constructor
  · intro hcol
    refine theCoordinateVectorDeterminesTheSquareClass hd he ?_ ?_
    · exact hcol _ (Or.inl rfl)
    · intro p hp
      exact hcol _ (Or.inr ⟨p, hp, rfl⟩)
  · intro hsq f hf
    rcases hf with h | ⟨p, hp, h⟩
    · subst h
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (theCoordinatesAreBlindToTheSquareClass hd he hsq 2).1
    · subst h
      haveI : Fact p.Prime := ⟨hp⟩
      exact (theCoordinatesAreBlindToTheSquareClass hd he hsq p).2

end Soma.Holonics.Millennium.PrimeAxes
