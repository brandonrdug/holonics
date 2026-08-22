import ElementaryHolonics.Millennium.FiveDescent
import ElementaryHolonics.Millennium.FiveWitness
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Tactic

/-!
# FiveRank: the algebraic rank at five is exactly one, and the rank clause closes

**The endgame of the descent.**  The Mordell–Weil group is finitely generated
(`FiveDescent`), so the structure theorem presents it as `ℤⁿ × T` with `T` finite.
The face image is eight classes, so no nine points can pairwise avoid differing by a
double; but were `n ≥ 2`, the two free directions crossed with the three torsion
directions `{0, (0,0), (5,0)}` — pairwise non-congruent modulo doubles by their slot
classes — would supply nine.  So `n ≤ 1`:

* **`theAlgebraicRankAtFiveIsBelowTwo`** — `¬ AlgebraicRankAtLeast 5 r` for `r ≥ 2`;
* **`theAlgebraicRankIsOneAtFive`** — `AlgebraicRankIs 5 1`, both sides;
* **`theRankClauseHoldsWholeAtFive`** — `TheRankClause 5 theWitnessAtFive`:
  the complete rank clause of the posed Birch–Swinnerton-Dyer conjecture at the
  rank-one instance, every ingredient in this tree.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FiveRank

open WeierstrassCurve.Affine
open DirectSum
open Soma.Holonics.Millennium

/-! ## 1. Local plumbing -/

private lemma slotOne5_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotOne (.some h) = if x = 0 then -25 else x := rfl

private lemma slotTwo5_some {x y : ℚ} (h : RankOne.E5.Nonsingular x y) :
    RankOne.slotTwo (.some h) = if x = 5 then 50 else x - 5 := rfl

private lemma slotOne5_ne (P : RankOne.E5.Point) : RankOne.slotOne P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotOne5_some]
    split_ifs with hx
    · norm_num
    · exact hx

private lemma slotTwo5_ne (P : RankOne.E5.Point) : RankOne.slotTwo P ≠ 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact one_ne_zero
  · rw [slotTwo5_some]
    split_ifs with hx
    · norm_num
    · exact sub_ne_zero.mpr hx

private lemma slotOne_neg (P : RankOne.E5.Point) :
    RankOne.slotOne (-P) = RankOne.slotOne P := by
  rcases P with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, neg_zero]
  · rw [Point.neg_some]
    rfl

private lemma slotTwo_neg (P : RankOne.E5.Point) :
    RankOne.slotTwo (-P) = RankOne.slotTwo P := by
  rcases P with _ | @⟨x, y, h⟩
  · rw [← Point.zero_def, neg_zero]
  · rw [Point.neg_some]
    rfl

private lemma sqcls_trans {a b c : ℚ} (h₁ : Descent.SqCls a b) (h₂ : Descent.SqCls b c) :
    Descent.SqCls a c := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma sqcls_symm {a b : ℚ} (h : Descent.SqCls a b) : Descent.SqCls b a := by
  obtain ⟨c, hc, hv⟩ := h
  exact ⟨c⁻¹, inv_ne_zero hc, by
    rw [hv, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero 2 hc)]⟩

private lemma sqcls_mul {a b c d : ℚ} (h₁ : Descent.SqCls a c) (h₂ : Descent.SqCls b d) :
    Descent.SqCls (a * b) (c * d) := by
  obtain ⟨k, hk, hkv⟩ := h₁
  obtain ⟨m, hm, hmv⟩ := h₂
  exact ⟨k * m, mul_ne_zero hk hm, by rw [hkv, hmv]; ring⟩

private lemma sqcls_ne {a b : ℚ} (h : Descent.SqCls a b) (ha : a ≠ 0) : b ≠ 0 := by
  obtain ⟨c, hc, hv⟩ := h
  intro hb
  rw [hb, mul_zero] at hv
  exact ha hv

/-! ## 2. The square-class refutations -/

private lemma no_sq_neg {d : ℚ} (hd : d < 0) : ¬ Descent.SqCls 1 d := by
  rintro ⟨c, hc0, hcv⟩
  nlinarith [sq_nonneg c]

private lemma no_sq_five : ¬ Descent.SqCls 1 5 := by
  rintro ⟨c, hc0, hcv⟩
  refine RankOne.notSquareFive ⟨1 / c, ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hc0 hc0)]
  linear_combination -hcv

/-- A difference realized as a double forces the slot-class product into the trivial
class. -/
private lemma diff_gives_sqcls {A B Q : RankOne.E5.Point} (hAB : A - B = Q + Q)
    {dA dB pr : ℚ} (hA : Descent.SqCls (RankOne.slotOne A) dA)
    (hB : Descent.SqCls (RankOne.slotOne B) dB) (hpr : dA * dB = pr) :
    Descent.SqCls 1 pr := by
  obtain ⟨hom1, -⟩ :=
    FaceHomomorphism.theRankOneFaceIsAHomomorphismEverywhereHolds A (-B)
  rw [slotOne_neg, ← sub_eq_add_neg, hAB] at hom1
  obtain ⟨k1, -⟩ := FaceHomomorphism.theDoublesLandInTheKernelOnTheFiveCurve Q
  have h2 : Descent.SqCls (RankOne.slotOne A * RankOne.slotOne B) pr := by
    rw [← hpr]
    exact sqcls_mul hA hB
  exact sqcls_trans (sqcls_trans (sqcls_symm k1) hom1) h2

/-! ## 3. The torsion trio, pairwise non-congruent modulo doubles -/

private def tor3 : Fin 3 → RankOne.E5.Point := fun b =>
  if b = 0 then 0 else if b = 1 then RankOne.T0 else RankOne.T5

private lemma fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨iv, hiv⟩
  interval_cases iv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private lemma tor3_add_self (b : Fin 3) : tor3 b + tor3 b = 0 := by
  obtain ⟨h1, h2, -⟩ := RankOne.theThreePointsAreHalfTurns
  fin_cases b <;> simp [tor3, h1, h2]

private lemma tor3_sub_ne_double (b b' : Fin 3) (hbb : b ≠ b')
    (Q : RankOne.E5.Point) : tor3 b - tor3 b' ≠ Q + Q := by
  intro hc
  obtain ⟨⟨e1, -⟩, ⟨a1, -⟩, ⟨b1, -⟩, -, -, -⟩ := RankOne.theFaceValues
  have t0 : tor3 0 = 0 := by simp [tor3]
  have t1 : tor3 1 = RankOne.T0 := by simp [tor3]
  have t2 : tor3 2 = RankOne.T5 := by simp [tor3]
  have hs0 : Descent.SqCls (RankOne.slotOne (0 : RankOne.E5.Point)) 1 := by
    rw [e1]
    exact Descent.sqClsRefl 1
  have hsT0 : Descent.SqCls (RankOne.slotOne RankOne.T0) (-25) := by
    rw [a1]
    exact Descent.sqClsRefl _
  have hsT5 : Descent.SqCls (RankOne.slotOne RankOne.T5) 5 := by
    rw [b1]
    exact Descent.sqClsRefl _
  rcases fin3_cases b with rfl | rfl | rfl <;> rcases fin3_cases b' with rfl | rfl | rfl
  · exact hbb rfl
  · rw [t0, t1] at hc
    exact no_sq_neg (d := -25) (by norm_num)
      (diff_gives_sqcls (pr := -25) hc hs0 hsT0 (by norm_num))
  · rw [t0, t2] at hc
    exact no_sq_five (diff_gives_sqcls (pr := 5) hc hs0 hsT5 (by norm_num))
  · rw [t1, t0] at hc
    exact no_sq_neg (d := -25) (by norm_num)
      (diff_gives_sqcls (pr := -25) hc hsT0 hs0 (by norm_num))
  · exact hbb rfl
  · rw [t1, t2] at hc
    exact no_sq_neg (d := -125) (by norm_num)
      (diff_gives_sqcls (pr := -125) hc hsT0 hsT5 (by norm_num))
  · rw [t2, t0] at hc
    exact no_sq_five (diff_gives_sqcls (pr := 5) hc hsT5 hs0 (by norm_num))
  · rw [t2, t1] at hc
    exact no_sq_neg (d := -125) (by norm_num)
      (diff_gives_sqcls (pr := -125) hc hsT5 hsT0 (by norm_num))
  · exact hbb rfl

/-! ## 4. The eight-class pigeonhole -/

private def dv : Fin 8 → ℚ × ℚ := fun i =>
  if i = 0 then (1, 1) else if i = 1 then (1, 5) else if i = 2 then (5, 2)
  else if i = 3 then (5, 10) else if i = 4 then (-1, -1) else if i = 5 then (-1, -5)
  else if i = 6 then (-5, -2) else (-5, -10)

/-- **The nine collide**: any family of nine points contains two whose difference is
a double — the face image is eight classes, the face is a homomorphism, and the
kernel is the doubles. -/
private lemma face_collision (f : Fin 3 × Fin 3 → RankOne.E5.Point) :
    ∃ x x', x ≠ x' ∧ ∃ Q : RankOne.E5.Point, f x - f x' = Q + Q := by
  have hcls : ∀ x, ∃ i : Fin 8,
      Descent.SqCls (RankOne.slotOne (f x)) (dv i).1 ∧
      Descent.SqCls (RankOne.slotTwo (f x)) (dv i).2 := by
    intro x
    obtain ⟨d₁, d₂, hreal, h1, h2⟩ :=
      FaceImageFive.theFaceImageAtFiveIsTheRealizedEight (f x)
    rcases hreal with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, by simpa [dv] using h1, by simpa [dv] using h2⟩
    · exact ⟨1, by simpa [dv] using h1, by simpa [dv] using h2⟩
    · exact ⟨2, by simpa [dv] using h1, by simpa [dv] using h2⟩
    · exact ⟨3, by simpa [dv] using h1, by simpa [dv] using h2⟩
    · exact ⟨4, by simpa [dv] using h1, by simpa [dv] using h2⟩
    · exact ⟨5, by simpa [dv] using h1, by simpa [dv] using h2⟩
    · exact ⟨6, by simpa [dv] using h1, by simpa [dv] using h2⟩
    · exact ⟨7, by simpa [dv] using h1, by simpa [dv] using h2⟩
  choose idx hidx using hcls
  obtain ⟨x, x', hne, hxx⟩ := Fintype.exists_ne_map_eq_of_card_lt idx
    (by simp only [Fintype.card_prod, Fintype.card_fin]; norm_num)
  refine ⟨x, x', hne, ?_⟩
  have h11 := (hidx x).1
  have h12 := (hidx x).2
  have h21 := (hidx x').1
  have h22 := (hidx x').2
  rw [← hxx] at h21 h22
  have hda : (dv (idx x)).1 ≠ 0 := sqcls_ne h11 (slotOne5_ne _)
  have hdb : (dv (idx x)).2 ≠ 0 := sqcls_ne h12 (slotTwo5_ne _)
  obtain ⟨hom1, hom2⟩ :=
    FaceHomomorphism.theRankOneFaceIsAHomomorphismEverywhereHolds (f x) (-(f x'))
  rw [slotOne_neg, ← sub_eq_add_neg] at hom1
  rw [slotTwo_neg, ← sub_eq_add_neg] at hom2
  have hface1 : Descent.SqCls (RankOne.slotOne (f x - f x')) 1 :=
    sqcls_trans hom1 (sqcls_trans (sqcls_mul h11 h21)
      ⟨(dv (idx x)).1, hda, by ring⟩)
  have hface2 : Descent.SqCls (RankOne.slotTwo (f x - f x')) 1 :=
    sqcls_trans hom2 (sqcls_trans (sqcls_mul h12 h22)
      ⟨(dv (idx x)).2, hdb, by ring⟩)
  obtain ⟨Q, hQ⟩ := FiveHalving.theKernelIsTheDoublesAtFive _ hface1 hface2
  exact ⟨Q, hQ.symm⟩

/-! ## 5. The rank bound -/

private lemma familyFive : FamilyFace.E ((5 : ℕ) : ℚ) = RankOne.E5 := by
  unfold FamilyFace.E RankOne.E5
  norm_num

/-- Two integer Finsupps on fewer than two coordinates are dependent. -/
private lemma finsupp_pair_dep {n : ℕ} (hn : n < 2) (v₀ v₁ : Fin n →₀ ℤ) :
    ∃ c₀ c₁ : ℤ, ¬(c₀ = 0 ∧ c₁ = 0) ∧ c₀ • v₀ + c₁ • v₁ = 0 := by
  match n, hn, v₀, v₁ with
  | 0, _, v₀, v₁ =>
    refine ⟨1, 0, by simp, ?_⟩
    have h0 : v₀ = 0 := by
      apply Finsupp.ext
      intro j
      exact absurd j.2 (Nat.not_lt_zero _)
    simp [h0]
  | 1, _, v₀, v₁ =>
    by_cases h0 : v₀ = 0
    · exact ⟨1, 0, by simp, by simp [h0]⟩
    · refine ⟨v₁ ⟨0, one_pos⟩, -(v₀ ⟨0, one_pos⟩), ?_, ?_⟩
      · rintro ⟨-, h2⟩
        apply h0
        apply Finsupp.ext
        intro j
        rw [Subsingleton.elim j (⟨0, one_pos⟩ : Fin 1)]
        simpa using neg_eq_zero.mp h2
      · apply Finsupp.ext
        intro j
        rw [Subsingleton.elim j (⟨0, one_pos⟩ : Fin 1)]
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
          Finsupp.coe_zero, Pi.zero_apply]
        ring

set_option maxHeartbeats 2000000 in
/-- **THE ALGEBRAIC RANK AT FIVE IS BELOW TWO**: no two points of `y² = x³ − 25x`
are independent modulo torsion.  Finite generation presents the group as `ℤⁿ × T`;
independence would force `n ≥ 2`, and the two free directions crossed with the
torsion trio give nine points pairwise not differing by doubles — against the
eight-class face. -/
theorem theAlgebraicRankAtFiveIsBelowTwo (r : ℕ) (hr : 2 ≤ r) :
    ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast 5 r := by
  intro hR
  unfold BirchSwinnertonDyer.AlgebraicRankAtLeast
    BirchSwinnertonDyer.IndependentModTorsion BirchSwinnertonDyer.IsTorsion at hR
  rw [familyFive] at hR
  obtain ⟨Pts, hind⟩ := hR
  set j₀ : Fin r := ⟨0, by omega⟩ with hj₀
  set j₁ : Fin r := ⟨1, by omega⟩ with hj₁
  have hj01 : j₀ ≠ j₁ := by
    rw [hj₀, hj₁]
    exact Fin.ne_of_val_ne (by norm_num)
  -- pair independence, extracted from the family
  have hpair : ∀ c₀ c₁ : ℤ,
      (∃ k : ℕ, 0 < k ∧ k • (c₀ • Pts j₀ + c₁ • Pts j₁) = 0) → c₀ = 0 ∧ c₁ = 0 := by
    intro c₀ c₁ htorc
    set c' : Fin r → ℤ := fun j => if j = j₀ then c₀ else if j = j₁ then c₁ else 0
      with hc'
    have hsplit : ∀ j : Fin r, c' j • Pts j
        = (if j = j₀ then c₀ • Pts j else 0) + (if j = j₁ then c₁ • Pts j else 0) := by
      intro j
      simp only [hc']
      by_cases h1 : j = j₀
      · rw [if_pos h1, if_pos h1, if_neg (by rw [h1]; exact hj01), add_zero]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : j = j₁
        · rw [if_pos h2, if_pos h2, zero_add]
        · rw [if_neg h2, if_neg h2]
          simp
    have hsum : (∑ j : Fin r, c' j • Pts j) = c₀ • Pts j₀ + c₁ • Pts j₁ := by
      rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ j₀ fun j => c₀ • Pts j,
        Finset.sum_ite_eq' Finset.univ j₁ fun j => c₁ • Pts j,
        if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
    have hall := hind c' (by rw [hsum]; exact htorc)
    constructor
    · simpa [hc'] using hall j₀
    · simpa [hc', Ne.symm hj01] using hall j₁
  -- finite generation and the structure theorem
  haveI : AddGroup.FG (RankOne.E5.Point) :=
    FiveDescent.theMordellWeilGroupIsFinitelyGenerated
  obtain ⟨n, ι, hι, p, hp, e, ⟨F⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod (RankOne.E5.Point)
  haveI := hι
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  haveI : Finite (⨁ i, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  -- the torsion criterion: zero free part means finite order
  have htor : ∀ X : RankOne.E5.Point, (F X).1 = 0 →
      ∃ k : ℕ, 0 < k ∧ k • X = 0 := by
    intro X hX
    refine ⟨Nat.card (⨁ i, ZMod (p i ^ e i)), Nat.card_pos, ?_⟩
    apply F.injective
    rw [map_nsmul, map_zero]
    have h2 : (Nat.card (⨁ i, ZMod (p i ^ e i))) • F X
        = ((Nat.card (⨁ i, ZMod (p i ^ e i))) • (F X).1,
           (Nat.card (⨁ i, ZMod (p i ^ e i))) • (F X).2) := rfl
    rw [h2, hX, smul_zero, card_nsmul_eq_zero']
    rfl
  -- independence forces at least two free directions
  have hn2 : 2 ≤ n := by
    by_contra hn
    push_neg at hn
    obtain ⟨c₀, c₁, hcne, hczero⟩ :=
      finsupp_pair_dep hn (F (Pts j₀)).1 (F (Pts j₁)).1
    refine hcne ⟨(hpair c₀ c₁ ?_).1, (hpair c₀ c₁ ?_).2⟩ <;>
    · apply htor
      rw [map_add, map_zsmul, map_zsmul]
      show c₀ • (F (Pts j₀)).1 + c₁ • (F (Pts j₁)).1 = 0
      exact hczero
  -- the torsion trio has zero free part
  have hfree : ∀ b : Fin 3, (F (tor3 b)).1 = 0 := by
    intro b
    have h2 : F (tor3 b) + F (tor3 b) = 0 := by
      rw [← map_add, tor3_add_self b, map_zero]
    have h3 : (F (tor3 b)).1 + (F (tor3 b)).1 = 0 := by
      have h4 := congrArg Prod.fst h2
      simpa using h4
    ext j
    have h5 := DFunLike.congr_fun h3 j
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h5 ⊢
    omega
  -- the nine points
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  have hi01 : i₀ ≠ i₁ := by
    rw [hi₀, hi₁]
    exact Fin.ne_of_val_ne (by norm_num)
  set wv : Fin 3 → (Fin n →₀ ℤ) := fun a =>
    if a = 0 then 0 else if a = 1 then Finsupp.single i₀ 1 else Finsupp.single i₁ 1
    with hwv
  set tt : Fin 3 → (⨁ i, ZMod (p i ^ e i)) := fun b => (F (tor3 b)).2 with htt
  obtain ⟨x, x', hnexx, Q, hQ⟩ :=
    face_collision fun ab => F.symm (wv ab.1, tt ab.2)
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := x'
  dsimp only at hQ
  have himg : ((wv a, tt b) : (Fin n →₀ ℤ) × (⨁ i, ZMod (p i ^ e i)))
      - (wv a', tt b') = F Q + F Q := by
    have h1 := congrArg F hQ
    rwa [map_sub, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h1
  have hfst : wv a - wv a' = (F Q).1 + (F Q).1 := by
    have h2 := congrArg Prod.fst himg
    simpa using h2
  by_cases haa : a = a'
  · -- the same free direction: the torsion trio collides with a double
    subst haa
    have hbb : b ≠ b' := by
      intro h
      exact hnexx (by rw [h])
    have hFb : F (tor3 b) = (0, tt b) := Prod.ext_iff.mpr ⟨hfree b, rfl⟩
    have hFb' : F (tor3 b') = (0, tt b') := Prod.ext_iff.mpr ⟨hfree b', rfl⟩
    have htdiff : tor3 b - tor3 b' = Q + Q := by
      rw [show tor3 b = F.symm (0, tt b) from by
          rw [← hFb, AddEquiv.symm_apply_apply],
        show tor3 b' = F.symm (0, tt b') from by
          rw [← hFb', AddEquiv.symm_apply_apply],
        ← map_sub,
        show ((0, tt b) : (Fin n →₀ ℤ) × (⨁ i, ZMod (p i ^ e i))) - (0, tt b')
            = ((wv a, tt b) : (Fin n →₀ ℤ) × (⨁ i, ZMod (p i ^ e i))) - (wv a, tt b')
          from by rw [Prod.mk_sub_mk, Prod.mk_sub_mk, sub_self, sub_self],
        map_sub]
      exact hQ
    exact tor3_sub_ne_double b b' hbb Q htdiff
  · -- different free directions: parity at one coordinate refutes the double
    rcases fin3_cases a with rfl | rfl | rfl <;>
      rcases fin3_cases a' with rfl | rfl | rfl
    · exact haa rfl
    · rw [show wv 0 = 0 from by simp [hwv],
        show wv 1 = Finsupp.single i₀ 1 from by simp [hwv]] at hfst
      have hev := DFunLike.congr_fun hfst i₀
      rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same] at hev
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hev
      omega
    · rw [show wv 0 = 0 from by simp [hwv],
        show wv 2 = Finsupp.single i₁ 1 from by simp [hwv]] at hfst
      have hev := DFunLike.congr_fun hfst i₁
      rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same] at hev
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hev
      omega
    · rw [show wv 1 = Finsupp.single i₀ 1 from by simp [hwv],
        show wv 0 = 0 from by simp [hwv]] at hfst
      have hev := DFunLike.congr_fun hfst i₀
      rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same] at hev
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hev
      omega
    · exact haa rfl
    · rw [show wv 1 = Finsupp.single i₀ 1 from by simp [hwv],
        show wv 2 = Finsupp.single i₁ 1 from by simp [hwv]] at hfst
      have hev := DFunLike.congr_fun hfst i₀
      rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hi01] at hev
      omega
    · rw [show wv 2 = Finsupp.single i₁ 1 from by simp [hwv],
        show wv 0 = 0 from by simp [hwv]] at hfst
      have hev := DFunLike.congr_fun hfst i₁
      rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same] at hev
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hev
      omega
    · rw [show wv 2 = Finsupp.single i₁ 1 from by simp [hwv],
        show wv 1 = Finsupp.single i₀ 1 from by simp [hwv]] at hfst
      have hev := DFunLike.congr_fun hfst i₀
      rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hi01] at hev
      omega
    · exact haa rfl

/-! ## 6. The rank clause, whole at five -/

/-- **THE ALGEBRAIC RANK AT FIVE IS EXACTLY ONE**: at least one by the point
`(−4, 6)` against the torsion classification; below two by the descent. -/
theorem theAlgebraicRankIsOneAtFive : BirchSwinnertonDyer.AlgebraicRankIs 5 1 :=
  ⟨BirchSwinnertonDyer.theAlgebraicRankAtFiveIsAtLeastOne,
   theAlgebraicRankAtFiveIsBelowTwo 2 le_rfl⟩

/-- **The two-sided rank-one instance**: the analytic rank of the declared witness
is exactly one, and the algebraic rank is exactly one. -/
theorem theTwoSidedRankOneInstanceAtFive :
    BirchSwinnertonDyer.analyticRank FiveWitness.theWitnessAtFive = 1 ∧
    BirchSwinnertonDyer.AlgebraicRankIs 5 1 :=
  ⟨FiveWitness.theAnalyticRankAtFiveIsOne, theAlgebraicRankIsOneAtFive⟩

/-- **THE RANK CLAUSE HOLDS WHOLE AT FIVE**: for every `r`, the analytic rank of the
witness equals `r` exactly when the algebraic rank is `r` — the complete rank clause
of the posed Birch–Swinnerton-Dyer conjecture at the rank-one instance, with every
ingredient a theorem of this tree. -/
theorem theRankClauseHoldsWholeAtFive :
    BirchSwinnertonDyer.TheRankClause 5 FiveWitness.theWitnessAtFive := by
  intro r
  constructor
  · intro h
    have h1 : (1 : ℕ∞) = (r : ℕ∞) :=
      FiveWitness.theAnalyticRankAtFiveIsOne.symm.trans h
    have h2 : r = 1 := by exact_mod_cast h1.symm
    rw [h2]
    exact theAlgebraicRankIsOneAtFive
  · intro h
    rcases r with _ | (_ | m)
    · exact absurd BirchSwinnertonDyer.theAlgebraicRankAtFiveIsAtLeastOne h.2
    · exact_mod_cast FiveWitness.theAnalyticRankAtFiveIsOne
    · exact absurd h.1 (theAlgebraicRankAtFiveIsBelowTwo (m + 2) (by omega))

end Soma.Holonics.Millennium.FiveRank
