import ElementaryHolonics.Millennium.FamilyLogRank
import Mathlib.Tactic

/-!
# FamilyPrimeRank: the rank is uniformly bounded at every prime modulus

**The constant family rank bound.**  At a prime modulus the divisor lattice of `2n`
has four rungs, so each slot class lives among the eight signed classes
`{±1, ±2, ±n, ±2n}` and the face image has at most `64` cells:

* **`theClassesCollideAtEveryPrimeModulus`** — any family of more than `64` points
  contains two whose difference is a double, at every prime modulus at once;
* **`theAlgebraicRankIsUniformlyBoundedAtEveryPrimeModulus`** — whenever
  `64 < 3·2^r`, no `r` points are independent modulo torsion;
* **`theRankIsAtMostFourAtEveryPrimeModulus`** — the rank of the congruent-number
  curve `y² = x³ − p²x` is at most **four**, uniformly over all primes `p` — the
  logarithmic family bound sharpened to a constant on the prime moduli.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyPrimeRank

open WeierstrassCurve.Affine
open DirectSum
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyKernel

/-- A divisor of twice a prime is one of the four rungs. -/
private lemma dvd_two_mul_prime {n k : ℕ} (hnp : n.Prime) (h : k ∣ 2 * n) :
    k = 1 ∨ k = 2 ∨ k = n ∨ k = 2 * n := by
  by_cases hnk : n ∣ k
  · obtain ⟨j, hj⟩ := hnk
    have hjd : j ∣ 2 := by
      have h2 : n * j ∣ n * 2 := by
        rw [← hj]
        rw [show n * 2 = 2 * n from by ring]
        exact h
      exact (mul_dvd_mul_iff_left hnp.pos.ne').mp h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hjd with rfl | rfl
    · right; right; left
      omega
    · right; right; right
      omega
  · have hcop : Nat.Coprime k n :=
      (Nat.Prime.coprime_iff_not_dvd hnp |>.mpr hnk).symm
    have hk2 : k ∣ 2 := hcop.dvd_of_dvd_mul_right h
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
    · left; rfl
    · right; left; rfl

/-- The eight signed classes at a prime modulus. -/
private def rungs (n : ℕ) : Finset ℤ :=
  {1, -1, 2, -2, (n : ℤ), -(n : ℤ), 2 * (n : ℤ), -(2 * (n : ℤ))}

private lemma mem_rungs {n : ℕ} (hnp : n.Prime) {d : ℤ} (hd0 : d ≠ 0)
    (hdvd : d.natAbs ∣ 2 * n) : d ∈ rungs n := by
  have h4 := dvd_two_mul_prime hnp hdvd
  have habs := Int.natAbs_eq d
  unfold rungs
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

private lemma rungs_card_le (n : ℕ) : (rungs n).card ≤ 8 := by
  unfold rungs
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine Nat.succ_le_succ ?_
  exact Finset.card_singleton _ |>.le

set_option maxHeartbeats 1000000 in
/-- **THE CLASSES COLLIDE AT EVERY PRIME MODULUS**: any family of more than `64`
points contains two whose difference is a double — the divisor lattice of `2p` has
four rungs, so the face image has at most `8 × 8` cells, uniformly in the prime. -/
theorem theClassesCollideAtEveryPrimeModulus (n : ℕ) (hnp : n.Prime) {α : Type}
    [Fintype α] (hcard : 64 < Fintype.card α)
    (f : α → (FamilyFace.E ((n : ℚ))).Point) :
    ∃ a b, a ≠ b ∧ ∃ Q : (FamilyFace.E ((n : ℚ))).Point, f a - f b = Q + Q := by
  have hn : 0 < n := hnp.pos
  set box : Finset (ℤ × ℤ) := rungs n ×ˢ rungs n with hbox
  have hmaps : ∀ a : α, FamilyCollision.classOf hn (f a) ∈ box := by
    intro a
    obtain ⟨h10, h20, h1d, h2d, -, -⟩ := FamilyCollision.classOf_spec hn (f a)
    rw [hbox, Finset.mem_product]
    exact ⟨mem_rungs hnp h10 h1d, mem_rungs hnp h20 h2d⟩
  have hboxcard : box.card ≤ 64 := by
    rw [hbox, Finset.card_product]
    have h := rungs_card_le n
    nlinarith
  have hlt : box.card < Fintype.card α := by omega
  obtain ⟨a, -, b, -, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by rw [Finset.card_univ]; exact hlt) fun a _ => hmaps a
  exact ⟨a, b, hab, FamilyCollision.sameClass_double hn (f a) (f b) hfab⟩

set_option maxHeartbeats 2000000 in
/-- **THE ALGEBRAIC RANK IS UNIFORMLY BOUNDED AT EVERY PRIME MODULUS**: whenever
`64 < 3·2^r`, no `r` points are independent modulo torsion, uniformly in the
prime. -/
theorem theAlgebraicRankIsUniformlyBoundedAtEveryPrimeModulus (n r : ℕ)
    (hnp : n.Prime) (hr : 64 < 3 * 2 ^ r) :
    ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast n r := by
  have hn : 0 < n := hnp.pos
  intro hR
  unfold BirchSwinnertonDyer.AlgebraicRankAtLeast
    BirchSwinnertonDyer.IndependentModTorsion BirchSwinnertonDyer.IsTorsion at hR
  obtain ⟨Pts, hind⟩ := hR
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  haveI : AddGroup.FG ((FamilyFace.E ((n : ℚ))).Point) :=
    FamilyMordell.theMordellWeilTheoremAtEveryModulus n hn
  obtain ⟨m, ι, hι, p, hp, e, ⟨F⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod ((FamilyFace.E ((n : ℚ))).Point)
  haveI := hι
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  haveI : Finite (⨁ i, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have htor : ∀ X : (FamilyFace.E ((n : ℚ))).Point, (F X).1 = 0 →
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
      have h2 := map_sum (AddMonoidHom.fst (Fin m →₀ ℤ) (⨁ i, ZMod (p i ^ e i)))
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
  -- the torsion trio and its free-part vanishing
  have h00 : (FamilyFace.E ((n : ℚ))).Nonsingular 0 0 := by
    rw [nonsingular_iff, equation_iff]
    constructor
    · simp [FamilyFace.E]
    · left
      simp only [FamilyFace.E]
      intro hc
      nlinarith [hc, hnq]
  have hn0 : (FamilyFace.E ((n : ℚ))).Nonsingular ((n : ℚ)) 0 := by
    rw [nonsingular_iff, equation_iff]
    constructor
    · simp only [FamilyFace.E]
      ring
    · left
      simp only [FamilyFace.E]
      intro hc
      nlinarith [hc, hnq]
  set T : Fin 3 → (FamilyFace.E ((n : ℚ))).Point :=
    ![0, Point.some h00, Point.some hn0] with hT
  have hT0 : T 0 = 0 := rfl
  have hT1 : T 1 = Point.some h00 := rfl
  have hT2 : T 2 = Point.some hn0 := rfl
  have htrio2 : ∀ b : Fin 3, T b + T b = 0 := by
    intro b
    rcases FamilyRankFin3.fin3_cases b with rfl | rfl | rfl
    · rw [hT0, add_zero]
    · rw [hT1]
      exact Point.add_self_of_Y_eq (by simp [negY, FamilyFace.E])
    · rw [hT2]
      exact Point.add_self_of_Y_eq (by simp [negY, FamilyFace.E])
  have hfree : ∀ b : Fin 3, (F (T b)).1 = 0 := by
    intro b
    have h2 : F (T b) + F (T b) = 0 := by
      rw [← map_add, htrio2 b, map_zero]
    have h3 : (F (T b)).1 + (F (T b)).1 = 0 := by
      have h4 := congrArg Prod.fst h2
      simpa using h4
    ext j
    have h5 := DFunLike.congr_fun h3 j
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h5 ⊢
    omega
  set tt : Fin 3 → (⨁ i, ZMod (p i ^ e i)) := fun b => (F (T b)).2 with htt
  have hFT : ∀ b : Fin 3, F (T b) = (0, tt b) := fun b =>
    Prod.ext_iff.mpr ⟨hfree b, rfl⟩
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
    · by_cases hb : ε i
      · rw [if_pos hb, if_pos hb, Finsupp.single_eq_same]
      · rw [if_neg hb, if_neg hb, Finsupp.coe_zero, Pi.zero_apply]
    · intro j _ hji
      by_cases hb : ε j
      · rw [if_pos hb]
        exact Finsupp.single_eq_of_ne
          (fun hc => hji (Fin.castLE_injective hrm hc).symm)
      · rw [if_neg hb, Finsupp.coe_zero, Pi.zero_apply]
    · intro habs
      exact absurd (Finset.mem_univ i) habs
  -- the colliding family of `3·2^r` points
  obtain ⟨x, x', hnexx, Q, hQ⟩ :=
    theClassesCollideAtEveryPrimeModulus n hnp
      (α := (Fin r → Bool) × Fin 3)
      (by
        simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
          Fintype.card_bool]
        omega)
      (fun ab => F.symm (wv ab.1, tt ab.2))
  obtain ⟨ε, b⟩ := x
  obtain ⟨δ, b'⟩ := x'
  dsimp only at hQ
  have himg : ((wv ε, tt b) : (Fin m →₀ ℤ) × (⨁ i, ZMod (p i ^ e i)))
      - (wv δ, tt b') = F Q + F Q := by
    have h1 := congrArg F hQ
    rwa [map_sub, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h1
  have hfst : wv ε - wv δ = (F Q).1 + (F Q).1 := by
    have h2 := congrArg Prod.fst himg
    simpa using h2
  by_cases hεδ : ε = δ
  · -- same signs: the torsion trio collides — refused
    subst hεδ
    have hbb : b ≠ b' := by
      intro h
      exact hnexx (by rw [h])
    have hFb : F (T b) = (0, tt b) := hFT b
    have hFb' : F (T b') = (0, tt b') := hFT b'
    have htdiff : T b - T b' = F.symm (0, (F Q).2) + F.symm (0, (F Q).2) := by
      have hsnd : tt b - tt b' = (F Q).2 + (F Q).2 := by
        have h2 := congrArg Prod.snd himg
        simpa using h2
      apply F.injective
      rw [map_sub, map_add, AddEquiv.apply_symm_apply, hFb, hFb',
        Prod.mk_sub_mk, Prod.mk_add_mk]
      exact Prod.ext_iff.mpr ⟨by simp, hsnd⟩
    exact FamilyCollision.theTorsionTrioDoesNotCollideAtEveryModulus hn T hT0 hT1
      hT2 b b' hbb (F.symm (0, (F Q).2)) htdiff
  · -- different signs: parity at the first differing coordinate refuses the double
    have hex : ∃ i : Fin r, ε i ≠ δ i := by
      by_contra hall
      push_neg at hall
      exact hεδ (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    have hev := DFunLike.congr_fun hfst (Fin.castLE hrm i₀)
    rw [Finsupp.sub_apply, Finsupp.add_apply, hwv_apply, hwv_apply] at hev
    rcases Bool.eq_false_or_eq_true (ε i₀) with hε | hε <;>
      rcases Bool.eq_false_or_eq_true (δ i₀) with hδ | hδ
    · exact hi₀ (hε.trans hδ.symm)
    · rw [hε, hδ] at hev
      simp only [Bool.false_eq_true, if_false, if_pos] at hev
      omega
    · rw [hε, hδ] at hev
      simp only [Bool.false_eq_true, if_false, if_pos] at hev
      omega
    · exact hi₀ (hε.trans hδ.symm)


/-- **THE RANK IS AT MOST FOUR AT EVERY PRIME MODULUS**: no five points of
`y² = x³ − p²x` are independent modulo torsion, for **every** prime `p` at once —
the uniform constant bound the divisor lattice forces. -/
theorem theRankIsAtMostFourAtEveryPrimeModulus (n : ℕ) (hnp : n.Prime) :
    ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast n 5 :=
  theAlgebraicRankIsUniformlyBoundedAtEveryPrimeModulus n 5 hnp (by norm_num)

end Soma.Holonics.Millennium.FamilyPrimeRank

