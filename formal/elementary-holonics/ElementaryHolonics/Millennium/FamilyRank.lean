import ElementaryHolonics.Millennium.FamilyCollision
import ElementaryHolonics.Millennium.BirchSwinnertonDyer
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# FamilyRank: the algebraic rank is effectively bounded at every modulus

**The family rank endgame.**  On every congruent-number curve `y² = x³ − n²x` with
`n ≥ 1`, the algebraic rank of the posed conjecture is bounded by an explicit
function of the modulus:

* **`theAlgebraicRankIsBoundedAtEveryModulus`** —
  `¬ AlgebraicRankAtLeast n ((4n+1)²)`, for every `n ≥ 1`.

The assembly: the Mordell–Weil theorem (`FamilyMordell`) admits the structure
theorem, presenting the group as `ℤᵐ × T`; independence modulo torsion transports
to ℚ-linear independence of the free parts, forcing `m ≥ (4n+1)²`; the
`(4n+1)²` single-coordinate free directions crossed with the torsion trio give
`3·(4n+1)²` points pairwise not congruent modulo doubles — against the class
pigeonhole (`FamilyCollision`), which caps such families at `(4n+1)²`.  The rank
side of the conjecture is thereby a **finite, effectively bounded** quantity at
every modulus.  Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyRank

open WeierstrassCurve.Affine
open DirectSum
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyKernel

set_option maxHeartbeats 2000000 in
/-- **THE ALGEBRAIC RANK IS BOUNDED AT EVERY MODULUS**: no `(4n+1)²` points of
`y² = x³ − n²x` are independent modulo torsion. -/
theorem theAlgebraicRankIsBoundedAtEveryModulus (n : ℕ) (hn : 0 < n) :
    ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast n ((4 * n + 1) ^ 2) := by
  intro hR
  set B : ℕ := (4 * n + 1) ^ 2 with hB
  unfold BirchSwinnertonDyer.AlgebraicRankAtLeast
    BirchSwinnertonDyer.IndependentModTorsion BirchSwinnertonDyer.IsTorsion at hR
  obtain ⟨Pts, hind⟩ := hR
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  -- finite generation and the structure theorem
  haveI : AddGroup.FG ((FamilyFace.E ((n : ℚ))).Point) :=
    FamilyMordell.theMordellWeilTheoremAtEveryModulus n hn
  obtain ⟨m, ι, hι, p, hp, e, ⟨F⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod ((FamilyFace.E ((n : ℚ))).Point)
  haveI := hι
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  haveI : Finite (⨁ i, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  -- the torsion criterion: zero free part means finite order
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
  -- the free parts of the independent points
  set v : Fin B → (Fin m →₀ ℤ) := fun i => (F (Pts i)).1 with hv
  have hindZ : ∀ c : Fin B → ℤ, (∑ i, c i • v i) = 0 → ∀ i, c i = 0 := by
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
  -- the free rank dominates B: transport to ℚ-linear independence
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
  set w : Fin B → (Fin m →₀ ℚ) := fun i => castHom (v i) with hw
  have hindW : LinearIndependent ℚ w := by
    rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    refine hindZ c ?_ i
    apply hcastInj
    rw [map_sum, map_zero]
    have hterm : ∀ j : Fin B, castHom (c j • v j) = c j • w j := by
      intro j
      rw [map_zsmul, hw]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    exact hc
  have hBm : B ≤ m := by
    have h1 := hindW.fintype_card_le_finrank
    rw [Module.finrank_finsupp_self] at h1
    simpa using h1
  -- the torsion trio
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
    ![0, Point.some 0 0 h00, Point.some (n : ℚ) 0 hn0] with hT
  have hT0 : T 0 = 0 := rfl
  have hT1 : T 1 = Point.some 0 0 h00 := rfl
  have hT2 : T 2 = Point.some (n : ℚ) 0 hn0 := rfl
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
  -- the colliding family
  obtain ⟨x, x', hnexx, Q, hQ⟩ :=
    FamilyCollision.theClassesCollideAtEveryModulus hn
      (α := Fin B × Fin 3)
      (by
        simp only [Fintype.card_prod, Fintype.card_fin]
        have hB1 : 1 ≤ B := by
          rw [hB]
          have h2 : 1 ≤ 4 * n + 1 := by omega
          calc 1 = 1 ^ 2 := by norm_num
            _ ≤ (4 * n + 1) ^ 2 := Nat.pow_le_pow_left h2 2
        omega)
      (fun ab => F.symm (Finsupp.single (Fin.castLE hBm ab.1) (1 : ℤ), tt ab.2))
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := x'
  dsimp only at hQ
  have himg : ((Finsupp.single (Fin.castLE hBm a) (1 : ℤ), tt b)
        : (Fin m →₀ ℤ) × (⨁ i, ZMod (p i ^ e i)))
      - (Finsupp.single (Fin.castLE hBm a') (1 : ℤ), tt b') = F Q + F Q := by
    have h1 := congrArg F hQ
    rwa [map_sub, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h1
  have hfst : Finsupp.single (Fin.castLE hBm a) (1 : ℤ)
      - Finsupp.single (Fin.castLE hBm a') (1 : ℤ) = (F Q).1 + (F Q).1 := by
    have h2 := congrArg Prod.fst himg
    simpa using h2
  by_cases haa : a = a'
  · -- the same free direction: the torsion trio collides — refused
    subst haa
    have hbb : b ≠ b' := by
      intro h
      exact hnexx (by rw [h])
    have hzero : (0 : Fin m →₀ ℤ) = (F Q).1 + (F Q).1 := by
      rw [← hfst, sub_self]
    have hQ1 : (F Q).1 = 0 := by
      ext j
      have h5 := DFunLike.congr_fun hzero j
      simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h5 ⊢
      omega
    have hsnd : tt b - tt b' = (F Q).2 + (F Q).2 := by
      have h2 := congrArg Prod.snd himg
      simpa using h2
    have htdiff : T b - T b' = F.symm (0, (F Q).2) + F.symm (0, (F Q).2) := by
      apply F.injective
      rw [map_sub, map_add, AddEquiv.apply_symm_apply, hFT b, hFT b',
        Prod.mk_sub_mk, Prod.mk_add_mk]
      exact Prod.ext_iff.mpr ⟨by simp, hsnd⟩
    exact FamilyCollision.theTorsionTrioDoesNotCollideAtEveryModulus hn T hT0 hT1
      hT2 b b' hbb (F.symm (0, (F Q).2)) htdiff
  · -- different free directions: parity refuses the double
    have hcast : Fin.castLE hBm a ≠ Fin.castLE hBm a' :=
      fun hc => haa (Fin.castLE_injective hBm hc)
    have hev := DFunLike.congr_fun hfst (Fin.castLE hBm a)
    rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hcast] at hev
    omega

end Soma.Holonics.Millennium.FamilyRank
