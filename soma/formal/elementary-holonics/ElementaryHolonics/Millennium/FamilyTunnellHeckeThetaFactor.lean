import ElementaryHolonics.Millennium.FamilyTunnellHopfThetaLift
import ElementaryHolonics.Millennium.HeckeTheta

/-!
# The surviving Hopf theta current returns the Hecke shell

The signed factor left by the modulo-four Hopf census has one elementary
two-coordinate receiver.  Its first coordinate is constrained to `1 mod 4`;
its second is even and contributes a sign according to whether its residue is
`0` or `2 mod 4`.  Reflecting the first coordinate precisely in the second
case returns the quartic Hecke shell.

This file constructs that reflection as an equivalence of complete finite
occurrence populations and proves equality of their weighted sums.  The proof
is independent of any modular-form classification.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor

open Finset
open Soma.Holonics.Millennium.HeckeTheta
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift

/-- The factor shell before the residue-`2` reflection. -/
def heckeFactorShell (m : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ
      Finset.Icc (-(m : ℤ)) (m : ℤ)).filter fun p =>
    p.1 ^ 2 + p.2 ^ 2 = (m : ℤ) ∧
      p.1 % 4 = 1 ∧ p.2 % 2 = 0

def evenResidueSign (b : ℤ) : ℤ := if b % 4 = 0 then 1 else -1

def heckeFactorWeight (p : ℤ × ℤ) : ℤ := evenResidueSign p.2 * p.1

/-- The swing which reflects the first coordinate exactly over the residue-`2`
sheet. -/
def heckeFactorReflection (p : ℤ × ℤ) : ℤ × ℤ :=
  if p.2 % 4 = 0 then p else (-p.1, p.2)

private theorem even_emod_four_cases {b : ℤ} (hEven : b % 2 = 0) :
    b % 4 = 0 ∨ b % 4 = 2 := by
  omega

private theorem heckeFactorReflection_involutive :
    Function.Involutive heckeFactorReflection := by
  intro p
  unfold heckeFactorReflection
  split_ifs <;> simp_all

private theorem heckeFactorReflection_box {m : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ (Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ
      Finset.Icc (-(m : ℤ)) (m : ℤ)) :
    heckeFactorReflection p ∈
      (Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ
        Finset.Icc (-(m : ℤ)) (m : ℤ) := by
  rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
  rw [Finset.mem_product]
  unfold heckeFactorReflection
  split_ifs with h
  · exact ⟨ha, hb⟩
  · simp only [Finset.mem_Icc] at ha hb ⊢
    exact ⟨⟨by linarith [ha.2], by linarith [ha.1]⟩, hb⟩

private theorem heckeFactorReflection_mem_heckeShell {m : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ heckeFactorShell m) :
    heckeFactorReflection p ∈ heckeShell m := by
  rcases Finset.mem_filter.mp hp with ⟨hpBox, hnorm, haClass, hbEven⟩
  rw [heckeShell, Finset.mem_filter]
  refine ⟨heckeFactorReflection_box hpBox, ?_⟩
  rcases even_emod_four_cases hbEven with hb0 | hb2
  · rw [show heckeFactorReflection p = p by simp [heckeFactorReflection, hb0]]
    refine ⟨hnorm, ?_, hbEven⟩
    omega
  · rw [show heckeFactorReflection p = (-p.1, p.2) by
      simp [heckeFactorReflection, hb2]]
    refine ⟨by simpa using hnorm, ?_, hbEven⟩
    omega

private theorem heckeFactorReflection_mem_factorShell {m : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ heckeShell m) :
    heckeFactorReflection p ∈ heckeFactorShell m := by
  rcases Finset.mem_filter.mp hp with ⟨hpBox, hnorm, hclass, hbEven⟩
  rw [heckeFactorShell, Finset.mem_filter]
  refine ⟨heckeFactorReflection_box hpBox, ?_⟩
  rcases even_emod_four_cases hbEven with hb0 | hb2
  · rw [show heckeFactorReflection p = p by simp [heckeFactorReflection, hb0]]
    refine ⟨hnorm, ?_, hbEven⟩
    omega
  · rw [show heckeFactorReflection p = (-p.1, p.2) by
      simp [heckeFactorReflection, hb2]]
    refine ⟨by simpa using hnorm, ?_, hbEven⟩
    omega

/-- Complete occurrence equivalence between the signed factor shell and the
quartic Hecke shell. -/
def heckeFactorShellEquiv (m : ℕ) :
    {p // p ∈ heckeFactorShell m} ≃ {p // p ∈ heckeShell m} where
  toFun p := ⟨heckeFactorReflection p.1,
    heckeFactorReflection_mem_heckeShell p.2⟩
  invFun p := ⟨heckeFactorReflection p.1,
    heckeFactorReflection_mem_factorShell p.2⟩
  left_inv p := by
    apply Subtype.ext
    exact heckeFactorReflection_involutive p.1
  right_inv p := by
    apply Subtype.ext
    exact heckeFactorReflection_involutive p.1

private theorem reflected_first_eq_factorWeight {m : ℕ}
    (p : {p // p ∈ heckeFactorShell m}) :
    (heckeFactorReflection p.1).1 = heckeFactorWeight p.1 := by
  unfold heckeFactorReflection heckeFactorWeight evenResidueSign
  split_ifs <;> ring

/-- **THE SIGNED FACTOR SHELL IS THE EXISTING HECKE COEFFICIENT.** -/
theorem sum_heckeFactorWeight_eq_heckeCoeff (m : ℕ) :
    (∑ p ∈ heckeFactorShell m, heckeFactorWeight p) = heckeCoeff m := by
  rw [heckeCoeff]
  refine Finset.sum_bij
    (i := fun p (_ : p ∈ heckeFactorShell m) => heckeFactorReflection p)
    ?_ ?_ ?_ ?_
  · intro p hp
    exact heckeFactorReflection_mem_heckeShell hp
  · intro p₁ hp₁ p₂ hp₂ h
    exact heckeFactorReflection_involutive.injective h
  · intro q hq
    refine ⟨heckeFactorReflection q,
      heckeFactorReflection_mem_factorShell hq, ?_⟩
    exact heckeFactorReflection_involutive q
  · intro p hp
    exact (reflected_first_eq_factorWeight ⟨p, hp⟩).symm

/-! ## The returned coefficient stream -/

def heckeFactorShellTheta : PowerSeries ℤ :=
  PowerSeries.mk fun m => ∑ p ∈ heckeFactorShell m, heckeFactorWeight p

def heckeCoefficientSeries : PowerSeries ℤ :=
  PowerSeries.mk heckeCoeff

@[simp] theorem coeff_heckeFactorShellTheta (m : ℕ) :
    PowerSeries.coeff m heckeFactorShellTheta =
      ∑ p ∈ heckeFactorShell m, heckeFactorWeight p := by
  simp [heckeFactorShellTheta]

@[simp] theorem coeff_heckeCoefficientSeries (m : ℕ) :
    PowerSeries.coeff m heckeCoefficientSeries = heckeCoeff m := by
  simp [heckeCoefficientSeries]

/-- The occurrence equivalence closes coefficientwise and therefore closes the
whole formal Hecke stream. -/
theorem heckeFactorShellTheta_eq_heckeCoefficientSeries :
    heckeFactorShellTheta = heckeCoefficientSeries := by
  apply PowerSeries.ext
  intro m
  simp [sum_heckeFactorWeight_eq_heckeCoeff]

/-! ## Coefficient occurrence carrier for the Cauchy product -/

def weightedQuarterSquareTheta (r : QuarterResidue) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ∑ x ∈ quarterSquarePopulation r n, x

@[simp] theorem coeff_weightedQuarterSquareTheta (r : QuarterResidue) (n : ℕ) :
    PowerSeries.coeff n (weightedQuarterSquareTheta r) =
      ∑ x ∈ quarterSquarePopulation r n, x := by
  simp [weightedQuarterSquareTheta]

/-- The complete split-address population underlying one Cauchy coefficient. -/
def squareSplitPopulation (r s : QuarterResidue) (n : ℕ) :
    Finset (Σ kl : ℕ × ℕ, ℤ × ℤ) :=
  (Finset.antidiagonal n).sigma fun kl =>
    quarterSquarePopulation r kl.1 ×ˢ quarterSquarePopulation s kl.2

/-- Multiplication of the two square streams retains the full split address;
the ordinary coefficient is its weighted receiver. -/
theorem coeff_weighted_mul_quarter_eq_splitSum
    (r s : QuarterResidue) (n : ℕ) :
    PowerSeries.coeff n
        (weightedQuarterSquareTheta r * quarterSquareTheta s) =
      ∑ q ∈ squareSplitPopulation r s n, q.2.1 := by
  rw [PowerSeries.coeff_mul]
  simp only [coeff_weightedQuarterSquareTheta, coeff_quarterSquareTheta]
  simp [squareSplitPopulation, Finset.sum_sigma, Finset.sum_product,
    Finset.sum_mul, Finset.mul_sum, mul_comm]

/-- The same occurrence population after forgetting the now-reconstructible
norm split. -/
def residuePairShell (r s : QuarterResidue) (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ
      Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun p =>
    p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) ∧
      (p.1 : ZMod 4) = r.val ∧ (p.2 : ZMod 4) = s.val

def squareIndex (a : ℤ) : ℕ := (a ^ 2).toNat

private theorem squareIndex_cast (a : ℤ) :
    (squareIndex a : ℤ) = a ^ 2 := by
  rw [squareIndex, Int.toNat_of_nonneg (sq_nonneg a)]

private theorem coordinate_mem_squareIndex_box (a : ℤ) :
    a ∈ Finset.Icc (-(squareIndex a : ℤ)) (squareIndex a : ℤ) := by
  simp only [Finset.mem_Icc, squareIndex_cast]
  constructor
  · by_cases ha : 0 ≤ a
    · nlinarith [sq_nonneg a]
    · have ha' : a ≤ -1 := by omega
      have hprod : 0 ≤ (-a) * (-a - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  · by_cases ha : a ≤ 0
    · nlinarith [sq_nonneg a]
    · have ha' : 1 ≤ a := by omega
      have hprod : 0 ≤ a * (a - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith

private theorem pairToSplit_mem {r s : QuarterResidue} {n : ℕ}
    {p : ℤ × ℤ} (hp : p ∈ residuePairShell r s n) :
    (Sigma.mk (squareIndex p.1, squareIndex p.2) p) ∈
      squareSplitPopulation r s n := by
  rcases Finset.mem_filter.mp hp with ⟨hpBox, hnorm, haResidue, hbResidue⟩
  rw [squareSplitPopulation, Finset.mem_sigma]
  constructor
  · rw [Finset.mem_antidiagonal]
    have hcast : ((squareIndex p.1 + squareIndex p.2 : ℕ) : ℤ) = (n : ℤ) := by
      push_cast
      simpa [squareIndex_cast] using hnorm
    exact_mod_cast hcast
  · rw [Finset.mem_product]
    constructor
    · rw [quarterSquarePopulation, Finset.mem_filter]
      exact ⟨coordinate_mem_squareIndex_box p.1, (squareIndex_cast p.1).symm,
        haResidue⟩
    · rw [quarterSquarePopulation, Finset.mem_filter]
      exact ⟨coordinate_mem_squareIndex_box p.2, (squareIndex_cast p.2).symm,
        hbResidue⟩

private theorem splitToPair_mem {r s : QuarterResidue} {n : ℕ}
    {q : Σ kl : ℕ × ℕ, ℤ × ℤ}
    (hq : q ∈ squareSplitPopulation r s n) :
    q.2 ∈ residuePairShell r s n := by
  rcases Finset.mem_sigma.mp hq with ⟨hkl, hab⟩
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  rcases Finset.mem_filter.mp ha with ⟨haBox, haSquare, haResidue⟩
  rcases Finset.mem_filter.mp hb with ⟨hbBox, hbSquare, hbResidue⟩
  rw [residuePairShell, Finset.mem_filter]
  refine ⟨?_, ?_, haResidue, hbResidue⟩
  · rw [Finset.mem_product]
    simp only [Finset.mem_Icc] at haBox hbBox ⊢
    have hk : q.1.1 ≤ n := by
      have := Finset.mem_antidiagonal.mp hkl
      omega
    have hl : q.1.2 ≤ n := by
      have := Finset.mem_antidiagonal.mp hkl
      omega
    have hkZ : (q.1.1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
    have hlZ : (q.1.2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hl
    exact ⟨⟨le_trans (neg_le_neg hkZ) haBox.1,
      le_trans haBox.2 hkZ⟩,
      ⟨le_trans (neg_le_neg hlZ) hbBox.1,
      le_trans hbBox.2 hlZ⟩⟩
  · have hsum := Finset.mem_antidiagonal.mp hkl
    rw [haSquare, hbSquare]
    exact_mod_cast hsum

/-- The split index is reconstructible from the two square coordinates. -/
def squareSplitEquivResiduePair (r s : QuarterResidue) (n : ℕ) :
    {q // q ∈ squareSplitPopulation r s n} ≃
      {p // p ∈ residuePairShell r s n} where
  toFun q := ⟨q.1.2, splitToPair_mem q.2⟩
  invFun p := ⟨Sigma.mk (squareIndex p.1.1, squareIndex p.1.2) p.1,
    pairToSplit_mem p.2⟩
  left_inv q := by
    apply Subtype.ext
    rcases Finset.mem_sigma.mp q.2 with ⟨hkl, hab⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    rcases Finset.mem_filter.mp ha with ⟨haBox, haSquare, haResidue⟩
    rcases Finset.mem_filter.mp hb with ⟨hbBox, hbSquare, hbResidue⟩
    change Sigma.mk (squareIndex q.1.2.1, squareIndex q.1.2.2) q.1.2 = q.1
    apply Sigma.ext
    · apply Prod.ext
      · have h : (squareIndex q.1.2.1 : ℤ) = (q.1.1.1 : ℤ) := by
          rw [squareIndex_cast, haSquare]
        exact_mod_cast h
      · have h : (squareIndex q.1.2.2 : ℤ) = (q.1.1.2 : ℤ) := by
          rw [squareIndex_cast, hbSquare]
        exact_mod_cast h
    · rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Forgetting the split loses no occurrence and preserves the first-coordinate
weight. -/
theorem splitSum_eq_residuePairSum (r s : QuarterResidue) (n : ℕ) :
    (∑ q ∈ squareSplitPopulation r s n, q.2.1) =
      ∑ p ∈ residuePairShell r s n, p.1 := by
  refine Finset.sum_bij
    (i := fun q (_ : q ∈ squareSplitPopulation r s n) => q.2)
    ?_ ?_ ?_ ?_
  · intro q hq
    exact splitToPair_mem hq
  · intro q₁ hq₁ q₂ hq₂ h
    have heq := (squareSplitEquivResiduePair r s n).injective
      (Subtype.ext h :
        (squareSplitEquivResiduePair r s n ⟨q₁, hq₁⟩) =
          squareSplitEquivResiduePair r s n ⟨q₂, hq₂⟩)
    exact congrArg Subtype.val heq
  · intro p hp
    refine ⟨Sigma.mk (squareIndex p.1, squareIndex p.2) p,
      pairToSplit_mem hp, rfl⟩
  · intro q hq
    rfl

theorem coeff_weighted_mul_quarter_eq_residuePairSum
    (r s : QuarterResidue) (n : ℕ) :
    PowerSeries.coeff n
        (weightedQuarterSquareTheta r * quarterSquareTheta s) =
      ∑ p ∈ residuePairShell r s n, p.1 := by
  rw [coeff_weighted_mul_quarter_eq_splitSum,
    splitSum_eq_residuePairSum]

theorem coeff_weighted_mul_evenDifference (n : ℕ) :
    PowerSeries.coeff n
        (weightedQuarterSquareTheta 1 *
          (quarterSquareTheta 0 - quarterSquareTheta 2)) =
      (∑ p ∈ residuePairShell 1 0 n, p.1) -
        ∑ p ∈ residuePairShell 1 2 n, p.1 := by
  rw [mul_sub, map_sub, coeff_weighted_mul_quarter_eq_residuePairSum,
    coeff_weighted_mul_quarter_eq_residuePairSum]

private theorem intCast_zmod_four_eq_fin_iff_emod (x : ℤ) (r : Fin 4) :
    (x : ZMod 4) = r.val ↔ x % 4 = (r.val : ℤ) := by
  have hr0 : (0 : ℤ) ≤ (r.val : ℤ) := by omega
  have hr4 : (r.val : ℤ) < 4 := by exact_mod_cast r.isLt
  simpa [Int.emod_eq_of_lt hr0 hr4] using
    (ZMod.intCast_eq_intCast_iff' x (r.val : ℤ) 4)

def signedResiduePairCarrier (n : ℕ) : Finset (Sum (ℤ × ℤ) (ℤ × ℤ)) :=
  (residuePairShell 1 0 n).disjSum (residuePairShell 1 2 n)

def signedResiduePairValue : Sum (ℤ × ℤ) (ℤ × ℤ) → ℤ × ℤ
  | .inl p => p
  | .inr p => p

def signedResiduePairWeight : Sum (ℤ × ℤ) (ℤ × ℤ) → ℤ
  | .inl p => p.1
  | .inr p => -p.1

private theorem signedResiduePairValue_mem_factorShell {n : ℕ}
    {q : Sum (ℤ × ℤ) (ℤ × ℤ)} (hq : q ∈ signedResiduePairCarrier n) :
    signedResiduePairValue q ∈ heckeFactorShell n := by
  cases q with
  | inl p =>
      have hp : p ∈ residuePairShell 1 0 n := by
        simpa [signedResiduePairCarrier] using hq
      rcases Finset.mem_filter.mp hp with ⟨hpBox, hnorm, ha, hb⟩
      rw [heckeFactorShell, Finset.mem_filter]
      refine ⟨hpBox, hnorm, ?_, ?_⟩
      · exact (intCast_zmod_four_eq_fin_iff_emod p.1 1).mp ha
      · have hb0 := (intCast_zmod_four_eq_fin_iff_emod p.2 0).mp hb
        calc
          p.2 % 2 = (p.2 % 4) % 2 :=
            (Int.emod_emod_of_dvd p.2 (by norm_num : (2 : ℤ) ∣ 4)).symm
          _ = 0 := by rw [hb0]; norm_num
  | inr p =>
      have hp : p ∈ residuePairShell 1 2 n := by
        simpa [signedResiduePairCarrier] using hq
      rcases Finset.mem_filter.mp hp with ⟨hpBox, hnorm, ha, hb⟩
      rw [heckeFactorShell, Finset.mem_filter]
      refine ⟨hpBox, hnorm, ?_, ?_⟩
      · exact (intCast_zmod_four_eq_fin_iff_emod p.1 1).mp ha
      · have hb2 := (intCast_zmod_four_eq_fin_iff_emod p.2 2).mp hb
        calc
          p.2 % 2 = (p.2 % 4) % 2 :=
            (Int.emod_emod_of_dvd p.2 (by norm_num : (2 : ℤ) ∣ 4)).symm
          _ = 0 := by rw [hb2]; norm_num

private theorem signedResiduePairValue_injective_on {n : ℕ}
    {q₁ q₂ : Sum (ℤ × ℤ) (ℤ × ℤ)}
    (hq₁ : q₁ ∈ signedResiduePairCarrier n)
    (hq₂ : q₂ ∈ signedResiduePairCarrier n)
    (h : signedResiduePairValue q₁ = signedResiduePairValue q₂) :
    q₁ = q₂ := by
  cases q₁ with
  | inl p₁ =>
      cases q₂ with
      | inl p₂ => simpa [signedResiduePairValue] using h
      | inr p₂ =>
          have hp₁ : p₁ ∈ residuePairShell 1 0 n := by
            simpa [signedResiduePairCarrier] using hq₁
          have hp₂ : p₂ ∈ residuePairShell 1 2 n := by
            simpa [signedResiduePairCarrier] using hq₂
          have hb0 := (Finset.mem_filter.mp hp₁).2.2.2
          have hb2 := (Finset.mem_filter.mp hp₂).2.2.2
          have hp : p₁ = p₂ := by simpa [signedResiduePairValue] using h
          subst p₂
          have : (0 : ZMod 4) = 2 := hb0.symm.trans hb2
          exfalso
          exact (by decide : (0 : ZMod 4) ≠ 2) this

  | inr p₁ =>
      cases q₂ with
      | inl p₂ =>
          have hp₁ : p₁ ∈ residuePairShell 1 2 n := by
            simpa [signedResiduePairCarrier] using hq₁
          have hp₂ : p₂ ∈ residuePairShell 1 0 n := by
            simpa [signedResiduePairCarrier] using hq₂
          have hb2 := (Finset.mem_filter.mp hp₁).2.2.2
          have hb0 := (Finset.mem_filter.mp hp₂).2.2.2
          have hp : p₁ = p₂ := by simpa [signedResiduePairValue] using h
          subst p₂
          have : (2 : ZMod 4) = 0 := hb2.symm.trans hb0
          exfalso
          exact (by decide : (2 : ZMod 4) ≠ 0) this
      | inr p₂ => simpa [signedResiduePairValue] using h

private theorem signedResiduePairValue_surjective {n : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ heckeFactorShell n) :
    ∃ q ∈ signedResiduePairCarrier n, signedResiduePairValue q = p := by
  rcases Finset.mem_filter.mp hp with ⟨hpBox, hnorm, ha, hbEven⟩
  rcases even_emod_four_cases hbEven with hb0 | hb2
  · refine ⟨Sum.inl p, ?_, rfl⟩
    have hpResidue : p ∈ residuePairShell 1 0 n := by
      rw [residuePairShell, Finset.mem_filter]
      exact ⟨hpBox, hnorm,
      (intCast_zmod_four_eq_fin_iff_emod p.1 1).mpr ha,
      (intCast_zmod_four_eq_fin_iff_emod p.2 0).mpr hb0⟩
    simpa [signedResiduePairCarrier] using hpResidue
  · refine ⟨Sum.inr p, ?_, rfl⟩
    have hpResidue : p ∈ residuePairShell 1 2 n := by
      rw [residuePairShell, Finset.mem_filter]
      exact ⟨hpBox, hnorm,
      (intCast_zmod_four_eq_fin_iff_emod p.1 1).mpr ha,
      (intCast_zmod_four_eq_fin_iff_emod p.2 2).mpr hb2⟩
    simpa [signedResiduePairCarrier] using hpResidue

private theorem signedResiduePairWeight_eq_factorWeight {n : ℕ}
    {q : Sum (ℤ × ℤ) (ℤ × ℤ)} (hq : q ∈ signedResiduePairCarrier n) :
    signedResiduePairWeight q =
      heckeFactorWeight (signedResiduePairValue q) := by
  cases q with
  | inl p =>
      have hp : p ∈ residuePairShell 1 0 n := by
        simpa [signedResiduePairCarrier] using hq
      have hb := (Finset.mem_filter.mp hp).2.2.2
      have hb0 := (intCast_zmod_four_eq_fin_iff_emod p.2 0).mp hb
      simp [signedResiduePairWeight, signedResiduePairValue,
        heckeFactorWeight, evenResidueSign, hb0]
  | inr p =>
      have hp : p ∈ residuePairShell 1 2 n := by
        simpa [signedResiduePairCarrier] using hq
      have hb := (Finset.mem_filter.mp hp).2.2.2
      have hb2 := (intCast_zmod_four_eq_fin_iff_emod p.2 2).mp hb
      simp [signedResiduePairWeight, signedResiduePairValue,
        heckeFactorWeight, evenResidueSign, hb2]

theorem signedResiduePairSum_eq_heckeCoeff (n : ℕ) :
    (∑ p ∈ residuePairShell 1 0 n, p.1) -
        ∑ p ∈ residuePairShell 1 2 n, p.1 = heckeCoeff n := by
  rw [← sum_heckeFactorWeight_eq_heckeCoeff]
  have hcarrier :
      (∑ q ∈ signedResiduePairCarrier n, signedResiduePairWeight q) =
        ∑ p ∈ heckeFactorShell n, heckeFactorWeight p := by
    refine Finset.sum_bij
      (i := fun q (_ : q ∈ signedResiduePairCarrier n) =>
        signedResiduePairValue q) ?_ ?_ ?_ ?_
    · intro q hq
      exact signedResiduePairValue_mem_factorShell hq
    · intro q₁ hq₁ q₂ hq₂ h
      exact signedResiduePairValue_injective_on hq₁ hq₂ h
    · intro p hp
      obtain ⟨q, hq, hqp⟩ := signedResiduePairValue_surjective hp
      exact ⟨q, hq, hqp⟩
    · intro q hq
      exact signedResiduePairWeight_eq_factorWeight hq
  rw [← hcarrier]
  simp [signedResiduePairCarrier, signedResiduePairWeight,
    Finset.sum_disjSum, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- **THE SECOND FACTOR IS EXACTLY THE HECKE COEFFICIENT STREAM.** -/
theorem coeff_weighted_mul_evenDifference_eq_heckeCoeff (n : ℕ) :
    PowerSeries.coeff n
        (weightedQuarterSquareTheta 1 *
          (quarterSquareTheta 0 - quarterSquareTheta 2)) =
      heckeCoeff n := by
  rw [coeff_weighted_mul_evenDifference,
    signedResiduePairSum_eq_heckeCoeff]

theorem weighted_mul_evenDifference_eq_heckeCoefficientSeries :
    weightedQuarterSquareTheta 1 *
        (quarterSquareTheta 0 - quarterSquareTheta 2) =
      heckeCoefficientSeries := by
  apply PowerSeries.ext
  intro n
  simp [coeff_weighted_mul_evenDifference_eq_heckeCoeff]

#print axioms heckeFactorShellEquiv
#print axioms sum_heckeFactorWeight_eq_heckeCoeff
#print axioms heckeFactorShellTheta_eq_heckeCoefficientSeries
#print axioms coeff_weighted_mul_quarter_eq_splitSum
#print axioms squareSplitEquivResiduePair
#print axioms coeff_weighted_mul_quarter_eq_residuePairSum
#print axioms coeff_weighted_mul_evenDifference
#print axioms signedResiduePairSum_eq_heckeCoeff
#print axioms weighted_mul_evenDifference_eq_heckeCoefficientSeries

end Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor
