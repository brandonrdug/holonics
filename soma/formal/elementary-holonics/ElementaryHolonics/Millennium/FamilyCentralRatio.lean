import ElementaryHolonics.Millennium.FamilyRatio

/-!
# FamilyCentralRatio: the exact normalization before Waldspurger--Tunnell

This file removes the completed- versus uncompleted-`L` normalization from the
remaining central-ratio gate on the branch `p ≡ 3 (mod 8)`.  What remains after
these lemmas is the equality obtained when the integer parameter below is instantiated by the
finite signed ternary-form count; that equality is the genuine Waldspurger--Tunnell input and is
not postulated here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyCentralRatio

open Complex MeasureTheory Real Set
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.FamilyThetaFE
open Soma.Holonics.Millennium.FamilyDuplication

/-- The archimedean factor at the central point of the odd-prime witness. -/
def centralArchimedeanFactor (p : ℕ) : ℂ :=
  (Real.sqrt (32 * p ^ 2) : ℂ) / (2 * Real.pi)

lemma centralArchimedeanFactor_ne_zero {p : ℕ} (hp : 0 < p) :
    centralArchimedeanFactor p ≠ 0 := by
  unfold centralArchimedeanFactor
  apply div_ne_zero
  · exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 32 * p ^ 2)).ne'
  · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)

/-- **THE WITNESS CENTRAL VALUE WITH ITS EXACT COMPLETED NORMALIZATION.**
The completed central value is the plain theta integral, while the witness stores
the uncompleted `L`-function.  At `s = 1` their difference is exactly the displayed
archimedean factor. -/
theorem theWitnessCentralValueHasExactThetaNormalization
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    centralArchimedeanFactor p *
        (FamilyWitness.theWitnessAtEveryOddPrime p hp2).L 1
      = ((∫ t in Ioi (0 : ℝ), thetaP p t : ℝ) : ℂ) := by
  have hproduct := FamilyWitness.theCompletedProductFormulaHoldsAtEveryOddPrime
    p hp2 1 (fun m h => by
      have hre := congrArg Complex.re h
      simp at hre
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)
  have htheta := FamilyRatio.theCentralValueIsThePlainThetaIntegral p hp2
  rw [← htheta]
  have hL : (FamilyWitness.theWitnessAtEveryOddPrime p hp2).L 1 =
      FamilyWitness.pLOdd p hp2 1 := rfl
  rw [hL, ← hproduct]
  simp only [completed, centralArchimedeanFactor, Complex.cpow_one, Complex.Gamma_one, mul_one]
  push_cast
  ring

/-- **THE CENTRAL RATIO IS EXACTLY A THETA-INTEGRAL IDENTITY.**
No analytic statement is assumed: this is a two-way normalization bridge.  It
identifies the precise theorem still required from Waldspurger--Tunnell without
hiding it behind a new predicate. -/
theorem centralRatio_iff_exactThetaIdentity
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (c : ℤ) :
    ((2 : ℂ) * (FamilyWitness.theWitnessAtEveryOddPrime p hp2).L 1
        = ((c ^ 2 : ℤ) : ℂ) * ((realPeriod p : ℝ) : ℂ))
      ↔
    ((2 : ℂ) * ((∫ t in Ioi (0 : ℝ), thetaP p t : ℝ) : ℂ)
        = centralArchimedeanFactor p *
            (((c ^ 2 : ℤ) : ℂ) * ((realPeriod p : ℝ) : ℂ))) := by
  rw [← theWitnessCentralValueHasExactThetaNormalization p hp2]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hA := centralArchimedeanFactor_ne_zero hp
  constructor
  · intro h
    calc
      (2 : ℂ) * (centralArchimedeanFactor p *
          (FamilyWitness.theWitnessAtEveryOddPrime p hp2).L 1)
          = centralArchimedeanFactor p *
              ((2 : ℂ) * (FamilyWitness.theWitnessAtEveryOddPrime p hp2).L 1) := by ring
      _ = centralArchimedeanFactor p *
          (((c ^ 2 : ℤ) : ℂ) * ((realPeriod p : ℝ) : ℂ)) := by rw [h]
  · intro h
    apply (mul_left_cancel₀ hA)
    linear_combination h

/-- The classical root number is `+1` on the branch `p ≡ 3 (mod 8)`. -/
theorem theRootNumberIsPositiveOnTheThreeModEightBranch
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    FamilyWitness.rootNumber p = 1 := by
  have hp2 : p ≠ 2 := by omega
  have hXP := FamilyThetaFE.theFamilySignIsTheSecondSupplement p hp2
  have hodd : Odd ((p - 1) / 2) := ⟨(p - 3) / 4, by omega⟩
  unfold FamilyWitness.rootNumber
  rw [hXP, if_neg (by omega), hodd.neg_one_pow]
  norm_num

/-- **THE POSITIVE-SIGN CENTRAL INTEGRAL FOLDS AT ONE.**
On `p ≡ 3 (mod 8)`, inversion carries `(0,1)` to `(1,∞)` and the weight-two
functional equation has sign `+1`.  Thus the two halves are exactly equal. -/
theorem theCentralThetaIntegralIsTwiceTheTail
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    (∫ t in Ioi (0 : ℝ), thetaP p t)
      = 2 * ∫ t in Ioi (1 : ℝ), thetaP p t := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hconv, _⟩ :=
    FamilyThetaFE.theCompletedLFunctionHasMellinAtEveryOddPrime p hp2 1
  have hEq : Set.EqOn
      (fun t : ℝ => ((t : ℂ) ^ ((1 : ℂ) - 1)) •
        (Complex.ofReal ∘ thetaP p) t)
      (fun t : ℝ => ((thetaP p t : ℝ) : ℂ)) (Ioi 0) := by
    intro t ht
    simp [Complex.cpow_zero]
  have hC : IntegrableOn (fun t : ℝ => ((thetaP p t : ℝ) : ℂ)) (Ioi 0) :=
    hconv.congr_fun hEq measurableSet_Ioi
  have hR : IntegrableOn (thetaP p) (Ioi 0) := by
    exact hC.re
  have hsign :
      ((-1 : ℝ)) ^ ((p - 1) / 2) * ((XP p 2 : ℤ) : ℝ) = 1 := by
    exact_mod_cast theRootNumberIsPositiveOnTheThreeModEightBranch hp8

  let tail : ℝ → ℝ := Set.indicator (Ioi (1 : ℝ)) (thetaP p)
  have hsub := MeasureTheory.integral_comp_rpow_Ioi tail
    (p := (-1 : ℝ)) (by norm_num)
  have hintegrand : Set.EqOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • tail (x ^ (-1 : ℝ)))
      (Set.indicator (Iio (1 : ℝ)) (thetaP p)) (Ioi 0) := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
    have hxneg2 : x ^ ((-1 : ℝ) - 1) = (x ^ (2 : ℕ))⁻¹ := by
      rw [show (-1 : ℝ) - 1 = -((2 : ℕ) : ℝ) from by norm_num,
        Real.rpow_neg hx0.le, Real.rpow_natCast]
    by_cases hx1 : x < 1
    · have hinv1 : 1 < x⁻¹ := (one_lt_inv₀ hx0).mpr hx1
      have hfe := FamilyThetaFE.theFamilyThetaFunctionalEquationAtEveryOddPrime
        p hp2 hx0
      rw [hsign, one_mul] at hfe
      have hfe' : thetaP p x⁻¹ = x ^ 2 * thetaP p x := by
        simpa [one_div] using hfe
      unfold tail
      change (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
          Set.indicator (Ioi (1 : ℝ)) (thetaP p) (x ^ (-1 : ℝ))
        = Set.indicator (Iio (1 : ℝ)) (thetaP p) x
      rw [hxinv, Set.indicator_apply, Set.indicator_apply]
      simp only [Set.mem_Ioi, Set.mem_Iio, hinv1, hx1, if_pos]
      rw [show |(-1 : ℝ)| = 1 from by norm_num, one_mul, hxneg2, hfe']
      rw [smul_eq_mul]
      field_simp [hx0.ne']
    · have hxge : 1 ≤ x := le_of_not_gt hx1
      have hinvle : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hxge
      unfold tail
      change (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
          Set.indicator (Ioi (1 : ℝ)) (thetaP p) (x ^ (-1 : ℝ))
        = Set.indicator (Iio (1 : ℝ)) (thetaP p) x
      rw [hxinv, Set.indicator_apply, Set.indicator_apply]
      simp only [Set.mem_Ioi, Set.mem_Iio, not_lt.mpr hinvle, hx1, if_false]
      simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hintegrand] at hsub
  have hlower :
      (∫ x in Ioo (0 : ℝ) 1, thetaP p x)
        = ∫ x in Ioi (1 : ℝ), thetaP p x := by
    have hleft :
        (∫ x in Ioi (0 : ℝ), Set.indicator (Iio (1 : ℝ)) (thetaP p) x)
          = ∫ x in Ioo (0 : ℝ) 1, thetaP p x := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Iio]
      congr 1
    have hright :
        (∫ y in Ioi (0 : ℝ), tail y)
          = ∫ y in Ioi (1 : ℝ), thetaP p y := by
      unfold tail
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi,
        show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 from by
          ext y
          simp only [Set.mem_inter_iff, Set.mem_Ioi]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨lt_trans zero_lt_one h, h⟩]
    rw [← hleft, ← hright]
    simpa using hsub
  have hsets : Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
    constructor
    · intro ht
      rcases lt_or_ge t 1 with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h, _⟩ | h)
      · exact h
      · linarith
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_left]
    rintro t ⟨_, ht⟩ hge
    exact (not_le.mpr ht) hge
  have hsplit :
      (∫ t in Ioi (0 : ℝ), thetaP p t)
        = (∫ t in Ioo (0 : ℝ) 1, thetaP p t) +
            ∫ t in Ici (1 : ℝ), thetaP p t := by
    rw [hsets]
    exact setIntegral_union hdisj measurableSet_Ici
      (hR.mono_set (by rw [hsets]; exact Set.subset_union_left))
      (hR.mono_set (by rw [hsets]; exact Set.subset_union_right))
  rw [hsplit, hlower, MeasureTheory.integral_Ici_eq_integral_Ioi]
  ring

/-- The explicit absolutely convergent Gaussian lattice sum returned by the theta
tail calculation in `FamilyRatio`. -/
def centralGaussianSum (p : ℕ) [Fact p.Prime] : ℝ :=
  ∑' q : ℤ × ℤ,
    if (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0 then
      (q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ) *
        (Real.exp (-(FamilyRatio.alphaP p *
            ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2))) /
          (FamilyRatio.alphaP p *
            ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)))
    else 0

/-- On the positive-sign branch, the full central theta integral is exactly twice
the explicit Gaussian lattice sum. -/
theorem theCentralThetaIntegralIsTwiceTheExplicitLatticeSum
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    (∫ t in Ioi (0 : ℝ), thetaP p t) = 2 * centralGaussianSum p := by
  rw [theCentralThetaIntegralIsTwiceTheTail hp8,
    FamilyRatio.theTailIntegralIsTheLatticeSum (p := p) (by omega)]
  rfl

/-- **THE COMPLETED CENTRAL VALUE IS AN EXPLICIT GAUSSIAN LATTICE SUM.** -/
theorem theWitnessCentralValueHasExactLatticeSumNormalization
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    centralArchimedeanFactor p *
        (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)).L 1
      = (2 : ℂ) * ((centralGaussianSum p : ℝ) : ℂ) := by
  rw [theWitnessCentralValueHasExactThetaNormalization p (by omega),
    theCentralThetaIntegralIsTwiceTheExplicitLatticeSum hp8]
  norm_num

/-- **THE WALDSPURGER--TUNNELL GATE AS ONE EXPLICIT LATTICE IDENTITY.**
For every integer `c`, the central ratio is equivalent to the displayed Gaussian-sum identity.
Instantiating `c` with the finite signed ternary-form count makes this the desired
Waldspurger--Tunnell gate.  This theorem does not itself identify an arbitrary `c` with that count.
All completed-`L`, Mellin, inversion, root-number, and factor-of-two normalizations have been
discharged. -/
theorem centralRatio_iff_explicitLatticeIdentity
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) (c : ℤ) :
    ((2 : ℂ) * (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)).L 1
        = ((c ^ 2 : ℤ) : ℂ) * ((realPeriod p : ℝ) : ℂ))
      ↔
    ((4 : ℂ) * ((centralGaussianSum p : ℝ) : ℂ)
        = centralArchimedeanFactor p *
            (((c ^ 2 : ℤ) : ℂ) * ((realPeriod p : ℝ) : ℂ))) := by
  rw [centralRatio_iff_exactThetaIdentity (p := p) (by omega) c,
    theCentralThetaIntegralIsTwiceTheExplicitLatticeSum hp8]
  norm_num
  constructor <;> intro h <;> linear_combination h

end Soma.Holonics.Millennium.FamilyCentralRatio
