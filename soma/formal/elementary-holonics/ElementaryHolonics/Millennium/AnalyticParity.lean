import ElementaryHolonics.Millennium.UniversalBSD

/-!
# AnalyticParity: the sign forbids analytic rank one

**A theorem of the pose, before any continuation is constructed.**  The completed
functional equation `Λ(2−s) = w·Λ(s)` reflects `Λ` about the center `s = 1`, so `Λ`
is an even function of `s − 1` when `w = +1` and an odd one when `w = −1`.  The
first consequence of evenness is that the derivative at the center vanishes:

* **`theCompletedDerivativeVanishesAtAnEvenSign`** — `w = +1 ⟹ Λ'(1) = 0`.
* **`theCentralDerivativeVanishesAtAnEvenSign`** — the same for `L` itself, once
  the central value vanishes: `w = +1 ∧ L(1) = 0 ⟹ L'(1) = 0`.
* **`theAnalyticRankIsNeverOneAtAnEvenSign`** — so the analytic rank is **never
  exactly one** when the sign is `+1`.  This is the first half of the analytic
  parity law, and it is the half that constrains: at `p ≡ 1, 3 (mod 8)` the
  congruent-number twist cannot have analytic rank one, so under the conjecture it
  cannot have algebraic rank one either.

The transfer from `Λ` to `L` is the reason `Lambda_eq` is stated away from the poles
of `Γ`: the two agree on the ball of radius `1/2` about the center, which is a
neighbourhood, so their derivatives there agree.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.AnalyticParity

open Complex
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.UniversalBSD

variable {W : WeierstrassCurve ℤ} {M : ℕ}

/-! ## 1. The completed derivative at an even sign -/

/-- **THE COMPLETED DERIVATIVE VANISHES AT AN EVEN SIGN**: reflecting `Λ` about the
center and differentiating gives `−Λ'(1) = w·Λ'(1)`, so `w = +1` forces `Λ'(1) = 0`. -/
theorem theCompletedDerivativeVanishesAtAnEvenSign (D : LDatumOn W M)
    (hw : D.sign = 1) : deriv D.Lambda 1 = 0 := by
  have hfun : (fun s : ℂ => D.Lambda (2 - s)) = fun s : ℂ => (D.sign : ℂ) * D.Lambda s :=
    funext D.functional_equation
  -- the reflected function, differentiated by the chain rule
  have hinner : HasDerivAt (fun s : ℂ => 2 - s) (-1) 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).const_sub 2
  have houter : HasDerivAt D.Lambda (deriv D.Lambda (2 - (1 : ℂ))) (2 - (1 : ℂ)) :=
    (D.Lambda_analytic _).hasDerivAt
  have hcomp : HasDerivAt (fun s : ℂ => D.Lambda (2 - s))
      (deriv D.Lambda (2 - (1 : ℂ)) * (-1)) 1 := houter.comp 1 hinner
  have h21 : (2 : ℂ) - 1 = 1 := by ring
  rw [h21] at hcomp
  -- the same function, differentiated through the functional equation
  have hscal : HasDerivAt (fun s : ℂ => D.Lambda (2 - s))
      ((D.sign : ℂ) * deriv D.Lambda 1) 1 := by
    rw [hfun]
    exact (D.Lambda_analytic 1).hasDerivAt.const_mul _
  have huniq := hcomp.unique hscal
  rw [hw] at huniq
  push_cast at huniq
  have h2 : (2 : ℂ) * deriv D.Lambda 1 = 0 := by linear_combination -huniq
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-! ## 2. Transfer to the L-function itself -/

/-- Near the center the completed function is the classical product: the ball of
radius `1/2` about `1` misses every nonpositive integer. -/
lemma lambda_eventuallyEq (D : LDatumOn W M) :
    (fun s => D.Lambda s) =ᶠ[nhds (1 : ℂ)]
      fun s => BirchSwinnertonDyer.completed D.conductor D.L s := by
  refine Filter.eventuallyEq_of_mem
    (s := Metric.ball (1 : ℂ) (1 / 2)) (Metric.ball_mem_nhds _ (by norm_num)) ?_
  intro s hs
  refine D.Lambda_eq s fun m hm => ?_
  rw [Metric.mem_ball, Complex.dist_eq, hm] at hs
  have habs : ‖(-(m : ℂ)) - 1‖ = (m : ℝ) + 1 := by
    rw [show (-(m : ℂ)) - 1 = -(((m + 1 : ℕ) : ℂ)) from by push_cast; ring, norm_neg,
      Complex.norm_natCast]
    push_cast
    ring
  rw [habs] at hs
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- **THE CENTRAL DERIVATIVE VANISHES AT AN EVEN SIGN**: if the sign is `+1` and the
central value vanishes, the central derivative vanishes too. -/
theorem theCentralDerivativeVanishesAtAnEvenSign (D : LDatumOn W M)
    (hw : D.sign = 1) (hL : D.L 1 = 0) : deriv D.L 1 = 0 := by
  set c : ℂ := ((Real.sqrt D.conductor : ℂ) / (2 * Real.pi)) with hc
  have hNpos : (0 : ℝ) < Real.sqrt D.conductor := by
    refine Real.sqrt_pos.mpr ?_
    exact_mod_cast D.conductor_pos
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine div_ne_zero ?_ ?_
    · simpa using (Complex.ofReal_ne_zero.mpr hNpos.ne')
    · have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
  -- the prefactor `h(s) = c^s · Γ(s)`, differentiable and nonzero at the center
  set h : ℂ → ℂ := fun s => c ^ s * Complex.Gamma s with hh
  have hnotpole : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have : ((m : ℂ) + 1) = 0 := by rw [eq_neg_iff_add_eq_zero] at hm; linear_combination hm
    have hre : ((m : ℝ) + 1) = 0 := by exact_mod_cast congrArg Complex.re this
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hGam : DifferentiableAt ℂ Complex.Gamma 1 :=
    Complex.differentiableAt_Gamma 1 hnotpole
  have hcpow : DifferentiableAt ℂ (fun s : ℂ => c ^ s) 1 :=
    (differentiableAt_id (x := (1 : ℂ))).const_cpow (Or.inl hc0)
  have hhd : DifferentiableAt ℂ h 1 := hcpow.mul hGam
  have hh1 : h 1 = c := by
    rw [hh]
    simp [Complex.Gamma_one]
  -- the completed function is `h · L` and its derivative at the center is `c·L'(1)`
  have hprod : (fun s => BirchSwinnertonDyer.completed D.conductor D.L s)
      = fun s => h s * D.L s := by
    funext s
    rw [BirchSwinnertonDyer.completed, hh, hc]
  have hderiv : deriv (fun s => BirchSwinnertonDyer.completed D.conductor D.L s) 1
      = c * deriv D.L 1 := by
    rw [hprod, deriv_fun_mul hhd (D.analytic 1), hL, hh1]
    ring
  have hLam := theCompletedDerivativeVanishesAtAnEvenSign D hw
  rw [(lambda_eventuallyEq D).deriv_eq, hderiv] at hLam
  exact (mul_eq_zero.mp hLam).resolve_left hc0

/-! ## 3. The analytic rank is never one at an even sign -/

/-- **THE ANALYTIC RANK IS NEVER EXACTLY ONE AT AN EVEN SIGN**: the functional
equation reflects `Λ` about the center, so a simple zero is impossible when the sign
is `+1`.  Under the conjecture this forbids algebraic rank one wherever the root
number is even — the even-rank prediction, from the functional equation alone. -/
theorem theAnalyticRankIsNeverOneAtAnEvenSign (D : LDatumOn W M) (hw : D.sign = 1) :
    analyticOrderAt D.L 1 ≠ (1 : ℕ∞) := by
  intro hord
  -- order one means the value vanishes and the derivative does not
  have hL0 : D.L 1 = 0 := by
    by_contra hne
    have : analyticOrderAt D.L 1 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hne)
    rw [hord] at this
    exact absurd this (by decide)
  have hd0 : deriv D.L 1 = 0 := theCentralDerivativeVanishesAtAnEvenSign D hw hL0
  -- but an order-one zero has a nonvanishing derivative
  have hana : AnalyticAt ℂ D.L 1 := D.analytic.analyticAt 1
  have hshift : analyticOrderAt (fun z => D.L z - D.L 1) 1 = (1 : ℕ∞) := by
    simpa [hL0] using hord
  have hkey := hana.analyticOrderAt_deriv_add_one
  rw [hshift] at hkey
  have hzero : analyticOrderAt (deriv D.L) 1 = 0 := by
    revert hkey
    generalize analyticOrderAt (deriv D.L) 1 = t
    cases t with
    | top => intro h; simp at h
    | coe k => intro h; norm_cast at h ⊢; omega
  rw [analyticOrderAt_eq_zero] at hzero
  rcases hzero with hna | hval
  · exact hna hana.deriv
  · exact hval hd0


/-! ## 4. The family reading: the even branches cannot have rank one -/

/-- The root number is `+1` at every prime `p ≡ 1, 3 (mod 8)`. -/
theorem theRootNumberIsEvenOnTheOneAndThreeModEightBranches
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1 ∨ p % 8 = 3) :
    FamilyWitness.rootNumber p = 1 := by
  have hp2 : p ≠ 2 := by rcases hp8 with h | h <;> omega
  have hchi : FamilyDuplication.XP p 2 =
      if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1 :=
    FamilyThetaFE.theFamilySignIsTheSecondSupplement p hp2
  unfold FamilyWitness.rootNumber
  rcases hp8 with h | h
  · have hhalf : (p - 1) / 2 = 2 * ((p - 1) / 8) * 2 := by omega
    rw [hchi, if_pos (by omega), hhalf, pow_mul, pow_mul]
    norm_num
  · have hhalf : (p - 1) / 2 = 2 * ((p - 3) / 8) * 2 + 1 := by omega
    rw [hchi, if_neg (by omega), hhalf, pow_succ, pow_mul, pow_mul]
    norm_num

/-- **THE ANALYTIC RANK IS NEVER ONE AT `p ≡ 1, 3 (mod 8)`**: the second supplement
makes the root number `+1` there, and the functional equation then forbids a simple
zero at the center.  Under the conjecture this is the even-rank prediction on those
branches, and it is derived from the theta functional equation alone. -/
theorem theAnalyticRankIsNeverOneOnTheEvenBranches
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1 ∨ p % 8 = 3) :
    BirchSwinnertonDyer.analyticRank
      (FamilyWitness.theWitnessAtEveryOddPrime p
        (by rcases hp8 with h | h <;> omega)) ≠ (1 : ℕ∞) := by
  have hp2 : p ≠ 2 := by rcases hp8 with h | h <;> omega
  have hw : (ofFamilyDatum (FamilyWitness.theWitnessAtEveryOddPrime p hp2)).sign = 1 :=
    theRootNumberIsEvenOnTheOneAndThreeModEightBranches p hp8
  exact theAnalyticRankIsNeverOneAtAnEvenSign
    (ofFamilyDatum (FamilyWitness.theWitnessAtEveryOddPrime p hp2)) hw

/-- **THE CONJECTURE FORCES EVEN RANK AT `p ≡ 1 (mod 8)`**: the rank is at most two
by the character-free descent and cannot be one by the functional equation, so under
the conjecture it is exactly zero or exactly two — never one. -/
theorem theConjectureForcesEvenRankOnTheOneModEightBranch
    (hBSD : TheBirchSwinnertonDyerRankConjecture)
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1) :
    BirchSwinnertonDyer.AlgebraicRankIs p 0 ∨ BirchSwinnertonDyer.AlgebraicRankIs p 2 := by
  have hp2 : p ≠ 2 := by omega
  have hclause := theFamilyPoseIsAnInstance hBSD p
    (FamilyWitness.theWitnessAtEveryOddPrime p hp2)
  have hne1 : ¬ BirchSwinnertonDyer.AlgebraicRankIs p 1 := by
    intro h1
    exact theAnalyticRankIsNeverOneOnTheEvenBranches p (Or.inl hp8) ((hclause 1).mpr h1)
  have hle : ¬ BirchSwinnertonDyer.AlgebraicRankAtLeast p 3 :=
    FamilyOddDescent.theRankIsAtMostTwoAtEveryOddPrime hp2
  by_cases h1 : BirchSwinnertonDyer.AlgebraicRankAtLeast p 1
  · by_cases h2 : BirchSwinnertonDyer.AlgebraicRankAtLeast p 2
    · exact Or.inr ⟨h2, hle⟩
    · exact absurd ⟨h1, h2⟩ hne1
  · exact Or.inl ⟨⟨fun i => i.elim0, fun c _ i => i.elim0⟩, h1⟩

end Soma.Holonics.Millennium.AnalyticParity

