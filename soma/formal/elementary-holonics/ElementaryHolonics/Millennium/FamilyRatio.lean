import ElementaryHolonics.Millennium.FamilyWitness
import ElementaryHolonics.Millennium.FamilyGenocchi
import ElementaryHolonics.Millennium.LatticeCount
import ElementaryHolonics.Millennium.FamilyPeriod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# FamilyRatio: the rank clause on an infinite family, reduced to a parity

**What the two-body reading buys.**  `L_p(1) ≠ 0` is a magnitude at a point — one
body, nothing to compare against, and the horizon law says magnitudes do not cross a
frame boundary.  The invariant is the **ratio** of the central value to the curve's own
real period, in the same frame, and that ratio is *discrete*: it is the square of an
integer lattice count over two.  Non-vanishing then stops being an estimate and becomes
a statement about the count.

* **`theRankClauseOnTheThreeModEightBranchIsExactlyTheNonvanishing`** — on the whole
  branch `p ≡ 3 (mod 8)` the algebraic rank is already zero family-wise (Genocchi), so
  the entire rank clause of the posed conjecture is *equivalent* to `L_p(1) ≠ 0`.
  Nothing else is left on that family.
* **`LatticeCountDatum`** — the declared ratio law `L(1) : Ω = c² : 2` with `c` **odd**,
  carrying no absolute scale and no transcendental constant.  Same shape as
  `TheLedgerClause`, with the rational exhibited.
* **`theCentralRatioIsTheSquareOfALatticeCount`** — the count's oddness alone forces
  the central value nonzero.
* **`theRankClauseHoldsOnTheThreeModEightBranch`** — the two joined: the BSD rank
  clause on an infinite family of curves, granted the count.

The remaining content is therefore the construction of the count and its parity — a
finite lattice statement — not an analytic lower bound.  Every `theorem` is discharged
and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyRatio

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.BirchSwinnertonDyer

variable {p : ℕ} [Fact p.Prime]

/-- **THE RANK CLAUSE ON THE THREE-MOD-EIGHT BRANCH IS EXACTLY ONE NONVANISHING.**
The algebraic side is already a theorem across that infinite family (Genocchi's law,
`FamilyGenocchi`), so every other face of the clause discharges and what remains is
`L_p(1) ≠ 0` — nothing else. -/
theorem theRankClauseOnTheThreeModEightBranchIsExactlyTheNonvanishing
    (hp8 : p % 8 = 3) :
    TheRankClause p (FamilyWitness.theWitnessAtEveryOddPrime p (by omega))
      ↔ (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)).L 1 ≠ 0 := by
  have hp2 : p ≠ 2 := by omega
  set W := FamilyWitness.theWitnessAtEveryOddPrime p hp2 with hW
  -- the algebraic rank is exactly zero, family-wise
  have hgen : AlgebraicRankIs p 0 :=
    FamilyGenocchi.theGenocchiLawHoldsOnTheThreeModEightBranch hp8
  -- downward monotonicity of "rank at least"
  have hmono : ∀ r : ℕ, 1 ≤ r → AlgebraicRankAtLeast p r → AlgebraicRankAtLeast p 1 := by
    intro r hr hR
    obtain ⟨Pts, hind⟩ := hR
    refine ⟨fun _ => Pts (Fin.castLE hr 0), ?_⟩
    intro c htor i
    set c' : Fin r → ℤ := fun j => if j = Fin.castLE hr 0 then c 0 else 0 with hc'
    have hsum : (∑ j, c' j • Pts j) = c 0 • Pts (Fin.castLE hr 0) := by
      rw [Finset.sum_eq_single (Fin.castLE hr 0)]
      · simp only [hc', if_pos rfl]
      · intro j _ hj
        simp only [hc', if_neg hj]
        exact zero_smul ℤ (Pts j)
      · intro habs
        exact absurd (Finset.mem_univ (Fin.castLE hr 0)) habs
    have htor' : IsTorsion p (∑ j, c' j • Pts j) := by
      rw [hsum]
      simpa using htor
    have h0 := hind c' htor' (Fin.castLE hr 0)
    simp only [hc', if_pos rfl] at h0
    have : i = 0 := Subsingleton.elim i 0
    rw [this]
    exact h0
  -- the algebraic rank pins `r` to zero
  have halg : ∀ r : ℕ, AlgebraicRankIs p r ↔ r = 0 := by
    intro r
    constructor
    · intro hR
      by_contra hne
      have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hne
      exact hgen.2 (hmono r hr1 hR.1)
    · intro hr; rw [hr]; exact hgen
  constructor
  · intro hclause
    have h0 : analyticRank W = (0 : ℕ) := (hclause 0).mpr hgen
    have hord : analyticOrderAt W.L 1 = 0 := by
      simpa [analyticRank] using h0
    rw [analyticOrderAt_eq_zero] at hord
    rcases hord with h | h
    · exact absurd (W.analytic.analyticAt 1) h
    · exact h
  · intro hne r
    have hord : analyticOrderAt W.L 1 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hne)
    have hAR : analyticRank W = (0 : ℕ∞) := by simpa [analyticRank] using hord
    rw [hAR, halg r]
    constructor
    · intro h; exact_mod_cast h.symm
    · intro h; rw [h]; rfl




/-- **The lattice-count datum, as a RATIO.**  No absolute scale and no transcendental
constant: the central value is compared against the curve's own real period, in the
same frame, and what crosses between them is the square of an integer count.  This is
the shape `TheLedgerClause` already uses — value = rational × period — with the
rational exhibited as `c²/2` and `c` **odd**. -/
structure LatticeCountDatum (p : ℕ) (W : LDatum p) where
  /-- The lattice count. -/
  count : ℤ
  /-- Its parity: the count is odd, so it is nonzero without any estimate. -/
  count_odd : Odd count
  /-- The period is not null in this frame.  **Not** a positivity: which side of the
  reflection is called positive is a hand, and the theorem never needs one.  What it
  needs is incidence with the null cone — that the period is a real length at all. -/
  period_ne_null : realPeriod p ≠ 0
  /-- The ratio law: `L(1) : Ω = c² : 2`. -/
  central_ratio : (2 : ℂ) * W.L 1 = ((count ^ 2 : ℤ) : ℂ) * ((realPeriod p : ℝ) : ℂ)

omit [Fact p.Prime] in
/-- **THE CENTRAL RATIO IS THE SQUARE OF THE LATTICE COUNT**, and the count's
ODDNESS forces nonvanishing.  No estimate, no margin, no majorant — a parity. -/
theorem theCentralRatioIsTheSquareOfALatticeCount {W : LDatum p}
    (D : LatticeCountDatum p W) : W.L 1 ≠ 0 := by
  intro h
  have hr := D.central_ratio
  rw [h, mul_zero] at hr
  have hc : D.count ≠ 0 := by
    rcases D.count_odd with ⟨k, hk⟩; omega
  have hc2 : ((D.count ^ 2 : ℤ) : ℂ) ≠ 0 := by
    have := pow_ne_zero 2 hc
    exact_mod_cast this
  have hp0 : ((realPeriod p : ℝ) : ℂ) ≠ 0 := by
    have := D.period_ne_null
    exact_mod_cast this
  exact (mul_ne_zero hc2 hp0) hr.symm

/-- **THE RANK CLAUSE ON THE THREE-MOD-EIGHT BRANCH**, granted the lattice count:
the algebraic side is Genocchi's law family-wise, the analytic side is the odd count,
and the clause closes on an infinite family of curves at once. -/
theorem theRankClauseHoldsOnTheThreeModEightBranch (hp8 : p % 8 = 3)
    (D : LatticeCountDatum p (FamilyWitness.theWitnessAtEveryOddPrime p (by omega))) :
    TheRankClause p (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)) :=
  (theRankClauseOnTheThreeModEightBranchIsExactlyTheNonvanishing hp8).mpr
    (theCentralRatioIsTheSquareOfALatticeCount D)

/-! ## The central value as an integral -/

section Integral
open Real MeasureTheory Set Complex
open Soma.Holonics.Millennium.FamilyThetaFE
open Soma.Holonics.Millennium.FamilyDuplication

/-- **THE CENTRAL VALUE IS THE PLAIN THETA INTEGRAL**, at every odd prime.  The Mellin
transform at the centre of the reflection has exponent zero, so the completed central
value is exactly the integral of the theta over the positive half-line — no weight, no
kernel, just the theta. -/
theorem theCentralValueIsThePlainThetaIntegral (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    lambdaPOdd p hp2 1 = ((∫ t in Ioi (0:ℝ), thetaP p t : ℝ) : ℂ) := by
  obtain ⟨hconv, heval⟩ := theCompletedLFunctionHasMellinAtEveryOddPrime p hp2 1
  have hEq : Set.EqOn (fun t : ℝ => ((t : ℂ) ^ ((1 : ℂ) - 1)) • (Complex.ofReal ∘ thetaP p) t)
      (fun t : ℝ => ((thetaP p t : ℝ) : ℂ)) (Set.Ioi 0) := by
    intro t ht
    simp [Complex.cpow_zero]
  calc lambdaPOdd p hp2 1 = mellin (Complex.ofReal ∘ thetaP p) 1 := heval.symm
    _ = ∫ t in Set.Ioi (0:ℝ), ((thetaP p t : ℝ) : ℂ) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq
    _ = ((∫ t in Set.Ioi (0:ℝ), thetaP p t : ℝ) : ℂ) := integral_ofReal

/-- **EACH LATTICE CLASS CONTRIBUTES AN EXPONENTIAL QUOTIENT.**  The tail integral of a
single Gaussian class is exact: `∫₁^∞ e^{−ct} dt = e^{−c}/c`.  This is the term of the
signed lattice sum the central value is, with `c = α·N` the class's norm times the
decay rate. -/
theorem theClassContributesItsExponentialQuotient {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (1:ℝ), Real.exp (-(c * t)) = Real.exp (-c) / c := by
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u)) 1 hc
  rw [integral_exp_neg_Ioi] at h
  simp only [mul_one] at h
  rw [show (fun t : ℝ => Real.exp (-(c * t))) = (fun t : ℝ => (fun u : ℝ => Real.exp (-u)) (c * t))
    from rfl]
  rw [h, smul_eq_mul]
  field_simp

/-- The decay rate of the family theta: `α_p = π√2/(4p)`. -/
def alphaP (p : ℕ) : ℝ := π * Real.sqrt 2 / (4 * p)

/-- The lattice class term of the family theta, at argument `x`. -/
def latTermP (p : ℕ) [Fact p.Prime] (q : ℤ × ℤ) (x : ℝ) : ℝ :=
  if (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0 then
    (q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ) *
      Real.exp (-(alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) * x))
  else 0

lemma alphaP_pos {p : ℕ} (hp : 0 < p) : 0 < alphaP p := by
  unfold alphaP
  have h1 := Real.pi_pos
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  positivity

/-- **A SURVIVING CLASS HAS ODD FIRST COORDINATE**, hence positive norm: the parity
condition `q₁+q₂ ≡ 1 (mod 4)` with `q₂` even forces `q₁` odd. -/
theorem theSurvivingClassHasPositiveNorm {p : ℕ} [Fact p.Prime] {q : ℤ × ℤ}
    (h : (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0) :
    0 < (q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2 := by
  obtain ⟨h1, h2⟩ := h
  have hq1 : q.1 ≠ 0 := by omega
  have : (0:ℝ) < (q.1 : ℝ) ^ 2 := by
    have : ((q.1 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hq1
    positivity
  nlinarith [sq_nonneg ((q.2 : ℝ))]

/-- **EACH CLASS TERM INTEGRATES TO ITS EXPONENTIAL QUOTIENT**, exactly, at every odd
prime.  This is the term of the signed lattice sum the central value is. -/
theorem theClassTermIntegratesExactly {p : ℕ} [Fact p.Prime] (hp : 0 < p) (q : ℤ × ℤ) :
    ∫ x in Ioi (1:ℝ), latTermP p q x
      = if (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0 then
          (q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ) *
            (Real.exp (-(alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)))
              / (alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)))
        else 0 := by
  by_cases hc : (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0
  · rw [if_pos hc]
    have hN := theSurvivingClassHasPositiveNorm (p := p) hc
    have hcpos : 0 < alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) :=
      mul_pos (alphaP_pos hp) hN
    have hfun : ∀ x ∈ Ioi (1:ℝ), latTermP p q x
        = ((q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ)) *
            Real.exp (-((alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) * x)) := by
      intro x _
      unfold latTermP
      rw [if_pos hc]
    rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul,
      theClassContributesItsExponentialQuotient hcpos]
  · rw [if_neg hc]
    have : ∀ x ∈ Ioi (1:ℝ), latTermP p q x = 0 := by
      intro x _; unfold latTermP; rw [if_neg hc]
    rw [setIntegral_congr_fun measurableSet_Ioi this]
    simp

/-- **EACH CLASS TERM IS INTEGRABLE ON THE TAIL.**  A surviving class decays
exponentially with a strictly positive rate, so the first half of the interchange
hypothesis holds at every class and every odd prime. -/
theorem theClassTermIsIntegrable {p : ℕ} [Fact p.Prime] (hp : 0 < p) (q : ℤ × ℤ) :
    IntegrableOn (latTermP p q) (Ioi (1:ℝ)) := by
  by_cases hc : (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0
  · have hN := theSurvivingClassHasPositiveNorm (p := p) hc
    have hcpos : 0 < alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) :=
      mul_pos (alphaP_pos hp) hN
    have hbase : IntegrableOn
        (fun x : ℝ => Real.exp (-((alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) * x)))
        (Ioi (1:ℝ)) := by simpa [neg_mul] using exp_neg_integrableOn_Ioi 1 hcpos
    have hfun : latTermP p q = fun x =>
        ((q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ)) *
          Real.exp (-((alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) * x)) := by
      funext x; unfold latTermP; rw [if_pos hc]
    rw [hfun]
    exact hbase.const_mul _
  · have hfun : latTermP p q = fun _ => (0:ℝ) := by
      funext x; unfold latTermP; rw [if_neg hc]
    rw [hfun]
    exact integrableOn_zero

/-! ### The Gaussian majorant -/

/-- Over the integers the square dominates the absolute value. -/
theorem theSquareDominatesTheAbsoluteValue (m : ℤ) : |(m : ℝ)| ≤ ((m : ℝ)) ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · norm_num
  · have h1 : (1:ℤ) ≤ |m| := Int.one_le_abs hm
    have h2 : (1:ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast h1
    nlinarith [sq_abs ((m : ℝ)), h2]

/-- **THE ONE-DIMENSIONAL GAUSSIAN LATTICE SERIES CONVERGES**, dominated by a geometric
one because the square dominates the absolute value over the integers. -/
theorem theGaussianLineIsSummable {a : ℝ} (ha : 0 < a) :
    Summable (fun m : ℤ => Real.exp (-(a * ((m : ℝ)) ^ 2))) := by
  have hr : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnat : Summable (fun n : ℕ => Real.exp (-(a * (n : ℝ)))) := by
    have hfun : (fun n : ℕ => Real.exp (-(a * (n : ℝ))))
        = fun n : ℕ => (Real.exp (-a)) ^ n := by
      funext n
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [hfun]
    exact summable_geometric_of_lt_one (Real.exp_nonneg _) hr
  have habs : Summable (fun m : ℤ => Real.exp (-(a * |(m : ℝ)|))) := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · refine hnat.of_nonneg_of_le (fun n => Real.exp_nonneg _) (fun n => ?_)
      push_cast
      rw [abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
    · refine hnat.of_nonneg_of_le (fun n => Real.exp_nonneg _) (fun n => ?_)
      push_cast
      rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  refine habs.of_nonneg_of_le (fun m => Real.exp_nonneg _) (fun m => ?_)
  refine Real.exp_le_exp.mpr ?_
  have := theSquareDominatesTheAbsoluteValue m
  nlinarith [this, ha]



/-- **THE GAUSSIAN LATTICE SERIES CONVERGES.**  The plane series factors as a product of
two line series, each dominated by a geometric one because the square dominates the
absolute value over the integers. -/
theorem theGaussianLatticeIsSummable {a : ℝ} (ha : 0 < a) :
    Summable (fun q : ℤ × ℤ => Real.exp (-(a * (((q.1 : ℝ)) ^ 2 + ((q.2 : ℝ)) ^ 2)))) := by
  have hline := theGaussianLineIsSummable ha
  have hprod : Summable (fun q : ℤ × ℤ =>
      Real.exp (-(a * ((q.1 : ℝ)) ^ 2)) * Real.exp (-(a * ((q.2 : ℝ)) ^ 2))) :=
    hline.mul_of_nonneg hline (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _)
  refine hprod.congr (fun q => ?_)
  rw [← Real.exp_add]
  congr 1
  ring

/-- **THE LINEAR IS DOMINATED BY THE EXPONENTIAL**: `x·e^{−bx} ≤ 1/b` for `x ≥ 0`. -/
theorem theLinearIsDominatedByTheExponential {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    x * Real.exp (-(b * x)) ≤ 1 / b := by
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp; positivity
  · have he : b * x ≤ Real.exp (b * x) := by
      have := Real.add_one_le_exp (b * x)
      linarith
    have hbx : (0:ℝ) < b * x := mul_pos hb hx'
    rw [Real.exp_neg, ← div_eq_mul_inv]
    calc x / Real.exp (b * x) ≤ x / (b * x) := by gcongr
      _ = 1 / b := by field_simp

/-- **THE TAIL INTEGRAL OF A CLASS TERM'S NORM IS ITS EXPONENTIAL QUOTIENT.** -/
theorem theClassNormIntegratesExactly {p : ℕ} [Fact p.Prime] (hp : 0 < p) (q : ℤ × ℤ) :
    ∫ x in Ioi (1:ℝ), ‖latTermP p q x‖
      = if (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0 then
          |(q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ)| *
            (Real.exp (-(alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)))
              / (alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)))
        else 0 := by
  by_cases hc : (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0
  · rw [if_pos hc]
    have hN := theSurvivingClassHasPositiveNorm (p := p) hc
    have hcpos : 0 < alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) := mul_pos (alphaP_pos hp) hN
    have hfun : ∀ x ∈ Ioi (1:ℝ), ‖latTermP p q x‖
        = |(q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ)| *
            Real.exp (-((alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) * x)) := by
      intro x _
      unfold latTermP
      rw [if_pos hc, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul,
      theClassContributesItsExponentialQuotient hcpos]
  · rw [if_neg hc]
    have hz : ∀ x ∈ Ioi (1:ℝ), ‖latTermP p q x‖ = 0 := by
      intro x _; unfold latTermP; rw [if_neg hc]; simp
    rw [setIntegral_congr_fun measurableSet_Ioi hz]
    simp

/-- **THE INTEGRAL NORMS ARE SUMMABLE.**  The exponential quotient's denominator cancels
the numerator's linear factor exactly: `|q₁| ≤ q₁² ≤ N`, so each class contributes at
most `e^{−αN}/α`, and the Gaussian lattice series dominates. -/
theorem theIntegralNormsAreSummable {p : ℕ} [Fact p.Prime] (hp : 0 < p) :
    Summable (fun q : ℤ × ℤ => ∫ x in Ioi (1:ℝ), ‖latTermP p q x‖) := by
  have halpha := alphaP_pos hp
  have hmaj : Summable (fun q : ℤ × ℤ =>
      (1 / alphaP p) * Real.exp (-(alphaP p * (((q.1 : ℝ)) ^ 2 + ((q.2 : ℝ)) ^ 2)))) :=
    (theGaussianLatticeIsSummable halpha).mul_left _
  refine hmaj.of_nonneg_of_le (fun q => ?_) (fun q => ?_)
  · exact setIntegral_nonneg measurableSet_Ioi (fun x _ => norm_nonneg _)
  · rw [theClassNormIntegratesExactly hp q]
    by_cases hc : (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0
    · rw [if_pos hc]
      have hN := theSurvivingClassHasPositiveNorm (p := p) hc
      have hcpos : 0 < alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) := mul_pos halpha hN
      have hchi : |((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ)| ≤ 1 := by
        have := XP_abs_le p (q.1 ^ 2 + q.2 ^ 2)
        exact_mod_cast this
      have hq1 : |(q.1 : ℝ)| ≤ ((q.1 : ℝ)) ^ 2 + ((q.2 : ℝ)) ^ 2 := by
        have := theSquareDominatesTheAbsoluteValue q.1
        nlinarith [sq_nonneg ((q.2 : ℝ))]
      have hnum : |(q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ)|
          ≤ ((q.1 : ℝ)) ^ 2 + ((q.2 : ℝ)) ^ 2 := by
        rw [abs_mul]
        nlinarith [abs_nonneg ((q.1 : ℝ)), abs_nonneg (((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ)),
          hchi, hq1]
      have hexp : (0:ℝ) < Real.exp (-(alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2))) :=
        Real.exp_pos _
      rw [div_eq_mul_inv, ← mul_assoc]
      calc |(q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ)| *
              Real.exp (-(alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2))) *
              (alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2))⁻¹
          ≤ (((q.1 : ℝ)) ^ 2 + ((q.2 : ℝ)) ^ 2) *
              Real.exp (-(alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2))) *
              (alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2))⁻¹ := by
            gcongr
        _ = Real.exp (-(alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2))) * (1 / alphaP p) := by
            field_simp
        _ = (1 / alphaP p) *
              Real.exp (-(alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2))) := by ring
    · rw [if_neg hc]
      positivity

/-- **THE INTERCHANGE IS LAWFUL.**  Each class term is integrable on the tail and the
integral norms are summable against the Gaussian lattice, so the lattice series
integrates term by term over `[1,∞)`. -/
theorem theInterchangeIsLawful {p : ℕ} [Fact p.Prime] (hp : 0 < p) :
    ∑' q : ℤ × ℤ, ∫ x in Ioi (1:ℝ), latTermP p q x
      = ∫ x in Ioi (1:ℝ), ∑' q : ℤ × ℤ, latTermP p q x :=
  integral_tsum_of_summable_integral_norm
    (fun q => theClassTermIsIntegrable hp q) (theIntegralNormsAreSummable hp)

/-- **THE REAL CLASS SUM IS THE THETA.**  The committed complex `HasSum` descends: its
summand is the complex cast of the real class term, and its value the cast of the
theta. -/
theorem theRealClassSumIsTheTheta {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x : ℝ}
    (hx : 0 < x) : HasSum (fun q : ℤ × ℤ => latTermP p q x) (thetaP p x) := by
  have hC := theFamilyThetaIsTheTwistedClassSum p hp2 hx
  rw [← Complex.hasSum_ofReal]
  refine hC.congr_fun ?_
  intro q
  by_cases hc : (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0
  · rw [if_pos hc]
    unfold latTermP
    rw [if_pos hc]
    push_cast
    congr 2
    unfold alphaP
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    field_simp
    push_cast
    ring
  · rw [if_neg hc]
    unfold latTermP
    rw [if_neg hc]
    norm_num

/-- **THE TAIL INTEGRAL IS THE SIGNED LATTICE SUM.**  The theta's tail integral is an
absolutely convergent sum over the Gaussian lattice, one exponential quotient per class,
signed by the quadratic character. -/
theorem theTailIntegralIsTheLatticeSum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∫ x in Ioi (1:ℝ), thetaP p x
      = ∑' q : ℤ × ℤ, (if (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0 then
          (q.1 : ℝ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℝ) *
            (Real.exp (-(alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)))
              / (alphaP p * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)))
        else 0) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hstep : ∀ x ∈ Ioi (1:ℝ), thetaP p x = ∑' q : ℤ × ℤ, latTermP p q x := by
    intro x hx
    exact ((theRealClassSumIsTheTheta hp2 (lt_trans one_pos hx)).tsum_eq).symm
  rw [setIntegral_congr_fun measurableSet_Ioi hstep, ← theInterchangeIsLawful hp]
  exact tsum_congr (fun q => theClassTermIntegratesExactly hp q)

end Integral

/-! ## What the rank clause on the branch still needs -/

section Reduction
open Soma.Holonics.Millennium.LatticeCount

/-- **THE RANK CLAUSE ON THE BRANCH NEEDS ONLY THE RATIO IDENTITY.**  On `p ≡ 3 (mod 8)`
the count's oddness and the period's non-nullity are both theorems, so the whole
Birch–Swinnerton-Dyer rank clause on that infinite family reduces to the single
identity `2·L(1) = c²·Ω` — the Shimura/Waldspurger leg and nothing else. -/
theorem theRankClauseNeedsOnlyTheRatio {p B : ℕ} [Fact p.Prime] (hp : p.Prime)
    (h8 : p % 8 = 3) (hB : p ≤ B) {c : ℤ} (hc : SF p B = 4 * c)
    (hratio : (2 : ℂ) * (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)).L 1
      = ((c ^ 2 : ℤ) : ℂ) * ((realPeriod p : ℝ) : ℂ)) :
    TheRankClause p (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)) := by
  obtain ⟨k, hk⟩ := theCountIsOddOnTheThreeModEightBranch hp h8 hB
  have hcodd : Odd c := by
    refine ⟨k, ?_⟩
    rw [hc] at hk
    omega
  refine theRankClauseHoldsOnTheThreeModEightBranch h8 ?_
  exact
    { count := c
      count_odd := hcodd
      period_ne_null := FamilyPeriod.theRealPeriodIsNotNull hp.pos
      central_ratio := hratio }

end Reduction

end Soma.Holonics.Millennium.FamilyRatio
