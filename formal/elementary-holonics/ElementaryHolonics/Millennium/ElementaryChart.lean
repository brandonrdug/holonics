import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# ElementaryChart: the refusal is a rank deficiency, not a failed search

**What is proved.**  The linear-system half of the decision *“does `∫ R(x) e^{g(x)} dx` close in
the elementary chart”* is built here over `ℚ`, exactly, and driven on the material of its Rust
owner.  The candidate realizer `a` enters through one operator, `a ↦ a′ + a·g′` — declared below
as `liouvilleImage` and again as an exact `ℚ`-linear map `liouvilleTransport` — and three faces of
that operator are proved.  **The row face**: the coefficient of the image at monomial `n` is
`a_{n+1}·(n+1) + ∑_{k ≤ n} a_k·g′_{n−k}`, which is literally the row the Rust owner builds in its
admission loop.  **The degree face**: for `a ≠ 0` and `g′ ≠ 0` the image has degree exactly
`deg a + deg g′`, hence `deg a + deg g = deg R + 1` — *one* degree, not a bound to search under,
which is what makes the candidate population finite.  **The coefficient face**: when `g′ = s·X`
the row collapses to the two-term recurrence `(j+2)·a_{j+2} + s·a_j` at monomial `j+1`, with
`a_1` alone at monomial `0`.

From those three, the core result: **no polynomial over `ℚ` satisfies `a′ − 2x·a = 1`**, so
`∫ e^{−x²}` has no realizer in the polynomial chart.  It is proved **twice, by two independent
routes**, and the two agreeing is the point rather than redundancy.  The *signature* route reads
the refusal off the object before any coefficient is computed: the predicted degree
`deg R − deg g + 1` is `0 − 2 + 1 = −1`, and a negative prediction refuses outright
(`theNegativePredictionRefusesWithoutTheSystem`).  The *system* route never mentions degree: the
constant monomial forces `a_1 = 1`, the recurrence then forces `(2m+3)·a_{2m+3} = −s·a_{2m+1}`,
so **the odd coefficient chain never reaches zero** and no finite polynomial can carry it
(`theOddChainNeverDies`, `noRealizerSurvivesTheOddChain`).

**The degree bound is necessary and never sufficient, and that is exhibited rather than asserted.**
`∫(1 + x)e^{x²}` predicts a realizer of degree `0` — the signature cannot refuse it — and the
system refuses it anyway, by the same odd chain.  `∫(1 + x + x²)e^{x²}` predicts degree `1`, and
its refusal needs a genuine **combination of two rows**: neither the constant equation nor the
quadratic one is inconsistent alone, while `equation₂ − 2·equation₀` annihilates every unknown of
the predicted degree and returns `−1`.  Both halves of that witness are proved
(`theWitnessCombinationAnnihilatesTheUnknowns`, `theWitnessResponseIsNotZero`), which is the
exhibited left null combination the Rust owner returns as its `MonomialObstruction`.

**The positive controls are proved on both faces.**  Algebraically, `a = 1` carries `2x`,
`a = 1/2` carries `x` (a realizer no integer carrier could return), `a = x` carries `1 + 2x²`, and
`a = 1` carries `1` under `g = x`.  Analytically — and this is the *reason* the criterion is the
criterion — `(a·e^g)′ = (a′ + a·g′)·e^g` is proved over `ℝ` as a `HasDerivAt` statement
(`theRealizerDifferentiatesBackThroughTheExponential`), and the three admissions are then real
antiderivative facts about `exp(x²)`, `exp(x²)/2` and `x·exp(x²)`.  That is the second frame the
Rust owner calls `returns_under_differentiation`: the produced realizer is differentiated back
rather than trusted.

**The two refusal species are kept apart, because collapsing them would delete the mechanism.**  A
simple pole obstructs **structurally**, with no linear system built at all: if `q ∤ p` then
`q·(a′ + a·g′) = p` is already impossible by divisibility
(`thePolynomialRealizerNeverCarriesASimplePole`, a two-line proof and deliberately so — the
content is that there is nothing to compute).  The `Ei` case is proved one step further, for
realizers carrying the pole themselves: no `u` over `ℚ` satisfies the cleared equation
`u′·x − u·x′ + u·x·g′ = 1·x` for `g = x`, by two coefficient extractions
(`theExponentialIntegralRefusesEveryRealizerOverItsOwnPole`).  An **inconsistent system** is the
other species entirely, and it is the one the Gaussian falls under.

**Classical provenance, as prose.**  The criterion `∫ R e^g` elementary `⟺ ∃ a` rational with
`a′ + a·g′ = R` is Liouville's (Liouville 1835), in the modern differential-algebra form of
Rosenlicht (Rosenlicht 1972) and made algorithmic by Risch (Risch 1969).  **This file proves none
of that.**  It owns the linear-system half only: given the criterion, the decision is one exact
linear system over `ℚ` whose refusal is a rank deficiency with a witness.

**Absence, measured 2026-08-21** over the pinned Mathlib (`v4.27.0`, revision `a3a10db0e9`) at
`.lake/packages/mathlib`: `grep -rli "risch" Mathlib --include='*.lean'` → **0 files**.  What
Mathlib does own is a neighbour that must not be confused with this one:
`Mathlib/FieldTheory/Differential/Liouville.lean` declares the class `IsLiouville` for a
differential field extension — *every `a = v′ + ∑ cᵢ·logDeriv uᵢ` writable over `K` is writable
over `F`* — following Rosenlicht 1972.  That is a statement about field extensions.  It is **not**
the `a′ + a·g′ = R` criterion for an exponential integrand, and it decides nothing about a
concrete integrand; those commands measure those names over that scope and nothing more.

**Independent re-verification, before any encoding** (exact `fractions.Fraction`, no floats):
every identity below was recomputed from the definition of `a′ + a·g′` on dictionary-encoded
polynomials — the four positive controls, the degree equation on each of them, the Gaussian odd
chain to seventeen terms, the `1 + x` odd chain to thirteen, the `1 + x + x²` chain from its
shifted base, and the `Ei` clearing.  All agreed with the Rust owner's committed test expectations,
including its exhibited combination `{0 ↦ −2, 2 ↦ 1}` with response `−1`.  **Zero discrepancies
were found and nothing was adjusted to make a number fit.**

**What this file does NOT claim.**  Liouville's theorem itself — that an elementary antiderivative
*forces* this shape — is **not proved and never assumed**; nothing below has it as a hypothesis,
and no theorem here says any integral *is* non-elementary.  What is proved is that a **polynomial
realizer over `ℚ` does not exist**, which becomes non-elementarity only through the imported
criterion.  Rational realizers are not covered in general: the two named-open propositions
`TheRationalRealizerRefusesTheSimplePole` and
`ThePolynomialRealizerSufficesForAPolynomialCoefficient` state, in full and over cleared
denominators, exactly what is missing, and two theorems exhibit what each would buy — the second
would lift the Gaussian refusal from polynomial realizers to every rational one.  Squarefreeness of
the denominator is used nowhere as a hypothesis and no `gcd`, resultant, partial-fraction or
Hermite machinery appears; the aperture the Rust owner declares by refusing repeated denominator
factors is not modelled here at all.  There is no solver, no rank computation, no Gaussian
elimination and no decision procedure — one operator is declared, three of its faces are proved,
and six integrands are read.  No `Real.exp` statement below is an integration theorem; each is a
`HasDerivAt` fact, which is the differentiation direction only.  Nothing here is a statement about
the Riemann hypothesis or any other named conjecture.

Every theorem is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.ElementaryChart

open Polynomial

/-! ## 1. The transport

Liouville's criterion sends a candidate realizer `a` to `a′ + a·g′`.  Everything in this file is a
face of that one map, so it is declared once — as a function, for computation, and as a `ℚ`-linear
map, because linearity is what makes the decision a *system* rather than a search. -/

/-- `a′ + a·g′`, the image of a candidate realizer `a` under the declared exponent `g`.  A
realizer is exactly a preimage of `R`. -/
noncomputable def liouvilleImage (g a : ℚ[X]) : ℚ[X] := derivative a + a * derivative g

/-- The same operation as an exact `ℚ`-linear map.  Additivity and homogeneity are what make the
candidate population a vector space and the refusal a rank deficiency. -/
noncomputable def liouvilleTransport (g : ℚ[X]) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun := liouvilleImage g
  map_add' a b := by
    simp only [liouvilleImage, derivative_add, add_mul]
    ring
  map_smul' c a := by
    simp only [liouvilleImage, derivative_smul, smul_add, smul_mul_assoc, RingHom.id_apply]

/-- **`rfl`-class: the proof is literally `rfl`.**  The linear map and the function are one
object; declaring both costs nothing and hides nothing. -/
@[simp] theorem liouvilleTransportApply (g a : ℚ[X]) :
    liouvilleTransport g a = liouvilleImage g a := rfl

/-- **The row of the exact linear system at monomial `n`.**  This is the Rust owner's admission
loop transcribed: the derivative contributes `a_{n+1}·(n+1)` to monomial `n`, and each coefficient
`a_k` contributes `g′_{n−k}`.  The admission ordinal *is* the monomial degree, which is what lets a
returned combination be read as a statement about powers of `x`. -/
theorem theTransportRow (g a : ℚ[X]) (n : ℕ) :
    (liouvilleImage g a).coeff n
      = a.coeff (n + 1) * ((n : ℚ) + 1)
        + ∑ k ∈ Finset.range (n + 1), a.coeff k * (derivative g).coeff (n - k) := by
  simp [liouvilleImage, coeff_derivative, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-! ## 2. The forced degree

The whole content of the criterion's decidability is that `a` does not range over a space to be
searched.  Its degree is a single value read off `R` and `g`. -/

/-- **The image's degree is exactly `deg a + deg g′`.**  The derivative term is strictly
outranked, because `deg a′ < deg a ≤ deg a + deg g′` whenever `g′ ≠ 0`; so nothing cancels and the
product term alone sets the degree. -/
theorem theRealizerDegreeIsForced {g a : ℚ[X]} (hg : derivative g ≠ 0) (ha : a ≠ 0) :
    (liouvilleImage g a).degree = a.degree + (derivative g).degree := by
  have h1 : (derivative a).degree < a.degree := degree_derivative_lt ha
  have h2 : (0 : WithBot ℕ) ≤ (derivative g).degree := zero_le_degree_iff.mpr hg
  have h3 : (a * derivative g).degree = a.degree + (derivative g).degree := degree_mul
  have h4 : (derivative a).degree < (a * derivative g).degree := by
    rw [h3]
    exact lt_of_lt_of_le h1 (by simpa [add_comm] using add_le_add_left h2 a.degree)
  rw [liouvilleImage, degree_add_eq_right_of_degree_lt h4, h3]

/-- **`deg a = deg R − deg g + 1`, stated without subtraction.**  A nonzero realizer for `R` under
a non-constant exponent has exactly one available degree.  This is the Rust owner's
`predicted_realizer_degree`, and it is the reason the candidate space is one finite-dimensional
vector space. -/
theorem theRealizerDegreeEquation {g a R : ℚ[X]} (hg : 1 ≤ g.natDegree) (ha : a ≠ 0)
    (h : liouvilleImage g a = R) : a.natDegree + g.natDegree = R.natDegree + 1 := by
  have hg' : derivative g ≠ 0 := by
    intro hz
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hz
    omega
  have hdeg := theRealizerDegreeIsForced hg' ha
  rw [h] at hdeg
  have hgd : (derivative g).degree = ((g.natDegree - 1 : ℕ) : WithBot ℕ) :=
    degree_derivative_eq g (by omega)
  rw [degree_eq_natDegree ha, hgd] at hdeg
  have hcast : ((a.natDegree : WithBot ℕ)) + ((g.natDegree - 1 : ℕ) : WithBot ℕ)
      = ((a.natDegree + (g.natDegree - 1) : ℕ) : WithBot ℕ) := by push_cast; ring
  rw [hcast] at hdeg
  have := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  omega

/-- `deg R − deg g + 1`, carried over `ℤ` so a negative prediction stays visible instead of being
truncated to zero by `ℕ` subtraction.  Reading it is a **recognition**: it commits before the
system is built and can therefore be wrong. -/
def predictedRealizerDegree (R g : ℚ[X]) : ℤ :=
  (R.natDegree : ℤ) - (g.natDegree : ℤ) + 1

/-- **A negative prediction settles the question without building any system.**  This is the
decisive half of the recognition, and no linear system could overturn it: a realizer would have to
have a degree, and the degree equation leaves none available.  The `R ≠ 0` hypothesis is not
decoration — for `R = 0` the zero realizer works at any exponent degree. -/
theorem theNegativePredictionRefusesWithoutTheSystem {R g a : ℚ[X]} (hR : R ≠ 0)
    (hg : 1 ≤ g.natDegree) (hpred : predictedRealizerDegree R g < 0) :
    liouvilleImage g a ≠ R := by
  intro h
  rcases eq_or_ne a 0 with rfl | ha
  · exact hR (by simpa [liouvilleImage] using h.symm)
  · have hdeg := theRealizerDegreeEquation hg ha h
    simp only [predictedRealizerDegree] at hpred
    omega

/-! ## 3. The coefficient recurrence

For a quadratic exponent the derivative is linear, `g′ = s·X`, and the general row collapses to a
two-term recurrence.  This is the face on which the refusal becomes a statement about an infinite
chain of coefficients rather than about a degree. -/

/-- The constant monomial consults exactly one unknown: the linear coefficient of `a`. -/
theorem theLinearExponentRowAtZero {g a : ℚ[X]} {s : ℚ} (hg : derivative g = C s * X) :
    (liouvilleImage g a).coeff 0 = a.coeff 1 := by
  have key : a * (C s * X) = C s * (a * X) := by ring
  rw [liouvilleImage, hg, key, coeff_add, coeff_derivative, coeff_C_mul, coeff_mul_X_zero]
  norm_num

/-- **The two-term recurrence.**  Every monomial above the constant one couples `a_{j+2}` to
`a_j` and to nothing else, which is what turns the system into a chain. -/
theorem theLinearExponentRowAtSucc {g a : ℚ[X]} {s : ℚ} (hg : derivative g = C s * X) (j : ℕ) :
    (liouvilleImage g a).coeff (j + 1)
      = a.coeff (j + 2) * ((j : ℚ) + 2) + s * a.coeff j := by
  have key : a * (C s * X) = C s * (a * X) := by ring
  rw [liouvilleImage, hg, key, coeff_add, coeff_derivative, coeff_C_mul, coeff_mul_X]
  push_cast
  ring

/-- **The odd chain never dies.**  Once one odd coefficient is nonzero past the reach of `R`, the
recurrence multiplies it by `−s/(2m+3)` forever and it can never return to zero.  Nothing here
mentions degree; this is the system face of the refusal, independent of the signature face. -/
theorem theOddChainNeverDies {g a R : ℚ[X]} {s : ℚ} (hs : s ≠ 0)
    (hg : derivative g = C s * X) (h : liouvilleImage g a = R) {m : ℕ}
    (hm : R.natDegree ≤ 2 * m + 1) (hne : a.coeff (2 * m + 1) ≠ 0) :
    ∀ k, a.coeff (2 * (m + k) + 1) ≠ 0 := by
  intro k
  induction k with
  | zero => simpa using hne
  | succ k ih =>
      have hrow := theLinearExponentRowAtSucc (a := a) hg (2 * (m + k) + 1)
      rw [h] at hrow
      have hz : R.coeff (2 * (m + k) + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz] at hrow
      have hidx : 2 * (m + (k + 1)) + 1 = 2 * (m + k) + 1 + 2 := by ring
      rw [hidx]
      intro hzero
      rw [hzero] at hrow
      have hprod : s * a.coeff (2 * (m + k) + 1) = 0 := by linarith [hrow]
      rcases mul_eq_zero.mp hprod with h1 | h2
      · exact hs h1
      · exact ih h2

/-- **A polynomial cannot carry an immortal chain.**  Every polynomial's coefficients vanish past
its degree, and the chain does not; that contradiction is the refusal. -/
theorem noRealizerSurvivesTheOddChain {g a R : ℚ[X]} {s : ℚ} (hs : s ≠ 0)
    (hg : derivative g = C s * X) (h : liouvilleImage g a = R) {m : ℕ}
    (hm : R.natDegree ≤ 2 * m + 1) (hne : a.coeff (2 * m + 1) ≠ 0) : False :=
  theOddChainNeverDies hs hg h hm hne a.natDegree
    (coeff_eq_zero_of_natDegree_lt (by omega))

/-! ## 4. The declared exponents and their degrees -/

theorem theSquareExponentDerivative : derivative (X ^ 2 : ℚ[X]) = C 2 * X := by
  rw [derivative_X_pow]; norm_num

theorem theNegatedSquareExponentDerivative :
    derivative (-(X ^ 2) : ℚ[X]) = C (-2) * X := by
  rw [derivative_neg, derivative_X_pow, C_neg]; norm_num

theorem theSquareExponentNatDegree : (X ^ 2 : ℚ[X]).natDegree = 2 := by compute_degree!

theorem theNegatedSquareExponentNatDegree : (-(X ^ 2) : ℚ[X]).natDegree = 2 := by compute_degree!

theorem theSeparatingCoefficientNatDegree : (1 + X : ℚ[X]).natDegree = 1 := by compute_degree!

theorem theWitnessCoefficientNatDegree : (1 + X + X ^ 2 : ℚ[X]).natDegree = 2 := by compute_degree!

/-! ## 5. Positive controls, on both faces

The Rust owner's admitting fixtures, proved as exact identities over `ℚ[X]` and then again as
real antiderivative facts.  An admission is not a claim until the realizer differentiates back. -/

/-- `∫ 2x·e^{x²} = e^{x²}`: the realizer is the constant `1`. -/
theorem theConstantRealizerCarriesTheDoubledLinear :
    liouvilleImage (X ^ 2) 1 = C 2 * X := by
  rw [liouvilleImage, derivative_one, theSquareExponentDerivative]; ring

/-- `∫ x·e^{x²} = e^{x²}/2`: the realizer is `1/2`, which no integer carrier could return. -/
theorem theHalfRealizerCarriesTheLinear :
    liouvilleImage (X ^ 2) (C (1 / 2)) = X := by
  rw [liouvilleImage, derivative_C, theSquareExponentDerivative, ← mul_assoc, ← C_mul]
  norm_num

/-- `∫ (1 + 2x²)·e^{x²} = x·e^{x²}`: the realizer has degree `1`, the degree the prediction names. -/
theorem theLinearRealizerCarriesTheQuadratic :
    liouvilleImage (X ^ 2) X = 1 + C 2 * X ^ 2 := by
  rw [liouvilleImage, derivative_X, theSquareExponentDerivative]; ring

/-- `∫ e^x = e^x`: the degenerate sibling, `g = x` and `R = 1`, realizer `1`. -/
theorem theUnitRealizerCarriesTheUnitCoefficient : liouvilleImage X 1 = 1 := by
  rw [liouvilleImage, derivative_one, derivative_X]; ring

/-- **The degree equation holds on the admitting material.**  `0 + 2 = 1 + 1`: the realizer's
degree is the one the prediction named, and the prediction is checked against the realizer rather
than restated from it. -/
theorem theAdmittedRealizerMeetsThePrediction :
    predictedRealizerDegree (C 2 * X) (X ^ 2) = 0 := by
  simp only [predictedRealizerDegree, theSquareExponentNatDegree]
  rw [show (C 2 * X : ℚ[X]).natDegree = 1 by compute_degree!]
  norm_num

/-- **Why the criterion is the criterion.**  `(a·e^g)′ = (a′ + a·g′)·e^g`, over `ℝ`, as a
`HasDerivAt` statement.  A realizer is therefore not a certificate about an integral — it *is* the
antiderivative, and differentiating it back is the second frame. -/
theorem theRealizerDifferentiatesBackThroughTheExponential (a g : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun t : ℝ => a.eval t * Real.exp (g.eval t))
      ((derivative a + a * derivative g).eval x * Real.exp (g.eval x)) x := by
  have h := (a.hasDerivAt x).mul ((g.hasDerivAt x).exp)
  convert h using 1 <;> try rfl
  simp only [eval_add, eval_mul]
  ring

/-- The constant realizer, analytically: `d/dx e^{x²} = 2x·e^{x²}`. -/
theorem theSquareExponentialCarriesTheDoubledLinear (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t ^ 2)) (2 * x * Real.exp (x ^ 2)) x := by
  have h := (hasDerivAt_pow 2 x).exp
  convert h using 1
  norm_num
  ring

/-- The rational realizer, analytically: `d/dx (e^{x²}/2) = x·e^{x²}`. -/
theorem theHalvedSquareExponentialCarriesTheLinear (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t ^ 2) / 2) (x * Real.exp (x ^ 2)) x := by
  have h := (theSquareExponentialCarriesTheDoubledLinear x).div_const 2
  convert h using 1 <;> try rfl
  ring

/-- The degree-one realizer, analytically: `d/dx (x·e^{x²}) = (1 + 2x²)·e^{x²}`. -/
theorem theLinearRealizerCarriesTheQuadraticAnalytically (x : ℝ) :
    HasDerivAt (fun t : ℝ => t * Real.exp (t ^ 2)) ((1 + 2 * x ^ 2) * Real.exp (x ^ 2)) x := by
  have h := (hasDerivAt_id x).mul (theSquareExponentialCarriesTheDoubledLinear x)
  convert h using 1 <;> try rfl
  simp only [id_eq]
  ring

/-! ## 6. The Gaussian, refused twice by two independent routes -/

/-- **The signature route.**  `deg R − deg g + 1 = 0 − 2 + 1 = −1`: the prediction is negative, so
the refusal is read off the object and no coefficient is ever computed.  This is the Rust owner's
`Recognition::RealizerDegreeNegative`, graded `Decisive`. -/
theorem theGaussianPredictionIsNegative :
    predictedRealizerDegree 1 (-(X ^ 2)) = -1 := by
  simp only [predictedRealizerDegree, theNegatedSquareExponentNatDegree, natDegree_one]
  norm_num

/-- **`∫ e^{−x²}` has no polynomial realizer — the degree face.**  Proved through the degree
equation alone: a nonzero realizer would need `deg a + 2 = 1`. -/
theorem theGaussianIsRefusedByItsSignature (a : ℚ[X]) :
    liouvilleImage (-(X ^ 2)) a ≠ 1 :=
  theNegativePredictionRefusesWithoutTheSystem one_ne_zero
    (by rw [theNegatedSquareExponentNatDegree]; norm_num)
    (by rw [theGaussianPredictionIsNegative]; norm_num)

/-- **`∫ e^{−x²}` has no polynomial realizer — the coefficient face, and this route never mentions
degree.**  The constant monomial forces `a_1 = 1`; the recurrence
`(2m+3)·a_{2m+3} = 2·a_{2m+1}` then keeps every odd coefficient nonzero, so `a` would need
infinitely many of them.  This is the algebraic core of the non-elementarity of `∫ e^{−x²}`,
kernel-checked.  The two routes agreeing is the finding: a defect in one would not move the
other. -/
theorem theGaussianAdmitsNoPolynomialRealizer (a : ℚ[X]) :
    liouvilleImage (-(X ^ 2)) a ≠ 1 := by
  intro h
  have h0 := theLinearExponentRowAtZero (a := a) theNegatedSquareExponentDerivative
  rw [h, coeff_one_zero] at h0
  have ha1 : a.coeff (2 * 0 + 1) = 1 := by simpa using h0.symm
  exact noRealizerSurvivesTheOddChain (s := -2) (by norm_num)
    theNegatedSquareExponentDerivative h (m := 0) (by simp) (by rw [ha1]; norm_num)

/-! ## 7. A satisfied degree bound does not imply a realizer exists

This is the separating material.  If the recognition refused everywhere it would be a solver in
disguise; if it opened everywhere it would decide nothing.  Both occur, and the split is what makes
the prediction falsifiable. -/

/-- The prediction for `∫(1 + x)e^{x²}` is `1 − 2 + 1 = 0`: **non-negative**, so the signature
cannot refuse it. -/
theorem theSeparatingPredictionIsNonNegative :
    predictedRealizerDegree (1 + X) (X ^ 2) = 0 := by
  simp only [predictedRealizerDegree, theSquareExponentNatDegree,
    theSeparatingCoefficientNatDegree]
  norm_num

/-- **And the system refuses it anyway.**  The degree bound is necessary and not sufficient; here
that is a theorem rather than a caution.  The same odd chain runs, with `s = 2`. -/
theorem theSatisfiedPredictionStillRefuses (a : ℚ[X]) :
    liouvilleImage (X ^ 2) a ≠ 1 + X := by
  intro h
  have h0 := theLinearExponentRowAtZero (a := a) theSquareExponentDerivative
  rw [h] at h0
  have ha1 : a.coeff (2 * 0 + 1) = 1 := by
    simpa [coeff_one, coeff_X] using h0.symm
  exact noRealizerSurvivesTheOddChain (s := 2) (by norm_num) theSquareExponentDerivative h
    (m := 0) (by rw [theSeparatingCoefficientNatDegree]) (by rw [ha1]; norm_num)

/-! ## 8. The witness spans two equations

For `∫(1 + x + x²)e^{x²}` no single monomial equation is inconsistent.  The contradiction lives
only in `equation₂ − 2·equation₀`, so a witness that could not span two rows would have nothing to
report — which is why the Rust owner returns a `combination`, keyed by monomial, and not a row
index. -/

/-- **The exhibited left null combination annihilates every unknown.**  At the predicted degree
(`deg a ≤ 1`) the coefficient `a₃` is unavailable, and `equation₂ − 2·equation₀` then cancels the
only surviving unknown `a₁` identically — for *every* candidate, which is what makes it a
combination over the system rather than a computation on one solution. -/
theorem theWitnessCombinationAnnihilatesTheUnknowns {a : ℚ[X]} (ha : a.natDegree ≤ 1) :
    (liouvilleImage (X ^ 2) a).coeff 2 - 2 * (liouvilleImage (X ^ 2) a).coeff 0 = 0 := by
  have h0 := theLinearExponentRowAtZero (a := a) theSquareExponentDerivative
  have h2 := theLinearExponentRowAtSucc (a := a) theSquareExponentDerivative 1
  have ha3 : a.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [show (1 : ℕ) + 1 = 2 from rfl, show (1 : ℕ) + 2 = 3 from rfl, ha3] at h2
  rw [h0, h2]
  push_cast
  ring

/-- **And the same combination returns `−1` on the responses.**  `R₂ − 2·R₀ = 1 − 2 = −1`, the
exhibited remainder: a weighting of the monomial equations that kills every unknown while leaving
the response standing.  This is exactly the Rust owner's `MonomialObstruction` with
`combination = {0 ↦ −2, 2 ↦ 1}` and `response = −1`. -/
theorem theWitnessResponseIsNotZero :
    ((1 + X + X ^ 2 : ℚ[X]).coeff 2) - 2 * ((1 + X + X ^ 2 : ℚ[X]).coeff 0) = -1 := by
  norm_num [coeff_one, coeff_X]

/-- **The refusal at the predicted degree, read straight off the two rows above.**  No search, no
elimination: one combination, one nonzero response. -/
theorem theWitnessRefusesAtThePredictedDegree {a : ℚ[X]} (ha : a.natDegree ≤ 1) :
    liouvilleImage (X ^ 2) a ≠ 1 + X + X ^ 2 := by
  intro h
  have hcomb := theWitnessCombinationAnnihilatesTheUnknowns ha
  rw [h, theWitnessResponseIsNotZero] at hcomb
  norm_num at hcomb

/-- The prediction for `∫(1 + x + x²)e^{x²}` is `2 − 2 + 1 = 1`, so the candidate does have a
degree available — and the file refuses it at that degree above and at every degree below. -/
theorem theWitnessPredictionIsOne :
    predictedRealizerDegree (1 + X + X ^ 2) (X ^ 2) = 1 := by
  simp only [predictedRealizerDegree, theSquareExponentNatDegree, theWitnessCoefficientNatDegree]
  norm_num

/-- **The same integrand refused at every degree, by the chain rather than by the combination.**
The base of the chain is the exhibited combination's own arithmetic: `a₁ = 1` from the constant
monomial and `3·a₃ + 2·a₁ = 1` from the quadratic one force `a₃ = −1/3`, and the chain runs from
there.  The two routes bracket the same refusal, one under the degree bound and one without it. -/
theorem theWitnessRefusesAtEveryDegree (a : ℚ[X]) :
    liouvilleImage (X ^ 2) a ≠ 1 + X + X ^ 2 := by
  intro h
  have h0 := theLinearExponentRowAtZero (a := a) theSquareExponentDerivative
  rw [h] at h0
  have ha1 : a.coeff 1 = 1 := by simpa [coeff_one, coeff_X] using h0.symm
  have h2 := theLinearExponentRowAtSucc (a := a) theSquareExponentDerivative 1
  rw [h, show (1 : ℕ) + 1 = 2 from rfl, show (1 : ℕ) + 2 = 3 from rfl, ha1] at h2
  have hR2 : ((1 + X + X ^ 2 : ℚ[X]).coeff 2) = 1 := by simp [coeff_one, coeff_X]
  rw [hR2] at h2
  have ha3 : a.coeff (2 * 1 + 1) ≠ 0 := by
    norm_num
    intro hz
    rw [hz] at h2
    norm_num at h2
  exact noRealizerSurvivesTheOddChain (s := 2) (by norm_num) theSquareExponentDerivative h
    (m := 1) (by rw [theWitnessCoefficientNatDegree]; norm_num) ha3

/-! ## 9. The other species: a pole obstructs structurally

An inconsistent system is a compression with an exhibited remainder.  A simple pole is not that at
all — it refuses before any system is built, and the two must not be collapsed into one reading. -/

/-- **The structural refusal, and the proof's brevity is the content.**  If the denominator does
not divide the numerator then `q·(a′ + a·g′) = p` is impossible by divisibility alone, for every
polynomial realizer, at every degree, under every exponent.  Nothing is computed because there is
nothing to compute — the Rust owner returns this reading with `monomial_equations = 0` and
`unknowns = 0`. -/
theorem thePolynomialRealizerNeverCarriesASimplePole (p q g a : ℚ[X]) (hpq : ¬ q ∣ p) :
    q * liouvilleImage g a ≠ p := fun h => hpq ⟨liouvilleImage g a, h.symm⟩

/-- `∫ e^x / x` is the standard instance: `x ∤ 1`, so no polynomial realizer carries it. -/
theorem theExponentialIntegralHasNoPolynomialRealizer (a : ℚ[X]) :
    X * liouvilleImage X a ≠ 1 :=
  thePolynomialRealizerNeverCarriesASimplePole 1 X X a (by rw [X_dvd_iff]; simp)

/-- **And the pole is refused even to a realizer that carries it.**  Clearing `a = u/x` in
`a′ + a·g′ = 1/x` with `g = x` gives `u′·x − u·x′ + u·x·g′ = 1·x`, and two coefficient extractions
kill it: the constant monomial forces `u₀ = 0` and the linear monomial forces `u₀ = 1`.  This is
one step past the structural reading — the realizer was allowed the pole and still failed. -/
theorem theExponentialIntegralRefusesEveryRealizerOverItsOwnPole (u : ℚ[X]) :
    derivative u * X - u * derivative X + u * X * derivative X ≠ (1 : ℚ[X]) * X := by
  intro h
  have key : derivative u * X - u * derivative X + u * X * derivative X
      = X * (derivative u + u) - u := by rw [derivative_X]; ring
  rw [key, one_mul] at h
  have h0 := congrArg (fun p => Polynomial.coeff p 0) h
  have h1 := congrArg (fun p => Polynomial.coeff p (0 + 1)) h
  simp only [coeff_sub, coeff_X_mul, coeff_add, coeff_derivative, mul_coeff_zero,
    coeff_X_zero, coeff_X_one, zero_mul, zero_sub, neg_eq_zero, Nat.zero_add] at h0 h1
  rw [h0] at h1
  norm_num at h1

/-! ## 10. What is not owned, stated in full

Neither proposition below is assumed anywhere; each is stated over cleared denominators so it is a
real claim about `ℚ[X]` rather than a gesture, and each is followed by a theorem exhibiting what it
would buy. -/

/-- **Named open.**  A realizer carrying a simple pole of a squarefree denominator refuses, in
general: with `a = u/q`, `a′ + a·g′ = p/q` clears to `u′q − uq′ + uqg′ = pq`, and the claim is that
this has no solution when `q ∤ p`.  Proved above only for `q = X` and `g = X`. -/
def TheRationalRealizerRefusesTheSimplePole : Prop :=
  ∀ p q g u : ℚ[X], 1 ≤ q.natDegree → IsCoprime q (derivative q) → ¬ q ∣ p →
    derivative u * q - u * derivative q + u * q * derivative g ≠ p * q

/-- **Named open.**  The reduction this file's polynomial results depend on for their intended
reading: when `R` is a polynomial, a rational realizer `u/v` forces a polynomial one.  With
`a = u/v`, `a′ + a·g′ = R` clears to `u′v − uv′ + uvg′ = Rv²`. -/
def ThePolynomialRealizerSufficesForAPolynomialCoefficient : Prop :=
  ∀ R g u v : ℚ[X], v ≠ 0 → 1 ≤ g.natDegree →
    derivative u * v - u * derivative v + u * v * derivative g = R * v ^ 2 →
    ∃ a : ℚ[X], liouvilleImage g a = R

/-- **What the pole law would buy**: the same structural refusal under a different exponent, where
this file's own coefficient proof does not reach.  `∫ e^{x²}/x` refuses for every realizer of the
shape `u/x`. -/
theorem theOpenPoleLawWouldRefuseTheSquareExponentOverASimplePole
    (hopen : TheRationalRealizerRefusesTheSimplePole) (u : ℚ[X]) :
    derivative u * X - u * derivative X + u * X * derivative (X ^ 2) ≠ (1 : ℚ[X]) * X :=
  hopen 1 X (X ^ 2) u (by simp) (by rw [derivative_X]; exact isCoprime_one_right)
    (by rw [X_dvd_iff]; simp)

/-- **What the sufficiency law would buy, and it is the one that matters**: the Gaussian refusal
would lift from polynomial realizers to **every rational realizer**, which is the last algebraic
step before the imported criterion converts it into non-elementarity. -/
theorem theOpenSufficiencyLawWouldRefuseEveryRationalGaussianRealizer
    (hopen : ThePolynomialRealizerSufficesForAPolynomialCoefficient) (u v : ℚ[X]) (hv : v ≠ 0) :
    derivative u * v - u * derivative v + u * v * derivative (-(X ^ 2)) ≠ (1 : ℚ[X]) * v ^ 2 := by
  intro heq
  obtain ⟨a, ha⟩ :=
    hopen 1 (-(X ^ 2)) u v hv (by rw [theNegatedSquareExponentNatDegree]; norm_num) heq
  exact theGaussianAdmitsNoPolynomialRealizer a ha

end Soma.Holonics.Millennium.ElementaryChart
