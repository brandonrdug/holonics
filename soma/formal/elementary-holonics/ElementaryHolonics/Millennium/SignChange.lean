import Mathlib.Tactic
import ElementaryHolonics.Millennium.Sturm

/-!
# SignChange: what happens to a sign at a root, and what cannot happen away from one

**What is proved.**  The local facts a sign-variation count rests on, over `Polynomial ℝ`,
joined to the rational charts of `ElementaryHolonics.Millennium.Sturm` through their real
evaluation (`Sturm.evalReal`) and through an exact cast of the rational reading into a real one.

* **The root flip.**  At *any* root of a nonzero polynomial the product `p · p'` passes from
  strictly negative to strictly positive, with an exhibited window: the chart factors as
  `(X − r)^(n+1) · q` with `q(r) ≠ 0`, so `p · p' = (X − r)^(2n+1) · h` with `h(r) = (n+1)·q(r)² > 0`,
  and an **odd** power carries the hand.  For a **simple** root the flip is refined to a statement
  the counting instrument can actually consume: on one window `p(x) · p'(r) < 0` below and `> 0`
  above, *and* `p'(x) · p'(r) > 0` throughout, so the pair `(p, p')` is separated on both sides.
  The quotient form is proved as well: `p(x)/(x − r) → p'(r)` along the punctured neighbourhood,
  with no simplicity hypothesis at all.
* **No-root constancy.**  On a closed interval carrying no real root the sign does not move —
  the contrapositive of the intermediate value theorem (Bolzano 1817), via Mathlib's
  `intermediate_value_Ioo`.  Opposite signs at the endpoints are proved to force a root *strictly*
  inside, and root-freeness is proved to force any two points of the interval to share a sign.
* **The corollary the counting shape uses.**  Between two consecutive roots the chart keeps one
  sign; and when the lower root is simple, *which* sign is settled by the derivative there.
* **The pair-level fragment.**  The variation count is re-declared over `ℝ` — Sturm's chain must be
  read at real points inside a window, while `Sturm.variationCount` reads only rational ones — and
  the rational count is proved to cast to the real count exactly.  Then: the pair `(p, p')` carries
  **exactly one** variation just below a simple root and **exactly none** just above it; and an
  interior chain entry vanishing at a point forces its two neighbours to straddle, so the triple
  reads `1` there whatever the entry did.

**The material is Sturm's own.**  The star quartic `X⁴ − 5X² + 4` of
`crates/holonic-engine/src/winding_inertia.rs` — the squarefree part of `D₆(x) − 2`, whose roots are
the star values `β_m = ω^m + ω^{−m}` at `n = 6` — is carried here as a real polynomial, proved to
name the same function as `Sturm.starHexagonChart`, and its chain is exhibited as a division tower
over `ℝ`.  The flip is run at the star value `2`; the constancy corollary is run on the gap between
the star values `1` and `2`; the straddle is run at the origin, where two chain entries go blind
simultaneously.

**Independent re-verification, before any encoding** (exact `fractions.Fraction`, no floats): the
sign of `(p · p')(r ± h)` was recomputed for `X² − 1` at `1`, `X³ − X` at `0`, and
`(X−1)²(X−3)` at `3`, at six separations each down to `h = 10⁻⁶`; every one of the thirty-six
values had the sign the flip predicts.  The straddle products on the star chain at the origin were
recomputed as `−16` and `−16`.  The double-root instance was recomputed too, and it produced a
**correction to the plan rather than a confirmation**: the flip was expected to fail there and it
does not — `p · p' = (X−1)³(X−3)(3X−7)` still passes `−` to `+` across `1`.  That measurement is
what forced the general-multiplicity theorem below to be attempted instead of the simple-root one
alone, and it is recorded as `theFlipDoesNotDetectMultiplicity`.  **No discrepancy was found and
nothing was adjusted to make a number fit.**

**Measured 2026-08-21** over the pinned Mathlib (`v4.27.0`, revision `a3a10db0e9`) at
`.lake/packages/mathlib`: `grep -rli "sturm" Mathlib --include='*.lean'` → **0 files**.  That
command measures that name over that scope and is not a claim that no related content exists under
another name.  What Mathlib does supply, and what is used here rather than rebuilt, is
`intermediate_value_Ioo`, `Polynomial.continuous`, `Polynomial.dvd_iff_isRoot`,
`Polynomial.pow_mul_divByMonic_rootMultiplicity_eq` and `Odd.pow_neg`.

**What this file does NOT claim.**  It **does not discharge**
`Soma.Holonics.Millennium.Sturm.TheReadingEqualsThePopulation`, which remains named open in the file
that states it; nothing here assumes it and nothing here restates it.  What is proved is
strictly local: a window around one root, and an interval carrying none.  The three steps that would
close the counting law are **absent** — that the window decomposition of an interval by the finitely
many roots of the whole chain is exhaustive; that the count is *globally* unchanged across an
interior entry's root (the straddle below is the pointwise fact, not the two-sided comparison); and
that the head's own drop is exactly one *within the chain reading* rather than within the isolated
pair.  No claim is made about the Riemann hypothesis or any other named conjecture; no zeta
function, L-function, curve or variety appears.  Root counting *with* multiplicity is not addressed:
the general flip is deliberately blind to multiplicity, which is exhibited rather than hidden.  No
decision procedure, isolation loop or bisection driver is built.

Every theorem is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.SignChange

open Polynomial

/-! ## 1. A strict sign survives in a window

The one analytic input.  Everything else in the file is algebra plus the intermediate value
theorem. -/

/-- **A strictly positive value survives in an exhibited window.**  Continuity of polynomial
evaluation, converted from a neighbourhood filter into an explicit `δ` so that every later
statement can carry its window rather than a filter. -/
theorem thePositiveValueSurvivesInAWindow {q : Polynomial ℝ} {r : ℝ} (hq : 0 < q.eval r) :
    ∃ δ > 0, ∀ x : ℝ, r - δ < x → x < r + δ → 0 < q.eval x := by
  have hev : ∀ᶠ x in nhds r, 0 < q.eval x :=
    continuousAt_const.eventually_lt q.continuousAt hq
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, h⟩ := hev
  refine ⟨ε, hε, fun x h1 h2 => h ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **A strict sign survives division by a positive factor.**  Used to strip the square of a
derivative value off a product without ever forming a quotient. -/
theorem theStrictSignSurvivesAPositiveFactor {u c : ℝ} (hc : 0 < c) :
    (u * c < 0 ↔ u < 0) ∧ (0 < u * c ↔ 0 < u) := by
  constructor
  · constructor
    · intro h; by_contra hcon; push_neg at hcon; nlinarith
    · intro h; exact mul_neg_of_neg_of_pos h hc
  · constructor
    · intro h; by_contra hcon; push_neg at hcon; nlinarith
    · intro h; exact mul_pos h hc

/-! ## 2. The root flip, at any multiplicity

A nonzero chart factors through its root multiplicity, the product with the derivative factors at
an **odd** power of the root factor, and an odd power carries the hand of its base. -/

/-- **A nonzero chart factors through its root multiplicity**: `p = (X − r)^(n+1) · q` with `q`
not vanishing at `r`.  The exponent is written `n + 1` so that positivity is structural rather
than a side condition. -/
theorem theChartFactorsThroughItsRootMultiplicity {p : Polynomial ℝ} {r : ℝ}
    (hp0 : p ≠ 0) (hp : p.eval r = 0) :
    ∃ (n : ℕ) (q : Polynomial ℝ), p = (X - C r) ^ (n + 1) * q ∧ q.eval r ≠ 0 := by
  have hm : 0 < rootMultiplicity r p := (rootMultiplicity_pos hp0).mpr hp
  refine ⟨rootMultiplicity r p - 1, p /ₘ (X - C r) ^ rootMultiplicity r p, ?_,
    eval_divByMonic_pow_rootMultiplicity_ne_zero r hp0⟩
  rw [Nat.sub_add_cancel hm]
  exact (pow_mul_divByMonic_rootMultiplicity_eq p r).symm

/-- **The product with the derivative factors at an odd power of the root factor.**  From
`p = (X − r)^(n+1)·q` one gets `p·p' = (X − r)^(2n+1)·(C(n+1)·q² + (X − r)·q·q')`.  The exponent
`2n + 1` is odd for every `n`, which is the entire content of the flip: the cofactor is positive at
`r`, so the sign of the product is the sign of `x − r`. -/
theorem theProductWithTheDerivativeFactorsAtAnOddPower {p q : Polynomial ℝ} {r : ℝ} {n : ℕ}
    (hfac : p = (X - C r) ^ (n + 1) * q) :
    p * p.derivative
      = (X - C r) ^ (2 * n + 1)
        * (C ((n : ℝ) + 1) * q ^ 2 + (X - C r) * q * derivative q) := by
  have hd : derivative p
      = C ((n : ℝ) + 1) * (X - C r) ^ n * q + (X - C r) ^ (n + 1) * derivative q := by
    rw [hfac, derivative_mul, derivative_pow, derivative_X_sub_C, Nat.add_sub_cancel]
    push_cast
    ring
  rw [hd, hfac]
  ring

/-- **THE ROOT FLIP.**  At any root of a nonzero chart the product `p · p'` is strictly negative on
an exhibited window below the root and strictly positive on the same window above it.  No
simplicity hypothesis: multiplicity `m` contributes the odd exponent `2m − 1`, and an odd power
never hides a hand.  (Classically this is the observation that `p·p' = ½·(p²)'` and `p²` has a
strict local minimum at every root.) -/
theorem theRootFlipsTheProductWithItsDerivative {p : Polynomial ℝ} {r : ℝ}
    (hp0 : p ≠ 0) (hp : p.eval r = 0) :
    ∃ δ > 0,
      (∀ x : ℝ, r - δ < x → x < r → (p * derivative p).eval x < 0) ∧
      (∀ x : ℝ, r < x → x < r + δ → 0 < (p * derivative p).eval x) := by
  obtain ⟨n, q, hfac, hqr⟩ := theChartFactorsThroughItsRootMultiplicity hp0 hp
  set h : Polynomial ℝ := C ((n : ℝ) + 1) * q ^ 2 + (X - C r) * q * derivative q with hh
  have hhr : 0 < h.eval r := by
    have hq2 : 0 < q.eval r ^ 2 := by positivity
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [hh, eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self, zero_mul]
    nlinarith
  obtain ⟨δ, hδ, hpos⟩ := thePositiveValueSurvivesInAWindow hhr
  have hprod : ∀ x : ℝ, (p * derivative p).eval x = (x - r) ^ (2 * n + 1) * h.eval x := by
    intro x
    rw [theProductWithTheDerivativeFactorsAtAnOddPower hfac]
    simp [hh]
  have hodd : Odd (2 * n + 1) := ⟨n, by ring⟩
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro x h1 h2
    rw [hprod x]
    exact mul_neg_of_neg_of_pos (hodd.pow_neg (by linarith)) (hpos x (by linarith) (by linarith))
  · intro x h1 h2
    rw [hprod x]
    exact mul_pos (pow_pos (by linarith) _) (hpos x (by linarith) (by linarith))

/-! ## 3. The simple root, where the derivative's own sign is available

The general flip above says nothing about `p` itself — at a double root `p` does not change sign at
all.  Under `p'(r) ≠ 0` the chart *does* change sign, and the pair `(p, p')` is separated on both
sides of the root.  That refinement is what a variation count consumes. -/

/-- **A simple root's cofactor is the derivative value.**  `p = (X − r)·q` with `q(r) = p'(r)`;
this is `Polynomial.dvd_iff_isRoot` plus the product rule, and it is where `p'(r)` enters as a
*value of the cofactor* rather than as a limit. -/
theorem theSimpleRootFactorsWithItsDerivativeAsCofactor {p : Polynomial ℝ} {r : ℝ}
    (hp : p.eval r = 0) :
    ∃ q : Polynomial ℝ, p = (X - C r) * q ∧ q.eval r = (derivative p).eval r := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hp
  refine ⟨q, hq, ?_⟩
  have hd : derivative p = q + (X - C r) * derivative q := by
    rw [hq, derivative_mul, derivative_X_sub_C, one_mul]
  rw [hd]
  simp

/-- **The chart over its root factor tends to the derivative value.**  `p(x)/(x − r) → p'(r)` along
the punctured neighbourhood of `r`, for every root, simple or not.  This is the quotient face of the
factorization above; nothing below depends on it, and it is recorded because it is the form in which
the first-order approximation is usually stated. -/
theorem theChartOverItsRootFactorTendsToTheDerivative {p : Polynomial ℝ} {r : ℝ}
    (hp : p.eval r = 0) :
    Filter.Tendsto (fun x : ℝ => p.eval x / (x - r)) (nhdsWithin r {r}ᶜ)
      (nhds ((derivative p).eval r)) := by
  obtain ⟨q, hfac, hqr⟩ := theSimpleRootFactorsWithItsDerivativeAsCofactor hp
  have hagree : ∀ x ∈ ({r}ᶜ : Set ℝ), p.eval x / (x - r) = q.eval x := by
    intro x hx
    have hx' : x - r ≠ 0 := sub_ne_zero.mpr hx
    rw [hfac]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    field_simp
  have hcong : (fun x : ℝ => p.eval x / (x - r)) =ᶠ[nhdsWithin r {r}ᶜ] fun x : ℝ => q.eval x :=
    Filter.eventuallyEq_of_mem self_mem_nhdsWithin hagree
  rw [← hqr]
  exact Filter.Tendsto.congr' hcong.symm q.continuousAt.continuousWithinAt

/-- **A simple root's window separates the chart from its derivative.**  On one exhibited window
around a simple root: the derivative keeps the sign it has at `r`; the chart is strictly opposed to
that sign below `r`; and strictly aligned with it above.  Every later local statement is a
consequence of this one. -/
theorem theSimpleRootWindowCarriesBothSigns {p : Polynomial ℝ} {r : ℝ}
    (hp : p.eval r = 0) (hd : (derivative p).eval r ≠ 0) :
    ∃ δ > 0, ∀ x : ℝ, r - δ < x → x < r + δ →
      0 < (derivative p).eval x * (derivative p).eval r ∧
      (x < r → p.eval x * (derivative p).eval r < 0) ∧
      (r < x → 0 < p.eval x * (derivative p).eval r) := by
  obtain ⟨q, hfac, hqr⟩ := theSimpleRootFactorsWithItsDerivativeAsCofactor hp
  set c : ℝ := (derivative p).eval r with hc
  have hc2 : 0 < c * c := by
    rcases lt_or_gt_of_ne hd with h | h
    · exact mul_pos_of_neg_of_neg h h
    · exact mul_pos h h
  have hq1 : 0 < (q * C c).eval r := by
    simp only [eval_mul, eval_C, hqr]
    exact hc2
  have hq2 : 0 < (derivative p * C c).eval r := by
    simp only [eval_mul, eval_C]
    exact hc2
  obtain ⟨δ₁, hδ₁, hpos₁⟩ := thePositiveValueSurvivesInAWindow hq1
  obtain ⟨δ₂, hδ₂, hpos₂⟩ := thePositiveValueSurvivesInAWindow hq2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro x h1 h2
  have hm1 : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
  have hm2 : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
  have hA : 0 < q.eval x * c := by
    have := hpos₁ x (by linarith) (by linarith)
    simpa using this
  have hB : 0 < (derivative p).eval x * c := by
    have := hpos₂ x (by linarith) (by linarith)
    simpa using this
  have hval : p.eval x * c = (x - r) * (q.eval x * c) := by
    rw [hfac]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    ring
  refine ⟨hB, ?_, ?_⟩
  · intro hlt
    rw [hval]
    exact mul_neg_of_neg_of_pos (by linarith) hA
  · intro hgt
    rw [hval]
    exact mul_pos (by linarith) hA

/-- **A simple root flips the chart against its own derivative value.**  Below the root
`p(x)·p'(r) < 0`, above it `p(x)·p'(r) > 0`.  The general flip cannot say this: at a double root
`p` keeps one sign throughout. -/
theorem theSimpleRootFlipsTheChartAgainstItsDerivativeValue {p : Polynomial ℝ} {r : ℝ}
    (hp : p.eval r = 0) (hd : (derivative p).eval r ≠ 0) :
    ∃ δ > 0,
      (∀ x : ℝ, r - δ < x → x < r → p.eval x * (derivative p).eval r < 0) ∧
      (∀ x : ℝ, r < x → x < r + δ → 0 < p.eval x * (derivative p).eval r) := by
  obtain ⟨δ, hδ, hwin⟩ := theSimpleRootWindowCarriesBothSigns hp hd
  exact ⟨δ, hδ, fun x h1 h2 => (hwin x h1 (by linarith)).2.1 h2,
    fun x h1 h2 => (hwin x (by linarith) h2).2.2 h1⟩

/-- **The chart and its derivative are both nonzero on a punctured simple-root window.**  The
non-degeneracy a variation count needs before it may read the pair at all. -/
theorem theSimpleRootWindowIsBlindNowhereButTheRoot {p : Polynomial ℝ} {r : ℝ}
    (hp : p.eval r = 0) (hd : (derivative p).eval r ≠ 0) :
    ∃ δ > 0, ∀ x : ℝ, r - δ < x → x < r + δ → x ≠ r →
      p.eval x ≠ 0 ∧ (derivative p).eval x ≠ 0 := by
  obtain ⟨δ, hδ, hwin⟩ := theSimpleRootWindowCarriesBothSigns hp hd
  refine ⟨δ, hδ, fun x h1 h2 hne => ⟨?_, ?_⟩⟩
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · intro h0
      have := (hwin x h1 h2).2.1 hlt
      rw [h0, zero_mul] at this
      exact absurd this (lt_irrefl 0)
    · intro h0
      have := (hwin x h1 h2).2.2 hgt
      rw [h0, zero_mul] at this
      exact absurd this (lt_irrefl 0)
  · intro h0
    have := (hwin x h1 h2).1
    rw [h0, zero_mul] at this
    exact absurd this (lt_irrefl 0)

/-! ## 4. No-root constancy

The contrapositive of the intermediate value theorem (Bolzano 1817), as Mathlib's
`intermediate_value_Ioo` supplies it. -/

/-- **Opposite signs at the endpoints force a root strictly inside.**  The root is placed in the
*open* interval, so an endpoint that is itself a root is never the witness. -/
theorem theOppositeSignsForceARootStrictlyInside {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : p.eval a * p.eval b < 0) : ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  rcases lt_trichotomy (p.eval a) 0 with hA | hA | hA
  · have hB : 0 < p.eval b := by nlinarith
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo hab hcont ⟨hA, hB⟩
    exact ⟨c, hc, hc0⟩
  · rw [hA, zero_mul] at h
    exact absurd h (lt_irrefl 0)
  · have hB : p.eval b < 0 := by nlinarith
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' hab hcont ⟨hB, hA⟩
    exact ⟨c, hc, hc0⟩

/-- **A root-free closed interval keeps the sign of its lower endpoint.**  Nothing on the interval
can oppose `p(a)`, because opposing it would produce a root the hypothesis forbids. -/
theorem theRootFreeIntervalKeepsTheSignOfItsLowerEndpoint {p : Polynomial ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfree : ∀ z ∈ Set.Icc a b, p.eval z ≠ 0) :
    ∀ x ∈ Set.Icc a b, 0 < p.eval a * p.eval x := by
  intro x hx
  have ha : p.eval a ≠ 0 := hfree a ⟨le_refl a, hab⟩
  have hxne : p.eval x ≠ 0 := hfree x hx
  rcases lt_trichotomy (p.eval a * p.eval x) 0 with hlt | heq | hgt
  · exfalso
    obtain ⟨c, hc, hc0⟩ := theOppositeSignsForceARootStrictlyInside hx.1 hlt
    exact hfree c ⟨le_of_lt hc.1, le_of_lt (lt_of_lt_of_le hc.2 hx.2)⟩ hc0
  · exact absurd heq (mul_ne_zero ha hxne)
  · exact hgt

/-- **NO-ROOT CONSTANCY.**  On a closed interval carrying no real root, any two points return
values of the same sign — their product is strictly positive.  This is the statement a counting
argument uses between roots, and it is stated pointwise rather than as a `Set` predicate so that
nothing about connectedness has to be re-derived at the use site. -/
theorem theRootFreeIntervalGivesAnyTwoPointsOneSign {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfree : ∀ z ∈ Set.Icc a b, p.eval z ≠ 0) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, 0 < p.eval x * p.eval y := by
  intro x hx y hy
  have h1 := theRootFreeIntervalKeepsTheSignOfItsLowerEndpoint hab hfree x hx
  have h2 := theRootFreeIntervalKeepsTheSignOfItsLowerEndpoint hab hfree y hy
  have hane : p.eval a ≠ 0 := hfree a ⟨le_refl a, hab⟩
  have hsq : 0 < p.eval a ^ 2 := by positivity
  have hkey : 0 < p.eval a ^ 2 * (p.eval x * p.eval y) := by
    have : p.eval a ^ 2 * (p.eval x * p.eval y)
        = (p.eval a * p.eval x) * (p.eval a * p.eval y) := by ring
    rw [this]
    exact mul_pos h1 h2
  nlinarith

/-- **The chart keeps one sign between consecutive roots.**  Stated over the open gap and by
root-freeness alone: the endpoints need not be roots for the conclusion to hold, and saying so is
what keeps the hypothesis honest.  The consecutive-root reading is the intended use — take `r₁`,
`r₂` adjacent roots of the chain's head — and `theSignOnTheGapIsSetByTheDerivativeAtTheLowerSimpleRoot`
below is the form in which the roots themselves do work. -/
theorem theChartKeepsOneSignBetweenConsecutiveRoots {p : Polynomial ℝ} {r₁ r₂ : ℝ}
    (hfree : ∀ z ∈ Set.Ioo r₁ r₂, p.eval z ≠ 0) :
    ∀ x ∈ Set.Ioo r₁ r₂, ∀ y ∈ Set.Ioo r₁ r₂, 0 < p.eval x * p.eval y := by
  have hpair : ∀ x ∈ Set.Ioo r₁ r₂, ∀ y ∈ Set.Ioo r₁ r₂, x ≤ y →
      0 < p.eval x * p.eval y := by
    intro x hx y hy hxy
    refine theRootFreeIntervalGivesAnyTwoPointsOneSign hxy ?_ x ⟨le_refl x, hxy⟩ y ⟨hxy, le_refl y⟩
    intro z hz
    exact hfree z ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact hpair x hx y hy hxy
  · have := hpair y hy x hx hyx
    rwa [mul_comm] at this

/-- **On the gap above a simple root, the sign is the derivative's sign at that root.**  Both
hypotheses do work: the flip fixes the sign immediately above `r₁`, and root-freeness propagates it
across the whole gap.  This is the shape a chain reading needs — not merely *a* sign, but *which*
one. -/
theorem theSignOnTheGapIsSetByTheDerivativeAtTheLowerSimpleRoot {p : Polynomial ℝ} {r₁ r₂ : ℝ}
    (h12 : r₁ < r₂) (hp : p.eval r₁ = 0) (hd : (derivative p).eval r₁ ≠ 0)
    (hfree : ∀ z ∈ Set.Ioo r₁ r₂, p.eval z ≠ 0) :
    ∀ x ∈ Set.Ioo r₁ r₂, 0 < p.eval x * (derivative p).eval r₁ := by
  obtain ⟨δ, hδ, _, habove⟩ := theSimpleRootFlipsTheChartAgainstItsDerivativeValue hp hd
  set t : ℝ := r₁ + min δ (r₂ - r₁) / 2 with ht
  have hmin1 : min δ (r₂ - r₁) ≤ δ := min_le_left _ _
  have hmin2 : min δ (r₂ - r₁) ≤ r₂ - r₁ := min_le_right _ _
  have hminpos : 0 < min δ (r₂ - r₁) := lt_min hδ (by linarith)
  have htmem : t ∈ Set.Ioo r₁ r₂ := ⟨by simp only [ht]; linarith, by simp only [ht]; linarith⟩
  have hts : 0 < p.eval t * (derivative p).eval r₁ :=
    habove t (by simp only [ht]; linarith) (by simp only [ht]; linarith)
  intro x hx
  have hxt : 0 < p.eval x * p.eval t := theChartKeepsOneSignBetweenConsecutiveRoots hfree x hx t htmem
  have htne : p.eval t ≠ 0 := hfree t htmem
  have htsq : 0 < p.eval t ^ 2 := by positivity
  have hkey : 0 < p.eval t ^ 2 * (p.eval x * (derivative p).eval r₁) := by
    have : p.eval t ^ 2 * (p.eval x * (derivative p).eval r₁)
        = (p.eval x * p.eval t) * (p.eval t * (derivative p).eval r₁) := by ring
    rw [this]
    exact mul_pos hxt hts
  nlinarith

/-! ## 5. The variation count at a real point

`Sturm.variationCount` reads a chain at a **rational** point.  A counting law has to read it at
real points inside a window, so the count is re-declared over `ℝ` — same three clauses, same
zero-dropping rule — and the rational reading is proved to cast into it exactly. -/

/-- Sign variations along a list of real values, continuing from a declared nonzero predecessor.
Zeros are dropped, never counted.  This mirrors `Sturm.variationFrom` clause for clause. -/
noncomputable def realVariationFrom (u : ℝ) : List ℝ → ℕ
  | [] => 0
  | v :: l => if v = 0 then realVariationFrom u l else (if u * v < 0 then 1 else 0) + realVariationFrom v l

/-- The sign-variation count of a list of real values.  This mirrors `Sturm.variationCount`. -/
noncomputable def realVariationCount : List ℝ → ℕ
  | [] => 0
  | v :: l => if v = 0 then realVariationCount l else realVariationFrom v l

/-- The values of a rational reading, presented as real values.  Written as its own recursion
rather than as a coerced `List.map`, so that no list-level coercion enters the statements. -/
def castValues : List ℚ → List ℝ
  | [] => []
  | v :: l => (v : ℝ) :: castValues l

/-- Casting a value list peels one value.  `rfl`-class: this proof is `rfl`. -/
theorem theCastPeelsOneValue (v : ℚ) (l : List ℚ) :
    castValues (v :: l) = (v : ℝ) :: castValues l := rfl

/-- A rational value is blind exactly when its real presentation is. -/
theorem theBlindnessOfAValueSurvivesTheCast (v : ℚ) : ((v : ℝ) = 0) ↔ (v = 0) := by
  exact_mod_cast Iff.rfl

/-- A pair of rational values is opposed exactly when its real presentation is. -/
theorem theOppositionOfTwoValuesSurvivesTheCast (u v : ℚ) :
    ((u : ℝ) * (v : ℝ) < 0) ↔ (u * v < 0) := by
  rw [← Rat.cast_mul]
  exact_mod_cast Iff.rfl

/-- The continuing count is unchanged by presenting its values as real values. -/
theorem theRationalContinuingCountCastsToTheRealContinuingCount :
    ∀ (u : ℚ) (l : List ℚ),
      Sturm.variationFrom u l = realVariationFrom (u : ℝ) (castValues l) := by
  intro u l
  induction l generalizing u with
  | nil => rfl
  | cons v l ih =>
    rw [theCastPeelsOneValue]
    simp only [Sturm.variationFrom, realVariationFrom]
    by_cases hv : v = 0
    · rw [if_pos hv, if_pos ((theBlindnessOfAValueSurvivesTheCast v).mpr hv), ih u]
    · rw [if_neg hv, if_neg (fun h => hv ((theBlindnessOfAValueSurvivesTheCast v).mp h)), ih v]
      by_cases hs : u * v < 0
      · rw [if_pos hs, if_pos ((theOppositionOfTwoValuesSurvivesTheCast u v).mpr hs)]
      · rw [if_neg hs, if_neg (fun h => hs ((theOppositionOfTwoValuesSurvivesTheCast u v).mp h))]

/-- **The rational reading casts to the real reading exactly.**  Sturm's chain is read at rational
endpoints; a counting law compares those readings against a population of *real* roots inside the
window, so the two counts must be one count.  They are. -/
theorem theRationalCountCastsToTheRealCount :
    ∀ l : List ℚ, Sturm.variationCount l = realVariationCount (castValues l) := by
  intro l
  induction l with
  | nil => rfl
  | cons v l ih =>
    rw [theCastPeelsOneValue]
    simp only [Sturm.variationCount, realVariationCount]
    by_cases hv : v = 0
    · rw [if_pos hv, if_pos ((theBlindnessOfAValueSurvivesTheCast v).mpr hv)]
      exact ih
    · rw [if_neg hv, if_neg (fun h => hv ((theBlindnessOfAValueSurvivesTheCast v).mp h))]
      exact theRationalContinuingCountCastsToTheRealContinuingCount v l

/-- A two-value reading, with both values nonzero, is one variation or none according to the sign
of their product.  Both blindness tests are discharged before the sign test is reached. -/
theorem theTwoValueReadingIsTheSignOfTheProduct {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    realVariationCount [u, v] = if u * v < 0 then 1 else 0 := by
  simp only [realVariationCount, realVariationFrom, if_neg hu, if_neg hv, add_zero]

/-- **THE PAIR LOSES EXACTLY ONE VARIATION ACROSS A SIMPLE ROOT.**  On one exhibited window, the
pair `(p, p')` reads `1` at every point strictly below the root and `0` at every point strictly
above it.  This is the head's own contribution to a chain reading, in isolation; **it is not the
chain statement**, because it says nothing about the remaining entries. -/
theorem thePairLosesExactlyOneVariationAcrossASimpleRoot {p : Polynomial ℝ} {r : ℝ}
    (hp : p.eval r = 0) (hd : (derivative p).eval r ≠ 0) :
    ∃ δ > 0,
      (∀ x : ℝ, r - δ < x → x < r →
        realVariationCount [p.eval x, (derivative p).eval x] = 1) ∧
      (∀ x : ℝ, r < x → x < r + δ →
        realVariationCount [p.eval x, (derivative p).eval x] = 0) := by
  obtain ⟨δ, hδ, hwin⟩ := theSimpleRootWindowCarriesBothSigns hp hd
  set c : ℝ := (derivative p).eval r with hc
  have hc2 : 0 < c * c := by
    rcases lt_or_gt_of_ne hd with h | h
    · exact mul_pos_of_neg_of_neg h h
    · exact mul_pos h h
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro x h1 h2
    obtain ⟨hB, hbelow, _⟩ := hwin x h1 (by linarith)
    have hA := hbelow h2
    have hune : p.eval x ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hA; exact absurd hA (lt_irrefl 0)
    have hvne : (derivative p).eval x ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hB; exact absurd hB (lt_irrefl 0)
    rw [theTwoValueReadingIsTheSignOfTheProduct hune hvne, if_pos]
    refine (theStrictSignSurvivesAPositiveFactor hc2).1.mp ?_
    have hkey : (p.eval x * (derivative p).eval x) * (c * c)
        = (p.eval x * c) * ((derivative p).eval x * c) := by ring
    rw [hkey]
    exact mul_neg_of_neg_of_pos hA hB
  · intro x h1 h2
    obtain ⟨hB, _, habove⟩ := hwin x (by linarith) h2
    have hA := habove h1
    have hune : p.eval x ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hA; exact absurd hA (lt_irrefl 0)
    have hvne : (derivative p).eval x ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hB; exact absurd hB (lt_irrefl 0)
    rw [theTwoValueReadingIsTheSignOfTheProduct hune hvne, if_neg]
    refine not_lt.mpr (le_of_lt ((theStrictSignSurvivesAPositiveFactor hc2).2.mp ?_))
    have hkey : (p.eval x * (derivative p).eval x) * (c * c)
        = (p.eval x * c) * ((derivative p).eval x * c) := by ring
    rw [hkey]
    exact mul_pos hA hB

/-- **An interior entry going blind makes its neighbours straddle.**  If `P = T·Q − R` and `Q`
vanishes at a point where `R` does not, then `P` and `R` have strictly opposite signs there, so the
triple `[P, Q, R]` reads exactly `1` at that point — whatever `Q` was doing.  This is the pointwise
fact behind the interior half of a chain-counting argument; the **two-sided comparison** that would
turn it into an invariance is not proved here. -/
theorem theInteriorEntryStraddlesItsNeighbours {P Q R T : Polynomial ℝ} (hdiv : P = T * Q - R)
    {r : ℝ} (hQ : Q.eval r = 0) (hR : R.eval r ≠ 0) :
    P.eval r * R.eval r < 0 ∧ realVariationCount [P.eval r, Q.eval r, R.eval r] = 1 := by
  have hPr : P.eval r = -R.eval r := by
    rw [hdiv]
    simp [hQ]
  have hneg : P.eval r * R.eval r < 0 := by
    rw [hPr]
    have : -R.eval r * R.eval r = -(R.eval r * R.eval r) := by ring
    rw [this, neg_lt_zero]
    rcases lt_or_gt_of_ne hR with h | h
    · exact mul_pos_of_neg_of_neg h h
    · exact mul_pos h h
  refine ⟨hneg, ?_⟩
  have hPne : P.eval r ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hneg; exact absurd hneg (lt_irrefl 0)
  rw [hQ]
  show (if P.eval r = 0 then _ else realVariationFrom (P.eval r) [(0 : ℝ), R.eval r]) = 1
  rw [if_neg hPne]
  show (if (0 : ℝ) = 0 then realVariationFrom (P.eval r) [R.eval r] else _) = 1
  rw [if_pos rfl]
  show (if R.eval r = 0 then _
    else (if P.eval r * R.eval r < 0 then 1 else 0) + realVariationFrom (R.eval r) []) = 1
  rw [if_neg hR, if_pos hneg]
  rfl

/-! ## 6. The star quartic, carried over from Sturm's material

`X⁴ − 5X² + 4` is the squarefree part of `D₆(x) − 2` — the Dickson polynomial with
`D_n(z + z⁻¹) = zⁿ + z⁻ⁿ` — whose roots `2, 1, −1, −2` are the star values `β_m = ω^m + ω^{−m}` at
`n = 6`, the terrain of `crates/holonic-engine/src/winding_inertia.rs`.  Sturm's chain for it is
transcribed here as real polynomials so the local lemmas can be run on it. -/

/-- The chain's head: the star quartic. -/
noncomputable def starHead : Polynomial ℝ := X ^ 4 - C 5 * X ^ 2 + C 4

/-- The chain's second entry: the head's derivative, `4X³ − 10X`. -/
noncomputable def starDerivative : Polynomial ℝ := C 4 * X ^ 3 - C 10 * X

/-- The negated remainder of degree two, `(5/2)X² − 4`. -/
noncomputable def starQuadraticRemainder : Polynomial ℝ := C (5 / 2) * X ^ 2 - C 4

/-- The negated remainder of degree one, `(18/5)X`. -/
noncomputable def starLinearRemainder : Polynomial ℝ := C (18 / 5) * X

/-- The chain's terminal constant, `4`.  It vanishes nowhere, which is why the chain's adjacent
entries share no root. -/
noncomputable def starTerminalConstant : Polynomial ℝ := C 4

/-- The head evaluates to `x⁴ − 5x² + 4`. -/
theorem theStarHeadIsTheRealQuartic (x : ℝ) : starHead.eval x = x ^ 4 - 5 * x ^ 2 + 4 := by
  simp [starHead]

/-- **The head names the same function as `Sturm.starHexagonChart`.**  The two files carry one
object; nothing here is a second, parallel quartic. -/
theorem theStarHeadIsSturmsStarChart (x : ℝ) :
    starHead.eval x = Sturm.evalReal x Sturm.starHexagonChart := by
  rw [theStarHeadIsTheRealQuartic, Sturm.theStarHexagonChartIsTheRealQuartic]

/-- **The head's derivative is the chain's second entry.** -/
theorem theStarDerivativeIsTheChainsSecondEntry : derivative starHead = starDerivative := by
  simp only [starHead, starDerivative, derivative_add, derivative_sub, derivative_mul,
    derivative_C, derivative_X_pow]
  apply Polynomial.funext
  intro z
  simp
  ring

/-- **The star chain is an exact division tower over the reals**: `p₀ = (X/4)·p₁ − p₂`,
`p₁ = (8X/5)·p₂ − p₃`, `p₂ = (25X/36)·p₃ − p₄`.  These are the identities
`Sturm.theStarHexagonChainIsADivisionTower` states over `ℚ`, lifted to `Polynomial ℝ` so that
`theInteriorEntryStraddlesItsNeighbours` can consume them. -/
theorem theStarChainIsADivisionTowerOverTheReals :
    starHead = C (1 / 4) * X * starDerivative - starQuadraticRemainder ∧
    starDerivative = C (8 / 5) * X * starQuadraticRemainder - starLinearRemainder ∧
    starQuadraticRemainder = C (25 / 36) * X * starLinearRemainder - starTerminalConstant := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · apply Polynomial.funext
      intro z
      simp [starHead, starDerivative, starQuadraticRemainder, starLinearRemainder,
        starTerminalConstant]
      ring

/-- **The star chain straddles at the origin, twice.**  At `x = 0` the chain's second and fourth
entries both go blind; each time, the two neighbours are strictly opposed and the local triple reads
`1`.  This is `Sturm.theStarHexagonReadingDropsItsBlindEntries` seen locally: the reading did not
lose those entries, it read straight through them. -/
theorem theStarChainStraddlesAtTheOrigin :
    starHead.eval 0 * starQuadraticRemainder.eval 0 < 0 ∧
    realVariationCount [starHead.eval 0, starDerivative.eval 0, starQuadraticRemainder.eval 0] = 1 ∧
    starQuadraticRemainder.eval 0 * starTerminalConstant.eval 0 < 0 ∧
    realVariationCount [starQuadraticRemainder.eval 0, starLinearRemainder.eval 0,
      starTerminalConstant.eval 0] = 1 := by
  obtain ⟨htower₁, _, htower₃⟩ := theStarChainIsADivisionTowerOverTheReals
  have hQ₁ : starDerivative.eval (0 : ℝ) = 0 := by norm_num [starDerivative]
  have hR₁ : starQuadraticRemainder.eval (0 : ℝ) ≠ 0 := by norm_num [starQuadraticRemainder]
  have hQ₂ : starLinearRemainder.eval (0 : ℝ) = 0 := by norm_num [starLinearRemainder]
  have hR₂ : starTerminalConstant.eval (0 : ℝ) ≠ 0 := by norm_num [starTerminalConstant]
  obtain ⟨hheadStraddle, hheadRead⟩ := theInteriorEntryStraddlesItsNeighbours htower₁ hQ₁ hR₁
  obtain ⟨htailStraddle, htailRead⟩ := theInteriorEntryStraddlesItsNeighbours htower₃ hQ₂ hR₂
  exact ⟨hheadStraddle, hheadRead, htailStraddle, htailRead⟩

/-- **The head flips at its upper star value.**  `2` is a simple root of `X⁴ − 5X² + 4`
(`p(2) = 0`, `p'(2) = 12`), so the product with the derivative passes from negative to positive
across it, on an exhibited window. -/
theorem theStarHeadFlipsAtItsUpperStarValue :
    starHead.eval 2 = 0 ∧ (derivative starHead).eval 2 = 12 ∧
      ∃ δ > 0,
        (∀ x : ℝ, 2 - δ < x → x < 2 → starHead.eval x * (derivative starHead).eval 2 < 0) ∧
        (∀ x : ℝ, 2 < x → x < 2 + δ → 0 < starHead.eval x * (derivative starHead).eval 2) := by
  have hp : starHead.eval (2 : ℝ) = 0 := by rw [theStarHeadIsTheRealQuartic]; norm_num
  have hdv : (derivative starHead).eval (2 : ℝ) = 12 := by
    rw [theStarDerivativeIsTheChainsSecondEntry]
    simp [starDerivative]
    norm_num
  refine ⟨hp, hdv, ?_⟩
  exact theSimpleRootFlipsTheChartAgainstItsDerivativeValue hp (by rw [hdv]; norm_num)

/-- **The head keeps one sign between its two positive star values.**  On `(1, 2)` the quartic has
no root — `(x² − 1)(x² − 4)` is a strictly negative product there — so any two points of the gap
return values of the same sign, and that sign is fixed by the derivative at the lower root,
`p'(1) = −6`.  Both faces of the corollary, on the material `winding_inertia.rs` actually
isolates. -/
theorem theStarHeadKeepsOneSignBetweenItsPositiveStarValues :
    (∀ z ∈ Set.Ioo (1 : ℝ) 2, starHead.eval z ≠ 0) ∧
    (∀ x ∈ Set.Ioo (1 : ℝ) 2, ∀ y ∈ Set.Ioo (1 : ℝ) 2, 0 < starHead.eval x * starHead.eval y) ∧
    (∀ x ∈ Set.Ioo (1 : ℝ) 2, starHead.eval x < 0) := by
  have hfree : ∀ z ∈ Set.Ioo (1 : ℝ) 2, starHead.eval z ≠ 0 := by
    intro z hz
    rw [theStarHeadIsTheRealQuartic]
    have h1 : 0 < z ^ 2 - 1 := by nlinarith [hz.1, hz.2]
    have h2 : z ^ 2 - 4 < 0 := by nlinarith [hz.1, hz.2]
    have : z ^ 4 - 5 * z ^ 2 + 4 = (z ^ 2 - 1) * (z ^ 2 - 4) := by ring
    rw [this]
    exact ne_of_lt (mul_neg_of_pos_of_neg h1 h2)
  have hp1 : starHead.eval (1 : ℝ) = 0 := by rw [theStarHeadIsTheRealQuartic]; norm_num
  have hd1 : (derivative starHead).eval (1 : ℝ) = -6 := by
    rw [theStarDerivativeIsTheChainsSecondEntry]
    simp [starDerivative]
    norm_num
  refine ⟨hfree, theChartKeepsOneSignBetweenConsecutiveRoots hfree, ?_⟩
  intro x hx
  have := theSignOnTheGapIsSetByTheDerivativeAtTheLowerSimpleRoot (by norm_num : (1 : ℝ) < 2)
    hp1 (by rw [hd1]; norm_num) hfree x hx
  rw [hd1] at this
  linarith

/-! ## 7. The controls

Each hypothesis is shown to do work, and one expected failure is shown **not** to occur. -/

/-- **The root hypothesis is load-bearing.**  On `p = X` at the non-root `1`, no window below `1`
carries a negative `p·p'`: the product is `x`, which is positive there.  So the flip is a statement
about roots and not a statement about polynomials. -/
theorem theRootHypothesisIsLoadBearing :
    ∃ (p : Polynomial ℝ) (r : ℝ), p.eval r ≠ 0 ∧ (derivative p).eval r ≠ 0 ∧
      ∀ δ : ℝ, 0 < δ → ¬ (∀ x : ℝ, r - δ < x → x < r → (p * derivative p).eval x < 0) := by
  refine ⟨(X : Polynomial ℝ), 1, by simp, by simp, ?_⟩
  intro δ hδ hcon
  have hm1 : min δ 1 ≤ δ := min_le_left _ _
  have hm2 : min δ 1 ≤ 1 := min_le_right _ _
  have hm3 : 0 < min δ 1 := lt_min hδ one_pos
  have hx := hcon (1 - min δ 1 / 2) (by linarith) (by linarith)
  simp at hx
  linarith

/-- The chart `(X − 1)²·(X − 3)`: a double root at `1` beside a simple root at `3`.  It is the
material on which the flip is shown not to see an exponent. -/
noncomputable def multiplicityProbe : Polynomial ℝ := (X - C 1) ^ 2 * (X - C 3)

/-- The probe evaluates to `(x − 1)²(x − 3)`. -/
theorem theMultiplicityProbeIsACubic (x : ℝ) :
    multiplicityProbe.eval x = (x - 1) ^ 2 * (x - 3) := by
  simp [multiplicityProbe]

/-- **The probe's product with its derivative factors at an odd power**, exactly as the general
theorem predicts: `p·p' = (X − 1)³·(X − 3)·(3X − 7)`, and `2·2 − 1 = 3` is the odd exponent the
double root contributes. -/
theorem theMultiplicityProbeProductFactorsAtAnOddPower (x : ℝ) :
    (multiplicityProbe * derivative multiplicityProbe).eval x
      = (x - 1) ^ 3 * ((x - 3) * (3 * x - 7)) := by
  simp [multiplicityProbe, derivative_mul, derivative_pow]
  ring

/-- **The flip does not detect multiplicity, and this was measured before it was proved.**  At the
double root `1` of `(X−1)²(X−3)` the derivative also vanishes, so the simple-root hypothesis fails —
yet `p·p' = (X−1)³(X−3)(3X−7)` still passes from negative to positive across `1`.  The exhibited
window is `δ = 1/2`.  This is why the general flip above is stated without a simplicity hypothesis,
and it is the reason a sign-variation instrument counts **distinct** roots: nothing in the flip can
see the exponent. -/
theorem theFlipDoesNotDetectMultiplicity :
    multiplicityProbe.eval 1 = 0 ∧ (derivative multiplicityProbe).eval 1 = 0 ∧
      (∀ x : ℝ, 1 - 1 / 2 < x → x < 1 →
        (multiplicityProbe * derivative multiplicityProbe).eval x < 0) ∧
      (∀ x : ℝ, 1 < x → x < 1 + 1 / 2 →
        0 < (multiplicityProbe * derivative multiplicityProbe).eval x) := by
  refine ⟨by rw [theMultiplicityProbeIsACubic]; norm_num, ?_, ?_, ?_⟩
  · simp [multiplicityProbe, derivative_mul, derivative_pow]
  · intro x h1 h2
    rw [theMultiplicityProbeProductFactorsAtAnOddPower]
    have hcube : (x - 1) ^ 3 < 0 := by
      have hsplit : (x - 1) ^ 3 = (x - 1) * (x - 1) ^ 2 := by ring
      rw [hsplit]
      have hsq : 0 < (x - 1) ^ 2 := by nlinarith
      exact mul_neg_of_neg_of_pos (by linarith) hsq
    exact mul_neg_of_neg_of_pos hcube
      (mul_pos_of_neg_of_neg (by linarith) (by linarith))
  · intro x h1 h2
    rw [theMultiplicityProbeProductFactorsAtAnOddPower]
    exact mul_pos (pow_pos (by linarith : (0 : ℝ) < x - 1) 3)
      (mul_pos_of_neg_of_neg (by linarith) (by linarith))

end Soma.Holonics.Millennium.SignChange
