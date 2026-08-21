import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Card

/-!
# Sturm: the reading is the sign variation, and it equals the realized population

**What is proved.**  The exact real-root counting instrument — the negated-remainder chain and
the sign-variation reading of that chain at a rational point (*Sturm's chain* and *Sturm's
theorem*, Sturm 1829) — is built here over `ℚ` as a **computable** carrier, with the polynomial
side of the bridge landing in `Polynomial ℚ`, and it is exercised on **five explicit charts across
nine declared windows**, each window's root population re-derived independently before encoding.
The instrument's own laws are proved in general: the reading peels one coefficient at a time
(*Horner's recurrence*) and the chain opens with the construction — **both `rfl`-class, each
proof literally `rfl`**; trimming the chart does not move the reading; trimming is idempotent; a
chart is the evaluation of its polynomial; the rational reading casts to the real reading; **an
entry blind at the point is
dropped by the reading rather than counted**; the reading is invariant under a positive rescaling
of the values; the reading never exceeds the chain length; the chain carries no empty entry after
its head; and a root shared by two consecutive entries **descends** the division tower.

**The receiver question this file serves is `THE READING EQUALS THE POPULATION`, and here that is
an equation rather than a slogan.**  For **every one of the nine windows** the sign-variation
difference is proved, the real-root population inside that window is proved to be an explicit set
of real points, and that set's `Set.ncard` is proved to be the same natural number the reading
returned.  Nothing counts anything twice: the population is a set and the reading is a difference
of two natural numbers.

**Measured 2026-08-21** over the pinned Mathlib (`v4.27.0`, revision `a3a10db0e9`) at
`.lake/packages/mathlib`: `grep -rli "sturm" Mathlib --include='*.lean'` → **0 files**;
`grep -rli "sturm" Mathlib` (no extension filter) → **0 files**.  Those commands measure that
name over that scope.  What Mathlib *does* own is the neighbouring instrument, and it is
important not to confuse them: `Mathlib/Algebra/Polynomial/RuleOfSigns.lean` defines
`Polynomial.signVariations` on a polynomial's **coefficient list** and proves
`Polynomial.roots_countP_pos_le_signVariations` — the coefficient-sign **bound** on the number of
positive roots (*Descartes' rule of signs*, Descartes 1637).  A bound is not a count.  The file
exhibits the gap on its own material: on `X² − 2X + 2` the same sign-variation reading applied to
the coefficient list returns `2` while the chain reading returns `0`, and the real population is
empty.  **That single pair of numbers is why this instrument is worth having.**

**The Rust owners are read, not rebuilt.**  `crates/holonic-engine/src/exact_value.rs` carries
`sturm_sequence`, `sign_variations`, `distinct_root_count` and `AlgebraicRoot::isolate` with its
`SturmIsolationCertificate { variations_at_lower, variations_at_upper }`, refusing an interval
whose endpoint is itself a root and refusing an orientation whose count would be negative;
`crates/holonic-engine/src/winding_inertia.rs` uses that isolation as the certificate carrier for
the star values `β_m = ω^m + ω^{−m}`, the roots of the squarefree part of `D_n(x) − 2`.  The
chain, the negation, the zero-dropping filter and the adjacent-difference count encoded below are
that owner's definitions transcribed; the third anchor is that owner's own terrain, `n = 6`, whose
squarefree part `X⁴ − 5X² + 4` is asserted by that module's test at `winding_inertia.rs` (grep
`the_dickson_polynomial_carries_every_star_value_as_a_root`).

**One deliberate difference from the transcribed owner, recorded rather than smoothed over.**  On
a *constant* chart the Rust `sturm_sequence` seeds its vector with `[p, p']` before testing, so it
returns a trailing **empty** entry; `remainderChain` below halts first and returns none.  The two
readings are nevertheless identical, because an empty entry evaluates to zero everywhere and the
zero-dropping filter discards it — which is `theBlindEntryIsDroppedByTheReading` covering the
difference.  A constant chart is refused outright by `AlgebraicRoot::isolate` in any case
(`ConstantPolynomial`), so nothing downstream of either sees it.

**The fuel is an apparatus aperture and it is shown not to select.**  The chain recursion is
driven by a fuel bound read off the material — the chart's own length — because the degrees
strictly decrease down a remainder sequence.  Rather than assert adequacy, each anchor is proved
to return the identical chain under a fuel far larger than the one the instrument uses.  A number
that changed the answer would be an authored level; this one is measured not to.

**Independent re-verification, before any encoding** (exact `fractions.Fraction`, no floats): each
chain was recomputed from the definition, and each window's *distinct* real-root count was
recomputed by a route that never touches a sign chain — squarefree part by exact polynomial `gcd`,
then exact grid subdivision at five resolutions (7, 29, 101, 401, 1009 subintervals) with exact
zero detection, stable at every resolution.  All nine reading/population pairs agreed; **zero
discrepancies were found and nothing was adjusted to make a number fit.**

**What this file does NOT claim.**  Sturm's theorem itself is **not proved here**: it stands as
the named-open proposition `TheReadingEqualsThePopulation`, stated in full over real roots in a
window with rational endpoints, and it is never assumed — no theorem below has it as a hypothesis
except `theOpenLawWouldDischargeTheStarWindow`, which exhibits, as an implication, exactly what
the open proposition would buy.  Nothing here is a statement about the Riemann hypothesis or any
other named conjecture; no zeta function, L-function, curve or variety appears.  There is no
bisection driver, no isolation loop, no algebraic-number carrier and no claim of a decision
procedure — a chain and a reading are built, and five charts are read.  The general division
identity `p_{i−1} = q·p_i − p_{i+1}` for the *computed* chain is not proved; it is proved instead
as an exact identity on each of the five anchors' exhibited chains, which is what makes the
descent lemma bite there.  The **per-entry** positive gauge — rescaling each chain entry by its
own positive constant, which is what an implementation over `ℤ` does when it clears denominators
— is not proved either; only the uniform rescaling of all values by one positive constant is.
Root counting *with* multiplicity is refused throughout: the fifth anchor is a
double root, its reading is `1`, and its multiplicity is exhibited separately so the refusal is
visible rather than silent.  The classical generalization that the chain counts roots *without*
multiplicity even for a non-squarefree chart (Basu–Pollack–Roy 2006, real algebraic geometry
algorithms) is cited to justify stating the open proposition without a squarefreeness hypothesis;
it is not proved here either.

Every theorem is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.Sturm

open Polynomial

/-! ## 1. The chart, its readings, and the polynomial it names

A **chart** is a coefficient list, lowest degree first: `[c₀, c₁, …, c_d]` names
`c₀ + c₁X + ⋯ + c_dX^d`.  Three readings of one chart are declared — at a rational point, at a
real point, and as an object of `Polynomial ℚ` — and they are proved to agree. -/

/-- The reading of a chart at a rational point, by nested multiplication (*Horner's rule*). -/
def evalAt (x : ℚ) : List ℚ → ℚ
  | [] => 0
  | c :: p => c + x * evalAt x p

/-- The reading of a chart at a **real** point.  The chart stays rational; only the point moves,
which is the whole reason the instrument can count real roots without leaving `ℚ`. -/
noncomputable def evalReal (x : ℝ) : List ℚ → ℝ
  | [] => 0
  | c :: p => (c : ℝ) + x * evalReal x p

/-- The chart as an object of `Polynomial ℚ`. -/
noncomputable def toPoly : List ℚ → Polynomial ℚ
  | [] => 0
  | c :: p => Polynomial.C c + Polynomial.X * toPoly p

/-- Trailing zero coefficients carry no degree; `trim` removes them. -/
def trim : List ℚ → List ℚ
  | [] => []
  | c :: p =>
    match trim p with
    | [] => if c = 0 then [] else [c]
    | d :: q => c :: d :: q

/-- The derivative's coefficients, from a starting exponent. -/
def derivFrom : ℕ → List ℚ → List ℚ
  | _, [] => []
  | k, c :: p => (k : ℚ) * c :: derivFrom (k + 1) p

/-- The derivative chart. -/
def derivChart (p : List ℚ) : List ℚ := trim (derivFrom 1 p.tail)

/-- Coefficientwise difference of two charts. -/
def subChart : List ℚ → List ℚ → List ℚ
  | [], [] => []
  | [], b :: q => (-b) :: subChart [] q
  | a :: p, [] => a :: subChart p []
  | a :: p, b :: q => (a - b) :: subChart p q

/-- Multiplication by `X^n`. -/
def shiftBy : ℕ → List ℚ → List ℚ
  | 0, p => p
  | n + 1, p => 0 :: shiftBy n p

/-- Multiplication by a scalar. -/
def scaleChart (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | d :: p => c * d :: scaleChart c p

/-- Negation of a chart. -/
def negChart (p : List ℚ) : List ℚ := scaleChart (-1) p

/-- The leading coefficient of a trimmed chart. -/
def leadOf : List ℚ → ℚ
  | [] => 0
  | [c] => c
  | _ :: c :: p => leadOf (c :: p)

/-- One long-division pass, driven by a fuel bound. -/
def remainderAux : ℕ → List ℚ → List ℚ → List ℚ
  | 0, a, _ => a
  | n + 1, a, b =>
      if a.length < b.length then a
      else
        remainderAux n
          (trim (subChart a (shiftBy (a.length - b.length)
            (scaleChart (leadOf a / leadOf b) b)))) b

/-- The Euclidean remainder of one chart by another. -/
def remainderOf : List ℚ → List ℚ → List ℚ
  | a, [] => trim a
  | a, b :: q => remainderAux (a.length + 1) (trim a) (b :: q)

/-- The tail of the chain: each entry is the **negated** remainder of its two predecessors. -/
def chainAux : ℕ → List ℚ → List ℚ → List (List ℚ)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | n + 1, a, b :: q => (b :: q) :: chainAux n (b :: q) (negChart (remainderOf a (b :: q)))

/-- The negated-remainder chain (*Sturm's chain*) at a declared fuel. -/
def remainderChainWith (fuel : ℕ) (p : List ℚ) : List (List ℚ) :=
  trim p :: chainAux fuel (trim p) (derivChart (trim p))

/-- The negated-remainder chain: the chart, its derivative, then negated remainders.  The fuel is
read off the material — the chart's own length — because degrees strictly decrease down a
remainder sequence. -/
def remainderChain (p : List ℚ) : List (List ℚ) := remainderChainWith (p.length + 1) p

/-- Sign variations along a list of values, continuing from a declared nonzero predecessor.
Zeros are **dropped**, never counted, which is the rule that lets a chain entry vanish at the
point without disturbing the reading. -/
def variationFrom (u : ℚ) : List ℚ → ℕ
  | [] => 0
  | v :: l => if v = 0 then variationFrom u l else (if u * v < 0 then 1 else 0) + variationFrom v l

/-- The sign-variation count of a list of values. -/
def variationCount : List ℚ → ℕ
  | [] => 0
  | v :: l => if v = 0 then variationCount l else variationFrom v l

/-- **The reading**: the sign-variation count of a chain evaluated at a rational point.  This is
the exact carrier of `sign_variations` in `crates/holonic-engine/src/exact_value.rs`. -/
def readingAt (ch : List (List ℚ)) (x : ℚ) : ℕ := variationCount (ch.map (evalAt x))

/-! ## 2. The laws of the instrument

None of these is about any particular chart.  They are what makes the reading a reading. -/

/-- **The reading peels one coefficient and defers the rest** (*Horner's recurrence*).
`rfl`-class: this proof is `rfl`. -/
theorem theReadingPeelsOneCoefficient (x c : ℚ) (p : List ℚ) :
    evalAt x (c :: p) = c + x * evalAt x p := rfl

/-- **The chain opens with the construction.**  `rfl`-class: this proof is `rfl`. -/
theorem theChainOpensWithTheConstruction (p : List ℚ) :
    (remainderChain p).head? = some (trim p) := rfl

/-- When the tail trims away entirely, the head survives exactly when it is nonzero. -/
theorem theTrimOfAVanishingTailIsTheHeadOrNothing {c : ℚ} {p : List ℚ} (hp : trim p = []) :
    trim (c :: p) = if c = 0 then [] else [c] := by rw [trim, hp]

/-- When the tail survives trimming, the head is kept whatever it is. -/
theorem theTrimOfASurvivingTailKeepsTheHead {c d : ℚ} {p q : List ℚ} (hp : trim p = d :: q) :
    trim (c :: p) = c :: d :: q := by rw [trim, hp]

/-- **Trimming does not move the reading.**  Deleting trailing zeros is a change of chart, not of
the object read; the coefficients removed contribute nothing at any point. -/
theorem theTrimPreservesTheReading (x : ℚ) : ∀ p : List ℚ, evalAt x (trim p) = evalAt x p := by
  intro p
  induction p with
  | nil => rfl
  | cons c p ih =>
    cases hp : trim p with
    | nil =>
      rw [hp] at ih
      rw [theTrimOfAVanishingTailIsTheHeadOrNothing hp]
      by_cases hc : c = 0
      · rw [if_pos hc, theReadingPeelsOneCoefficient x c p, ← ih, hc]
        simp only [evalAt]
        ring
      · rw [if_neg hc, theReadingPeelsOneCoefficient x c [], theReadingPeelsOneCoefficient x c p,
          ← ih]
    | cons d q =>
      rw [hp] at ih
      rw [theTrimOfASurvivingTailKeepsTheHead hp, theReadingPeelsOneCoefficient x c (d :: q),
        theReadingPeelsOneCoefficient x c p, ih]

/-- **Trimming is idempotent**: a trimmed chart is already normal. -/
theorem theTrimIsIdempotent : ∀ p : List ℚ, trim (trim p) = trim p := by
  intro p
  induction p with
  | nil => rfl
  | cons c p ih =>
    cases hp : trim p with
    | nil =>
      rw [theTrimOfAVanishingTailIsTheHeadOrNothing hp]
      by_cases hc : c = 0
      · rw [if_pos hc]; rfl
      · rw [if_neg hc, theTrimOfAVanishingTailIsTheHeadOrNothing (c := c) (p := ([] : List ℚ)) rfl,
          if_neg hc]
    | cons d q =>
      rw [hp] at ih
      rw [theTrimOfASurvivingTailKeepsTheHead hp, theTrimOfASurvivingTailKeepsTheHead ih]

/-- **A chart is the evaluation of the polynomial it names**, so every anchor below is a statement
about an object of `Polynomial ℚ` and not only about a list. -/
theorem theChartIsTheEvaluationOfItsPolynomial (x : ℚ) :
    ∀ p : List ℚ, (toPoly p).eval x = evalAt x p := by
  intro p
  induction p with
  | nil => simp [toPoly, evalAt]
  | cons c p ih => simp [toPoly, evalAt, ih]

/-- **The rational reading casts to the real reading**: one chart, two receivers, no drift. -/
theorem theRationalReadingCastsToTheRealReading (x : ℚ) :
    ∀ p : List ℚ, ((evalAt x p : ℚ) : ℝ) = evalReal (x : ℝ) p := by
  intro p
  induction p with
  | nil => simp [evalAt, evalReal]
  | cons c p ih => simp [evalAt, evalReal, ih]

/-- A blind value inside a value list is dropped by the continuing count. -/
theorem theBlindValueIsDroppedByTheContinuingCount (u : ℚ) :
    ∀ l₁ l₂ : List ℚ, variationFrom u (l₁ ++ (0 : ℚ) :: l₂) = variationFrom u (l₁ ++ l₂) := by
  intro l₁
  induction l₁ generalizing u with
  | nil => intro l₂; simp [variationFrom]
  | cons a l₁ ih =>
    intro l₂
    by_cases ha : a = 0
    · simp only [List.cons_append, variationFrom, if_pos ha]
      exact ih u l₂
    · simp only [List.cons_append, variationFrom, if_neg ha]
      rw [ih a l₂]

/-- A blind value inside a value list is dropped by the count. -/
theorem theBlindValueIsDroppedByTheCount :
    ∀ l₁ l₂ : List ℚ, variationCount (l₁ ++ (0 : ℚ) :: l₂) = variationCount (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂
    simp [variationCount]
  | cons a l₁ ih =>
    intro l₂
    simp only [List.cons_append, variationCount]
    by_cases ha : a = 0
    · rw [if_pos ha, if_pos ha]
      exact ih l₂
    · rw [if_neg ha, if_neg ha]
      exact theBlindValueIsDroppedByTheContinuingCount a l₁ l₂

/-- **An entry blind at the point is dropped by the reading, not counted.**  This is the law that
makes a chain entry vanishing at an endpoint harmless, and the third anchor exercises it with two
simultaneously blind entries. -/
theorem theBlindEntryIsDroppedByTheReading (ch₁ ch₂ : List (List ℚ)) (q : List ℚ) (x : ℚ)
    (hq : evalAt x q = 0) :
    readingAt (ch₁ ++ q :: ch₂) x = readingAt (ch₁ ++ ch₂) x := by
  simp only [readingAt, List.map_append, List.map_cons, hq]
  exact theBlindValueIsDroppedByTheCount _ _

/-- Positive rescaling of the values does not move the continuing count. -/
theorem theContinuingCountIsInvariantUnderPositiveRescaling {c : ℚ} (hc : 0 < c) :
    ∀ (u : ℚ) (l : List ℚ),
      variationFrom (c * u) (l.map (fun v => c * v)) = variationFrom u l := by
  intro u l
  induction l generalizing u with
  | nil => simp [variationFrom]
  | cons v l ih =>
    simp only [List.map_cons, variationFrom]
    by_cases hv : v = 0
    · have hcv : c * v = 0 := by rw [hv, mul_zero]
      rw [if_pos hcv, if_pos hv]
      exact ih u
    · have hcv : c * v ≠ 0 := mul_ne_zero (ne_of_gt hc) hv
      have hc2 : (0 : ℚ) < c ^ 2 := by positivity
      have hprod : (c * u) * (c * v) = c ^ 2 * (u * v) := by ring
      have hsign : (c * u) * (c * v) < 0 ↔ u * v < 0 := by
        rw [hprod]
        constructor
        · intro h
          by_contra hcon
          push_neg at hcon
          exact absurd h (not_lt.mpr (mul_nonneg (le_of_lt hc2) hcon))
        · intro h
          exact mul_neg_of_pos_of_neg hc2 h
      rw [if_neg hv, if_neg hcv, ih v]
      by_cases hs : u * v < 0
      · rw [if_pos (hsign.mpr hs), if_pos hs]
      · rw [if_neg (fun h => hs (hsign.mp h)), if_neg hs]

/-- **The reading is invariant under positive rescaling of the values.**  Multiplying every value
by one positive rational leaves the reading exactly where it was: the reading sees the sign
pattern and nothing else, so a common positive factor is gauge.  Nothing here licenses a
*negative* rescaling, which is a genuine change of hand; and the **per-entry** gauge — rescaling
each chain entry by its own positive constant, which is what clearing denominators does — is
**not proved here** and is named in the boundary. -/
theorem theReadingIsInvariantUnderPositiveRescaling {c : ℚ} (hc : 0 < c) :
    ∀ l : List ℚ, variationCount (l.map (fun v => c * v)) = variationCount l := by
  intro l
  induction l with
  | nil => simp only [List.map_nil]
  | cons v l ih =>
    simp only [List.map_cons, variationCount]
    by_cases hv : v = 0
    · have hcv : c * v = 0 := by rw [hv, mul_zero]
      rw [if_pos hcv, if_pos hv]
      exact ih
    · have hcv : c * v ≠ 0 := mul_ne_zero (ne_of_gt hc) hv
      rw [if_neg hcv, if_neg hv]
      exact theContinuingCountIsInvariantUnderPositiveRescaling hc v l

/-- The continuing count never exceeds the length of what it reads. -/
theorem theContinuingCountNeverExceedsItsLength :
    ∀ (u : ℚ) (l : List ℚ), variationFrom u l ≤ l.length := by
  intro u l
  induction l generalizing u with
  | nil => simp [variationFrom]
  | cons v l ih =>
    by_cases hv : v = 0
    · simp only [variationFrom, if_pos hv, List.length_cons]
      exact le_trans (ih u) (Nat.le_succ _)
    · simp only [variationFrom, if_neg hv, List.length_cons]
      have h := ih v
      split <;> omega

/-- The count never exceeds the length of what it reads. -/
theorem theCountNeverExceedsItsLength : ∀ l : List ℚ, variationCount l ≤ l.length := by
  intro l
  induction l with
  | nil => simp only [variationCount, List.length_nil, le_refl]
  | cons v l ih =>
    simp only [variationCount, List.length_cons]
    by_cases hv : v = 0
    · rw [if_pos hv]; omega
    · rw [if_neg hv]
      exact le_trans (theContinuingCountNeverExceedsItsLength v l) (Nat.le_succ _)

/-- **The reading never exceeds the chain length.**  A reading is bounded by the material it
reads; nothing about a window can make the count exceed the number of entries. -/
theorem theReadingNeverExceedsTheChainLength (ch : List (List ℚ)) (x : ℚ) :
    readingAt ch x ≤ ch.length := by
  have h := theCountNeverExceedsItsLength (ch.map (evalAt x))
  rwa [List.length_map] at h

/-- **The chain carries no empty entry after its head.**  The recursion halts exactly when the
next entry would be the zero chart, so every entry it emits is a genuine polynomial — the
condition an implementation needs before it may call the last entry a greatest common divisor. -/
theorem theChainCarriesNoEmptyEntryAfterItsHead :
    ∀ (n : ℕ) (a b : List ℚ), ∀ q ∈ chainAux n a b, q ≠ [] := by
  intro n
  induction n with
  | zero => intro a b q hq; simp [chainAux] at hq
  | succ n ih =>
    intro a b q hq
    cases b with
    | nil => simp [chainAux] at hq
    | cons d r =>
      simp only [chainAux, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.cons_ne_nil d r
      · exact ih _ _ q hq

/-- **A root shared by two consecutive entries descends the division tower.**  If `P = T·Q − R`
and a point kills `P` and `Q`, it kills `R`.  Running this down an exhibited chain to a nonzero
constant is exactly how adjacent entries are shown to share no root — the non-degeneracy the
counting law rests on. -/
theorem theCommonRootDescendsTheDivisionTower (P Q R T : Polynomial ℝ) (h : P = T * Q - R)
    (x : ℝ) (hP : P.eval x = 0) (hQ : Q.eval x = 0) : R.eval x = 0 := by
  have hev := congrArg (Polynomial.eval x) h
  rw [hP] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, hQ, mul_zero, zero_sub] at hev
  linarith

/-! ## 3. The charts

Five charts, each with its window or windows.  All coefficients are exact rationals; the third is
the terrain of `crates/holonic-engine/src/winding_inertia.rs`. -/

/-- `X² − 2`: one irrational root above one, the isolation certificate's own example. -/
def squareLessTwoChart : List ℚ := [-2, 0, 1]

/-- `X³ − X`: three rational roots, used to show the reading localises. -/
def cubeLessLineChart : List ℚ := [0, -1, 0, 1]

/-- `X⁴ − 5X² + 4`: the squarefree part of the hexagon's `D₆(x) − 2` (the Dickson polynomial with
`D_n(z + z⁻¹) = zⁿ + z⁻ⁿ`), whose roots `2, 1, −1, −2` are the star values `β_m = ω^m + ω^{−m}`
at `n = 6`.  This is `winding_inertia.rs`'s own material. -/
def starHexagonChart : List ℚ := [4, 0, -5, 0, 1]

/-- `X² − 2X + 2`: no real root at all, and the control that separates a bound from a count. -/
def rootlessChart : List ℚ := [2, -2, 1]

/-- `(X − 1)²`: one root of multiplicity two, the control on what the reading refuses to see. -/
def doubleRootChart : List ℚ := [1, -2, 1]

/-- The real chart of `X² − 2`. -/
theorem theSquareLessTwoChartIsTheSquareLessTwo (x : ℝ) :
    evalReal x squareLessTwoChart = x ^ 2 - 2 := by
  simp only [squareLessTwoChart, evalReal]; push_cast; ring

/-- The real chart of `X³ − X`. -/
theorem theCubeLessLineChartIsTheCubeLessTheLine (x : ℝ) :
    evalReal x cubeLessLineChart = x ^ 3 - x := by
  simp only [cubeLessLineChart, evalReal]; push_cast; ring

/-- The real chart of the star polynomial: the squarefree part of `D₆(x) − 2` (*the Dickson
polynomial*), read at a real point. -/
theorem theStarHexagonChartIsTheRealQuartic (x : ℝ) :
    evalReal x starHexagonChart = x ^ 4 - 5 * x ^ 2 + 4 := by
  simp only [starHexagonChart, evalReal]; push_cast; ring

/-- The real chart of the rootless control. -/
theorem theRootlessChartIsTheShiftedSquare (x : ℝ) :
    evalReal x rootlessChart = (x - 1) ^ 2 + 1 := by
  simp only [rootlessChart, evalReal]; push_cast; ring

/-- The real chart of the double root, **with its multiplicity exhibited**. -/
theorem theDoubleRootChartIsASquare (x : ℝ) :
    evalReal x doubleRootChart = (x - 1) ^ 2 := by
  simp only [doubleRootChart, evalReal]; push_cast; ring

/-- **The star chart names the polynomial `X⁴ − 5X² + 4` in `Polynomial ℚ`**, so the anchors below
are statements about an object of `ℚ[X]` and not only about a coefficient list. -/
theorem theStarHexagonPolynomialIsTheQuarticLessFiveSquaresPlusFour :
    toPoly starHexagonChart = X ^ 4 - C 5 * X ^ 2 + C 4 := by
  apply Polynomial.funext
  intro r
  simp only [starHexagonChart, toPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_zero]
  ring

/-! ## 4. The chains, computed

Each chain is the instrument's own return, proved equal to an explicit list.  Each was recomputed
independently in exact rational arithmetic before being written down. -/

attribute [local simp] evalAt trim derivFrom derivChart subChart shiftBy scaleChart negChart
  leadOf remainderAux remainderOf chainAux remainderChainWith remainderChain variationFrom
  variationCount readingAt

set_option maxRecDepth 8000

/-- The chain of `X² − 2` is three entries: the chart, `2X`, and the constant `2`. -/
theorem theSquareLessTwoChainIsThreeEntries :
    remainderChain squareLessTwoChart = [[-2, 0, 1], [0, 2], [2]] := by
  norm_num [squareLessTwoChart]

/-- The chain of `X³ − X` is four entries, ending in the constant `1`. -/
theorem theCubeLessLineChainIsFourEntries :
    remainderChain cubeLessLineChart = [[0, -1, 0, 1], [-1, 0, 3], [0, 2 / 3], [1]] := by
  norm_num [cubeLessLineChart]

/-- The chain of the star polynomial is five entries, ending in the constant `4`. -/
theorem theStarHexagonChainIsFiveEntries :
    remainderChain starHexagonChart =
      [[4, 0, -5, 0, 1], [0, -10, 0, 4], [-4, 0, 5 / 2], [0, 18 / 5], [4]] := by
  norm_num [starHexagonChart]

/-- The chain of the rootless control is three entries, ending in the constant `−1`. -/
theorem theRootlessChainIsThreeEntries :
    remainderChain rootlessChart = [[2, -2, 1], [-2, 2], [-1]] := by
  norm_num [rootlessChart]

/-- **The double root's chain stops at the common factor.**  The remainder is exactly zero one
step early, so the chain has only two entries and its last entry `2X − 2` is a constant multiple
of `gcd(p, p')`.  That is why the reading below counts the root once and not twice. -/
theorem theDoubleRootChainStopsAtTheCommonFactor :
    remainderChain doubleRootChart = [[1, -2, 1], [-2, 2]] := by
  norm_num [doubleRootChart]

/-- **The fuel is an aperture that does not select.**  Every chain above is unchanged when the
recursion is given a fuel far in excess of the one the instrument reads off the chart, so the
bound is not deciding any answer. -/
theorem theFuelIsAnApertureThatDoesNotSelect :
    remainderChainWith 40 squareLessTwoChart = remainderChain squareLessTwoChart ∧
    remainderChainWith 40 cubeLessLineChart = remainderChain cubeLessLineChart ∧
    remainderChainWith 40 starHexagonChart = remainderChain starHexagonChart ∧
    remainderChainWith 40 rootlessChart = remainderChain rootlessChart ∧
    remainderChainWith 40 doubleRootChart = remainderChain doubleRootChart := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [squareLessTwoChart]
  · norm_num [cubeLessLineChart]
  · norm_num [starHexagonChart]
  · norm_num [rootlessChart]
  · norm_num [doubleRootChart]

/-! ## 5. The readings

The reading at each declared endpoint, and the difference across each window.  The difference is
stated additively — `reading at the lower endpoint = reading at the upper endpoint + n` — so no
truncated natural subtraction can hide a defect, which is exactly the refusal
`InvalidSturmOrientation` in `crates/holonic-engine/src/exact_value.rs`. -/

/-- `X² − 2` across `(1, 2)`: the reading counts **one** passage. -/
theorem theSquareLessTwoReadingCountsOnePassageAboveOne :
    readingAt (remainderChain squareLessTwoChart) 1
      = readingAt (remainderChain squareLessTwoChart) 2 + 1 := by
  rw [theSquareLessTwoChainIsThreeEntries]; norm_num

/-- `X² − 2` across `(−2, −1)`: the reading counts **one** passage on the other side, and the
endpoint readings are `2` and `1` — nonzero on both sides, so the count is a difference and never
an absolute level. -/
theorem theSquareLessTwoReadingCountsOnePassageBelowMinusOne :
    readingAt (remainderChain squareLessTwoChart) (-2) = 2 ∧
    readingAt (remainderChain squareLessTwoChart) (-1) = 1 ∧
    readingAt (remainderChain squareLessTwoChart) (-2)
      = readingAt (remainderChain squareLessTwoChart) (-1) + 1 := by
  rw [theSquareLessTwoChainIsThreeEntries]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- `X² − 2` across `(2, 3)`: the reading counts **nothing**, and the window is genuinely empty. -/
theorem theSquareLessTwoReadingCountsNothingAboveTwo :
    readingAt (remainderChain squareLessTwoChart) 2
      = readingAt (remainderChain squareLessTwoChart) 3 + 0 := by
  rw [theSquareLessTwoChainIsThreeEntries]; norm_num

/-- `X³ − X` across `(−2, 2)`: the reading counts **three** passages. -/
theorem theCubeLessLineReadingCountsThreePassages :
    readingAt (remainderChain cubeLessLineChart) (-2)
      = readingAt (remainderChain cubeLessLineChart) 2 + 3 := by
  rw [theCubeLessLineChainIsFourEntries]; norm_num

/-- `X³ − X` across `(−1/2, 3/2)`: the same chain, a narrower window, and the reading **localises**
to two passages.  The chain is a property of the chart; the count is a property of the window. -/
theorem theCubeLessLineReadingLocalisesToTwoPassages :
    readingAt (remainderChain cubeLessLineChart) (-1 / 2)
      = readingAt (remainderChain cubeLessLineChart) (3 / 2) + 2 := by
  rw [theCubeLessLineChainIsFourEntries]; norm_num

/-- The star polynomial across `(−3, 3)`: the reading counts **four** passages — the four star
values of the hexagon. -/
theorem theStarHexagonReadingCountsFourPassages :
    readingAt (remainderChain starHexagonChart) (-3)
      = readingAt (remainderChain starHexagonChart) 3 + 4 := by
  rw [theStarHexagonChainIsFiveEntries]; norm_num

/-- **The star polynomial across `(0, 3)`, where two chain entries are blind at the lower
endpoint.**  At `x = 0` the second and fourth entries both evaluate to zero; they are dropped, the
surviving values are `4, −4, 4`, and the reading is `2`.  This is
`theBlindEntryIsDroppedByTheReading` exercised on real material rather than asserted. -/
theorem theStarHexagonReadingDropsItsBlindEntries :
    readingAt (remainderChain starHexagonChart) 0
      = readingAt (remainderChain starHexagonChart) 3 + 2 := by
  rw [theStarHexagonChainIsFiveEntries]; norm_num

/-- The rootless control across `(−5, 5)`: the endpoint readings are **both `1`**, so the
difference is zero.  A nonzero variation count at a point says nothing at all about roots; only
the change across a window does. -/
theorem theRootlessReadingCountsNoPassage :
    readingAt (remainderChain rootlessChart) (-5) = 1 ∧
    readingAt (remainderChain rootlessChart) 5 = 1 ∧
    readingAt (remainderChain rootlessChart) (-5)
      = readingAt (remainderChain rootlessChart) 5 + 0 := by
  rw [theRootlessChainIsThreeEntries]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The double root across `(0, 2)`: the reading counts **one** passage, not two. -/
theorem theDoubleRootReadingCountsOnePassage :
    readingAt (remainderChain doubleRootChart) 0
      = readingAt (remainderChain doubleRootChart) 2 + 1 := by
  rw [theDoubleRootChainStopsAtTheCommonFactor]; norm_num

/-! ## 6. The populations

The realized real-root population inside each window, as a set of real points with its exact
cardinality.  Every number here matches the reading above. -/

/-- **The population of `X² − 2` in `(1, 2)` is the single point `√2`.**  The reading counted one;
the population is one, and it is exhibited rather than summarized. -/
theorem theSquareLessTwoPopulationAboveOneIsOnePoint :
    (1 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 2 ∧
      {x : ℝ | evalReal x squareLessTwoChart = 0 ∧ (1 : ℝ) < x ∧ x < 2} = {Real.sqrt 2} ∧
      ({Real.sqrt 2} : Set ℝ).ncard = 1 := by
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have h2 : Real.sqrt 2 < 2 := by nlinarith
  refine ⟨h1, h2, ?_, Set.ncard_singleton _⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, theSquareLessTwoChartIsTheSquareLessTwo]
  constructor
  · rintro ⟨hx, hlo, _⟩
    have hfac : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · linarith
  · rintro rfl
    exact ⟨by nlinarith, h1, h2⟩

/-- **The population of `X² − 2` in `(−2, −1)` is the single point `−√2`.**  The reading counted
one there too, from endpoint readings that were both nonzero. -/
theorem theSquareLessTwoPopulationBelowMinusOneIsOnePoint :
    (-2 : ℝ) < -Real.sqrt 2 ∧ -Real.sqrt 2 < -1 ∧
      {x : ℝ | evalReal x squareLessTwoChart = 0 ∧ (-2 : ℝ) < x ∧ x < -1} = {-Real.sqrt 2} ∧
      ({-Real.sqrt 2} : Set ℝ).ncard = 1 := by
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have h2 : Real.sqrt 2 < 2 := by nlinarith
  refine ⟨by linarith, by linarith, ?_, Set.ncard_singleton _⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, theSquareLessTwoChartIsTheSquareLessTwo]
  constructor
  · rintro ⟨hx, _, hhi⟩
    have hfac : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · linarith
  · rintro rfl
    exact ⟨by nlinarith, by linarith, by linarith⟩

/-- **The population of `X² − 2` in `(2, 3)` is empty**, and the reading counted nothing there —
a window of the very same chart on which the instrument returns zero. -/
theorem theSquareLessTwoPopulationAboveTwoIsEmpty :
    {x : ℝ | evalReal x squareLessTwoChart = 0 ∧ (2 : ℝ) < x ∧ x < 3} = ∅ ∧
      (∅ : Set ℝ).ncard = 0 := by
  refine ⟨?_, Set.ncard_empty ℝ⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
    theSquareLessTwoChartIsTheSquareLessTwo]
  intro hx hlo hhi
  nlinarith [hx, hlo]

/-- **The population of `X³ − X` in `(−2, 2)` is three points.**  The reading counted three. -/
theorem theCubeLessLinePopulationIsThreePoints :
    {x : ℝ | evalReal x cubeLessLineChart = 0 ∧ (-2 : ℝ) < x ∧ x < 2} = {-1, 0, 1} ∧
      ({-1, 0, 1} : Set ℝ).ncard = 3 := by
  constructor
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      theCubeLessLineChartIsTheCubeLessTheLine]
    constructor
    · rintro ⟨hx, _, _⟩
      have hfac : (x + 1) * x * (x - 1) = 0 := by linear_combination hx
      rcases mul_eq_zero.mp hfac with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (by linarith))
    · rintro (rfl | rfl | rfl) <;> norm_num
  · rw [Set.ncard_insert_of_notMem (by norm_num), Set.ncard_insert_of_notMem (by norm_num),
      Set.ncard_singleton]

/-- **The population of `X³ − X` in `(−1/2, 3/2)` is two points.**  The reading localised to
two: the same chain, a smaller window, and the population shrinks with it. -/
theorem theCubeLessLineLocalPopulationIsTwoPoints :
    {x : ℝ | evalReal x cubeLessLineChart = 0 ∧ (-1 / 2 : ℝ) < x ∧ x < 3 / 2} = {0, 1} ∧
      ({0, 1} : Set ℝ).ncard = 2 := by
  constructor
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      theCubeLessLineChartIsTheCubeLessTheLine]
    constructor
    · rintro ⟨hx, hlo, hhi⟩
      have hfac : (x + 1) * x * (x - 1) = 0 := by linear_combination hx
      rcases mul_eq_zero.mp hfac with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exfalso; linarith
        · exact Or.inl h'
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> norm_num
  · exact Set.ncard_pair (by norm_num)

/-- **The population of the star polynomial in `(−3, 3)` is the four star values.**  The reading
counted four; the population is `{−2, −1, 1, 2}`, which is `β_m = ω^m + ω^{−m}` at `n = 6`. -/
theorem theStarHexagonPopulationIsFourPoints :
    {x : ℝ | evalReal x starHexagonChart = 0 ∧ (-3 : ℝ) < x ∧ x < 3} = {-2, -1, 1, 2} ∧
      ({-2, -1, 1, 2} : Set ℝ).ncard = 4 := by
  constructor
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      theStarHexagonChartIsTheRealQuartic]
    constructor
    · rintro ⟨hx, _, _⟩
      have hfac : (x + 2) * (x + 1) * (x - 1) * (x - 2) = 0 := by linear_combination hx
      rcases mul_eq_zero.mp hfac with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl (by linarith)
          · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (Or.inl (by linarith)))
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
    · rintro (rfl | rfl | rfl | rfl) <;> norm_num
  · rw [Set.ncard_insert_of_notMem (by norm_num), Set.ncard_insert_of_notMem (by norm_num),
      Set.ncard_pair (by norm_num)]

/-- **The population of the star polynomial in `(0, 3)` is two points.**  The window where two
chain entries went blind is the one where the reading returned two, and the population is `{1, 2}`. -/
theorem theStarHexagonPopulationAboveZeroIsTwoPoints :
    {x : ℝ | evalReal x starHexagonChart = 0 ∧ (0 : ℝ) < x ∧ x < 3} = {1, 2} ∧
      ({1, 2} : Set ℝ).ncard = 2 := by
  constructor
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      theStarHexagonChartIsTheRealQuartic]
    constructor
    · rintro ⟨hx, hlo, _⟩
      have hfac : (x + 2) * (x + 1) * (x - 1) * (x - 2) = 0 := by linear_combination hx
      rcases mul_eq_zero.mp hfac with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exfalso; linarith
          · exfalso; linarith
        · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> norm_num
  · exact Set.ncard_pair (by norm_num)

/-- **The population of the rootless control is empty**, everywhere and not merely in the
window. -/
theorem theRootlessPopulationIsEmpty :
    (∀ x : ℝ, evalReal x rootlessChart ≠ 0) ∧
      {x : ℝ | evalReal x rootlessChart = 0 ∧ (-5 : ℝ) < x ∧ x < 5} = ∅ ∧
      (∅ : Set ℝ).ncard = 0 := by
  have hpos : ∀ x : ℝ, evalReal x rootlessChart ≠ 0 := by
    intro x
    rw [theRootlessChartIsTheShiftedSquare]
    nlinarith [sq_nonneg (x - 1)]
  refine ⟨hpos, ?_, Set.ncard_empty ℝ⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h
  exact absurd h (hpos x)

/-- **The population of the double root in `(0, 2)` is one point of multiplicity two.**  The
reading counted `1`; the population as a *set* is `{1}`; and the multiplicity is exhibited by the
factorization so that what the reading refuses to see is visible rather than silent.  Sturm's
chain counts **distinct** roots, and this is the material on which that distinction is real. -/
theorem theDoubleRootPopulationIsOnePointOfMultiplicityTwo :
    {x : ℝ | evalReal x doubleRootChart = 0 ∧ (0 : ℝ) < x ∧ x < 2} = {1} ∧
      ({1} : Set ℝ).ncard = 1 ∧
      (∀ x : ℝ, evalReal x doubleRootChart = (x - 1) ^ 2) := by
  refine ⟨?_, Set.ncard_singleton _, theDoubleRootChartIsASquare⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, theDoubleRootChartIsASquare]
  constructor
  · rintro ⟨hx, _, _⟩
    have : (x - 1) = 0 := by nlinarith [sq_nonneg (x - 1)]
    linarith
  · rintro rfl
    norm_num

/-! ## 7. What the chain is, and what the coefficient reading is not -/

/-- **The star chain is an exact division tower.**  Each entry is the previous pair's negated
Euclidean remainder, exhibited as an identity in exact rationals: `p₀ = (X/4)·p₁ − p₂`,
`p₁ = (8X/5)·p₂ − p₃`, `p₂ = (25X/36)·p₃ − p₄`.  Over the infinite field `ℚ` a functional identity
is a polynomial identity, so these are identities in `ℚ[X]`.  This is *why* the chain works, and
it is what `theCommonRootDescendsTheDivisionTower` consumes. -/
theorem theStarHexagonChainIsADivisionTower (x : ℚ) :
    evalAt x [4, 0, -5, 0, 1] = (x / 4) * evalAt x [0, -10, 0, 4] - evalAt x [-4, 0, 5 / 2] ∧
    evalAt x [0, -10, 0, 4] = (8 * x / 5) * evalAt x [-4, 0, 5 / 2] - evalAt x [0, 18 / 5] ∧
    evalAt x [-4, 0, 5 / 2] = (25 * x / 36) * evalAt x [0, 18 / 5] - evalAt x [4] := by
  refine ⟨by norm_num; ring, by norm_num; ring, by norm_num; ring⟩

/-- **The square-less-two chain is an exact division tower**: `p₀ = (X/2)·p₁ − p₂`, after which
the remainder is zero and the chain halts on the nonzero constant `2`. -/
theorem theSquareLessTwoChainIsADivisionTower (x : ℚ) :
    evalAt x [-2, 0, 1] = (x / 2) * evalAt x [0, 2] - evalAt x [2] := by
  norm_num; ring

/-- **The rootless chain is an exact division tower**: `p₀ = ((X−1)/2)·p₁ − p₂` with `p₂` the
constant `−1`, so this chain too halts on a nonzero constant. -/
theorem theRootlessChainIsADivisionTower (x : ℚ) :
    evalAt x [2, -2, 1] = ((x - 1) / 2) * evalAt x [-2, 2] - evalAt x [-1] := by
  norm_num; ring

/-- **The cube-less-line chain is an exact division tower** too: `p₀ = (X/3)·p₁ − p₂` and
`p₁ = (9X/2)·p₂ − p₃`. -/
theorem theCubeLessLineChainIsADivisionTower (x : ℚ) :
    evalAt x [0, -1, 0, 1] = (x / 3) * evalAt x [-1, 0, 3] - evalAt x [0, 2 / 3] ∧
    evalAt x [-1, 0, 3] = (9 * x / 2) * evalAt x [0, 2 / 3] - evalAt x [1] := by
  refine ⟨by norm_num; ring, by norm_num; ring⟩

/-- **The double root's last chain entry divides the chart exactly.**  `(X − 1)² = ((X−1)/2)·(2X − 2)`,
which is the greatest-common-divisor condition: the chain halted because the remainder was zero,
and the last entry is a constant multiple of `gcd(p, p')`. -/
theorem theDoubleRootLastEntryDividesTheChart (x : ℚ) :
    evalAt x [1, -2, 1] = ((x - 1) / 2) * evalAt x [-2, 2] := by
  norm_num; ring

/-- **Adjacent entries of the star chain share no real root.**  A common root of the chart and its
derivative would descend the tower to the constant `4`, which vanishes nowhere.  This is the
non-degeneracy condition, proved on this chart rather than asserted in general. -/
theorem theStarHexagonAdjacentEntriesShareNoRealRoot (x : ℝ) :
    ¬(evalReal x starHexagonChart = 0 ∧ evalReal x [0, -10, 0, 4] = 0) := by
  rintro ⟨h0, h1⟩
  rw [theStarHexagonChartIsTheRealQuartic] at h0
  have h1' : 4 * x ^ 3 - 10 * x = 0 := by
    simp only [evalReal] at h1; push_cast at h1; linarith [h1]
  have hx2 : x ^ 2 = 8 / 5 := by linear_combination (-2 / 5 : ℝ) * h0 + (x / 10) * h1'
  have hx : x = 0 := by linear_combination (-5 / 18 : ℝ) * h1' + (10 / 9 * x) * hx2
  rw [hx] at hx2
  norm_num at hx2

/-- **The coefficient reading bounds where the chain reading counts.**  On `X² − 2X + 2` the very
same sign-variation instrument, applied to the **coefficient list** read from the top degree down,
returns `2` — the bound of Descartes' rule of signs (Descartes 1637), which Mathlib owns as
`Polynomial.roots_countP_pos_le_signVariations`.  The chain reading across `(−5, 5)` returns `0`,
and the real population is empty.  **Two against zero is the whole distance between a bound and a
population**, and it is why this instrument is not a restatement of the one Mathlib already has. -/
theorem theCoefficientReadingBoundsWhereTheChainReadingCounts :
    variationCount (rootlessChart.reverse) = 2 ∧
      readingAt (remainderChain rootlessChart) (-5)
        = readingAt (remainderChain rootlessChart) 5 + 0 ∧
      {x : ℝ | evalReal x rootlessChart = 0 ∧ (-5 : ℝ) < x ∧ x < 5} = ∅ := by
  refine ⟨by norm_num [rootlessChart], ?_, (theRootlessPopulationIsEmpty).2.1⟩
  rw [theRootlessChainIsThreeEntries]; norm_num

/-! ## 8. Sturm's theorem, named open

The general law is not proved here.  It is stated in full, over real roots in a window with
rational endpoints, and it is assumed nowhere. -/

/-- The realized real-root population of a chart inside an open window with rational endpoints. -/
noncomputable def realPopulation (p : List ℚ) (a b : ℚ) : Set ℝ :=
  {x : ℝ | evalReal x p = 0 ∧ (a : ℝ) < x ∧ x < (b : ℝ)}

/-- **`TheReadingEqualsThePopulation` — Sturm's theorem over the rationals, NAMED OPEN.**

For a nonzero chart and a window whose endpoints are not themselves roots, the sign-variation
reading of the negated-remainder chain at the lower endpoint equals the reading at the upper
endpoint plus the number of **distinct** real roots strictly inside the window.

No squarefreeness hypothesis appears, and that is deliberate: the classical statement counts roots
without multiplicity for any nonzero chart, because the chain is the squarefree chain multiplied
through by `gcd(p, p')` (Sturm 1829; the without-multiplicity form as in Basu–Pollack–Roy 2006).
The fifth anchor above is precisely a non-squarefree instance where the reading and the distinct
population both equal `1`.

This proposition is **not proved in this file and is not assumed by any theorem in it.** -/
def TheReadingEqualsThePopulation : Prop :=
  ∀ (p : List ℚ) (a b : ℚ), a < b → trim p ≠ [] →
    evalAt a p ≠ 0 → evalAt b p ≠ 0 →
      readingAt (remainderChain p) a
        = readingAt (remainderChain p) b + (realPopulation p a b).ncard

/-- **The open proposition's hypotheses are live**, exhibited on `X² − 2` and `(1, 2)`: the window
is oriented, the chart is nonzero, and neither endpoint is a root.  A named-open statement whose
hypotheses nothing satisfies would carry nothing. -/
theorem theOpenLawHasLiveHypotheses :
    (1 : ℚ) < 2 ∧ trim squareLessTwoChart ≠ [] ∧
      evalAt 1 squareLessTwoChart ≠ 0 ∧ evalAt 2 squareLessTwoChart ≠ 0 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · simp [squareLessTwoChart]
  · norm_num [squareLessTwoChart]
  · norm_num [squareLessTwoChart]

/-- **The endpoint condition is a real restriction and it can fail.**  On `X³ − X` the endpoint
`0` *is* a root, so the open proposition says nothing about the window `(0, 2)` — the refusal
`RootAtIntervalBoundary` in `crates/holonic-engine/src/exact_value.rs`, as a fact about this
material rather than a defensive branch. -/
theorem theEndpointConditionCanFail : evalAt 0 cubeLessLineChart = 0 := by
  norm_num [cubeLessLineChart]

/-- **What the open proposition would buy, exhibited.**  Granted the general law, the star
polynomial's population inside `(−3, 3)` is forced to be exactly four — which is independently
proved above.  The two routes agreeing is the point: the reading is proved, the population is
proved, and the open law is exactly the bridge that would make the first *entail* the second in
general rather than instance by instance. -/
theorem theOpenLawWouldDischargeTheStarWindow (h : TheReadingEqualsThePopulation) :
    (realPopulation starHexagonChart (-3) 3).ncard = 4 := by
  have hchart : trim starHexagonChart ≠ [] := by simp [starHexagonChart]
  have hlo : evalAt (-3) starHexagonChart ≠ 0 := by norm_num [starHexagonChart]
  have hhi : evalAt 3 starHexagonChart ≠ 0 := by norm_num [starHexagonChart]
  have hlaw := h starHexagonChart (-3) 3 (by norm_num) hchart hlo hhi
  have hread := theStarHexagonReadingCountsFourPassages
  omega

end Soma.Holonics.Millennium.Sturm
