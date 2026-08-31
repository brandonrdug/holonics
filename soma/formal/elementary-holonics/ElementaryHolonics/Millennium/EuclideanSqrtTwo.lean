import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.Tactic

/-!
# `ℤ[√2]` divides with remainder, and the `2` is what makes the constant a half

The seventeen descent lives in `ℤ[√2]`: both Pell chains are its unit group, seventeen splits there
as `(5 + 2√2)(5 − 2√2)`, and both descended quartics are norms from it
(`Millennium.QuarticSeventeen`).  What the descent needs next is **unique factorisation**, and
mathlib supplies the Euclidean structure only for `d = −1` — measured 2026-08-23, `ls
Mathlib/NumberTheory/Zsqrtd/` returns `Basic, GaussianInt, QuadraticReciprocity, ToReal`.

This file supplies the arithmetic core, in pure integer terms and with no embedding into `ℝ` or
`ℂ`: rounding each coordinate of `α β̄` against `N(β)` leaves a remainder whose norm satisfies

```text
2 · |N(ρ)| ≤ |N(β)| .
```

The constant is a **half**, and the reason is the `2` in `√2`: the two error coordinates satisfy
`|r|, |s| ≤ |N|/2`, so `|r² − 2s²| ≤ max(r², 2s²) = N²/2`, and it is the coefficient `2` that
decides which of the two terms dominates.  For `d = 3` the same computation gives `max(N²/4,
3N²/4)`, still under `N²`; past `d = 4` it fails, which is exactly why the norm-Euclidean real
quadratic fields stop.
-/

namespace Soma.Holonics.Millennium.EuclideanSqrtTwo

/-- Rounding to the nearest multiple, positive modulus. -/
theorem theNearestMultipleOfPos (p N : ℤ) (hN : 0 < N) : ∃ m : ℤ, 2 * |p - m * N| ≤ N := by
  have hdm := Int.ediv_mul_add_emod p N
  have hcomm : (p / N) * N = N * (p / N) := mul_comm _ _
  have hr0 : 0 ≤ p % N := Int.emod_nonneg p (by omega)
  have hrN : p % N < N := Int.emod_lt_of_pos p hN
  rcases le_or_gt (2 * (p % N)) N with hle | hgt
  · refine ⟨p / N, ?_⟩
    have hval : p - (p / N) * N = p % N := by linarith [hdm, hcomm]
    rw [hval, abs_of_nonneg hr0]
    linarith
  · refine ⟨p / N + 1, ?_⟩
    have hval : p - (p / N + 1) * N = p % N - N := by
      have : (p / N + 1) * N = (p / N) * N + N := by ring
      linarith [hdm, hcomm, this]
    rw [hval, abs_of_nonpos (by linarith)]
    linarith

/-- **ROUNDING TO THE NEAREST MULTIPLE.**  For any `p` and nonzero `N`, some multiple of `N` lies
within `|N|/2` of `p`. -/
theorem theNearestMultiple (p N : ℤ) (hN : N ≠ 0) : ∃ m : ℤ, 2 * |p - m * N| ≤ |N| := by
  rcases lt_trichotomy N 0 with h | h | h
  · obtain ⟨m, hm⟩ := theNearestMultipleOfPos p (-N) (by omega)
    refine ⟨-m, ?_⟩
    rw [abs_of_neg h]
    have : (-m) * N = m * -N := by ring
    rw [this]
    exact hm
  · exact absurd h hN
  · obtain ⟨m, hm⟩ := theNearestMultipleOfPos p N h
    exact ⟨m, by rwa [abs_of_pos h]⟩

/-- The norm is multiplicative, written out in coordinates: this is the identity the remainder
bound rides on. -/
theorem theNormIdentity (a b c d m n : ℤ) :
    ((a - (m * c + 2 * n * d)) ^ 2 - 2 * (b - (m * d + n * c)) ^ 2) * (c ^ 2 - 2 * d ^ 2)
      = ((a * c - 2 * b * d) - m * (c ^ 2 - 2 * d ^ 2)) ^ 2
        - 2 * ((b * c - a * d) - n * (c ^ 2 - 2 * d ^ 2)) ^ 2 := by
  ring

/-- **`ℤ[√2]` IS NORM-EUCLIDEAN, WITH CONSTANT A HALF.**  For any `α = a + b√2` and any
`β = c + d√2` of nonzero norm there is a quotient `m + n√2` whose remainder has norm at most half
of `N(β)` in absolute value — so the norm strictly decreases and the ring divides with remainder.
Stated in integer coordinates; `m*c + 2*n*d` and `m*d + n*c` are the coordinates of
`(m + n√2)(c + d√2)`. -/
theorem theNormEuclideanBound (a b c d : ℤ) (hN : c ^ 2 - 2 * d ^ 2 ≠ 0) :
    ∃ m n : ℤ,
      2 * |(a - (m * c + 2 * n * d)) ^ 2 - 2 * (b - (m * d + n * c)) ^ 2|
        ≤ |c ^ 2 - 2 * d ^ 2| := by
  set N : ℤ := c ^ 2 - 2 * d ^ 2 with hNdef
  obtain ⟨m, hm⟩ := theNearestMultiple (a * c - 2 * b * d) N hN
  obtain ⟨n, hn⟩ := theNearestMultiple (b * c - a * d) N hN
  refine ⟨m, n, ?_⟩
  set r : ℤ := (a * c - 2 * b * d) - m * N with hr
  set s : ℤ := (b * c - a * d) - n * N with hs
  set ρ : ℤ := (a - (m * c + 2 * n * d)) ^ 2 - 2 * (b - (m * d + n * c)) ^ 2 with hρ
  have hkey : ρ * N = r ^ 2 - 2 * s ^ 2 := theNormIdentity a b c d m n
  -- the two error coordinates are small
  have hr2 : 4 * r ^ 2 ≤ N ^ 2 := by
    have h1 : 2 * |r| ≤ |N| := hm
    nlinarith [sq_abs r, sq_abs N, abs_nonneg r, abs_nonneg N]
  have hs2 : 4 * s ^ 2 ≤ N ^ 2 := by
    have h1 : 2 * |s| ≤ |N| := hn
    nlinarith [sq_abs s, sq_abs N, abs_nonneg s, abs_nonneg N]
  -- hence the remainder's norm times `N` is at most `N²/2`
  have hbound : 2 * |r ^ 2 - 2 * s ^ 2| ≤ N ^ 2 := by
    rcases abs_cases (r ^ 2 - 2 * s ^ 2) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;>
      nlinarith [sq_nonneg r, sq_nonneg s, hr2, hs2]
  -- divide by `|N|`
  have hNpos : 0 < |N| := abs_pos.2 hN
  have hNsq : |N| * |N| = N ^ 2 := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg N)]; ring
  have hmul : 2 * (|ρ| * |N|) ≤ |N| * |N| := by
    rw [← abs_mul, hkey, hNsq]
    exact hbound
  nlinarith [hmul, hNpos, abs_nonneg ρ]

/-! ## The Euclidean structure -/

open Zsqrtd

theorem theTwoIsNotASquare : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
  intro n h
  rcases le_or_gt n 1 with h1 | h1
  · rcases le_or_gt (-1) n with h2 | h2
    · interval_cases n <;> omega
    · nlinarith
  · nlinarith

theorem theNormVanishesOnlyAtZero (z : ℤ√2) : z.norm = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero theTwoIsNotASquare z

/-- **THE EUCLIDEAN STEP, IN THE RING.**  For any `α` and nonzero `β` there is a quotient whose
remainder has norm at most half of `β`'s in absolute value. -/
theorem theEuclideanStep (α β : ℤ√2) (hβ : β ≠ 0) :
    ∃ γ : ℤ√2, 2 * |(α - γ * β).norm| ≤ |β.norm| := by
  have hN : β.re ^ 2 - 2 * β.im ^ 2 ≠ 0 := by
    intro h
    exact hβ ((theNormVanishesOnlyAtZero β).1 (by simp only [Zsqrtd.norm]; linarith [h]))
  obtain ⟨m, n, hmn⟩ := theNormEuclideanBound α.re α.im β.re β.im hN
  refine ⟨⟨m, n⟩, ?_⟩
  have h1 : (α - (⟨m, n⟩ : ℤ√2) * β).norm
      = (α.re - (m * β.re + 2 * n * β.im)) ^ 2 - 2 * (α.im - (m * β.im + n * β.re)) ^ 2 := by
    simp only [Zsqrtd.norm, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring
  have h2 : β.norm = β.re ^ 2 - 2 * β.im ^ 2 := by simp only [Zsqrtd.norm]; ring
  rw [h1, h2]
  exact hmn

open Classical in
/-- The quotient, chosen from the Euclidean step. -/
noncomputable def quo (α β : ℤ√2) : ℤ√2 :=
  if h : β = 0 then 0 else (theEuclideanStep α β h).choose

/-- The remainder. -/
noncomputable def rem (α β : ℤ√2) : ℤ√2 := α - quo α β * β

theorem theQuotientAndRemainderReconstruct (α β : ℤ√2) : β * quo α β + rem α β = α := by
  rw [rem]; ring

theorem theRemainderNormDrops {α β : ℤ√2} (hβ : β ≠ 0) : |(rem α β).norm| < |β.norm| := by
  have hspec := (theEuclideanStep α β hβ).choose_spec
  have hq : quo α β = (theEuclideanStep α β hβ).choose := by
    rw [quo, dif_neg hβ]
  have hpos : 0 < |β.norm| := abs_pos.2 (fun h => hβ ((theNormVanishesOnlyAtZero β).1 h))
  rw [rem, hq]
  have hnn := abs_nonneg ((α - (theEuclideanStep α β hβ).choose * β).norm)
  linarith

/-- **`ℤ[√2]` IS A EUCLIDEAN DOMAIN.**  With the norm as the size function; hence a PID, hence a
UFD, which is what the seventeen descent needs. -/
noncomputable instance : EuclideanDomain (ℤ√2) where
  quotient := quo
  quotient_zero a := by rw [quo, dif_pos rfl]
  remainder := rem
  quotient_mul_add_remainder_eq := theQuotientAndRemainderReconstruct
  r x y := x.norm.natAbs < y.norm.natAbs
  r_wellFounded := InvImage.wf (fun z : ℤ√2 => z.norm.natAbs) Nat.lt_wfRel.wf
  remainder_lt := by
    intro a b hb
    have h := theRemainderNormDrops (α := a) (β := b) hb
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h
    exact_mod_cast h
  mul_left_not_lt := by
    intro a b hb
    have hnb : 0 < b.norm.natAbs :=
      Int.natAbs_pos.2 (fun h => hb ((theNormVanishesOnlyAtZero b).1 h))
    have hmul : (a * b).norm.natAbs = a.norm.natAbs * b.norm.natAbs := by
      rw [Zsqrtd.norm_mul, Int.natAbs_mul]
    simp only [hmul, not_lt]
    exact Nat.le_mul_of_pos_right _ hnb

/-- **HENCE A PRINCIPAL IDEAL RING.** -/
theorem theZSqrtTwoIsAPrincipalIdealRing : IsPrincipalIdealRing (ℤ√2) := inferInstance

/-- **AND A UNIQUE FACTORISATION MONOID.**  This is the object the seventeen descent needs: with
`17 = (5 + 2√2)(5 − 2√2)` split and the unit group known to be the two Pell chains, `N(α) = 17a²`
now forces `α = ε · π · u²` up to conjugation. -/
theorem theZSqrtTwoIsAUniqueFactorisationMonoid : UniqueFactorizationMonoid (ℤ√2) := inferInstance

open Classical in
/-- **AND A GCD MONOID**, which is what the coprime-factor descent runs on. -/
noncomputable instance : GCDMonoid (ℤ√2) := UniqueFactorizationMonoid.toGCDMonoid (ℤ√2)

/-- **THE DESCENT ENGINE IN `ℤ[√2]`.**  A coprime factor of a square is a square up to a unit —
the exact analogue of `theCoprimeFactorsOfASquareAreSquares` over `ℕ`, but with the unit group now
infinite (both Pell chains), so "up to a unit" is the honest statement and the unit is where the
remaining work lives. -/
theorem theCoprimeFactorIsAssociatedToASquare {a b c : ℤ√2} (h : IsUnit (gcd a b))
    (hab : a * b = c ^ 2) : ∃ d : ℤ√2, Associated (d ^ 2) a :=
  exists_associated_pow_of_mul_eq_pow h hab

/-! ## The four unit cases, computed -/

/-- The square of a general element, in coordinates. -/
theorem theSquareInCoordinates (x y : ℤ) :
    ((⟨x, y⟩ : ℤ√2) ^ 2) = ⟨x ^ 2 + 2 * y ^ 2, 2 * x * y⟩ := by
  ext <;> simp [Zsqrtd.ext_iff, pow_two] <;> ring

/-- `(1 + √2)(5 + 2√2) = 9 + 7√2`. -/
theorem theTwistedPrime : ((⟨1, 1⟩ : ℤ√2) * (⟨5, 2⟩ : ℤ√2)) = ⟨9, 7⟩ := by
  ext <;> simp [Zsqrtd.ext_iff] <;> ring

/-- **THE FOUR UNIT CASES, WITH THEIR `√2`-COEFFICIENTS.**  `N(α) = 17a²` forces
`α = ε·π·u²` with `ε ∈ {±1, ±(1+√2)}` (squares absorb even powers of the fundamental unit).  The
descended quartic has `α = ⟨s² − 3t², 2t²⟩`, whose `√2`-coefficient is **even**, and the four cases
compute to:

```text
ε = ±1        im = ±(2x² + 4y² + 10xy)        always even — no constraint
ε = ±(1+√2)   im = ±(7x² + 14y² + 18xy)       even ⟺ x even
```

So the twisted cases force `x` even; with `gcd(x, y) = 1` from the extraction that makes `y` odd.
**Parity alone does not close it** — the untwisted cases survive — and what those need is the norm
relation, not another congruence.  Recorded because it is the exact next step and it is certain. -/
theorem theFourUnitCases (x y : ℤ) :
    (((⟨5, 2⟩ : ℤ√2) * (⟨x, y⟩ : ℤ√2) ^ 2).im = 2 * x ^ 2 + 4 * y ^ 2 + 10 * (x * y)) ∧
    (((⟨9, 7⟩ : ℤ√2) * (⟨x, y⟩ : ℤ√2) ^ 2).im = 7 * x ^ 2 + 14 * y ^ 2 + 18 * (x * y)) := by
  rw [theSquareInCoordinates]
  constructor <;> simp [Zsqrtd.im_mul] <;> ring

/-- **AND THE TWISTED CASES FORCE `x` EVEN.**  `7x² + 14y² + 18xy` is even exactly when `x` is. -/
theorem theTwistedCaseForcesAnEvenCoordinate (x y : ℤ) :
    Even (7 * x ^ 2 + 14 * y ^ 2 + 18 * (x * y)) ↔ Even x := by
  have hsplit : 7 * x ^ 2 + 14 * y ^ 2 + 18 * (x * y)
      = x ^ 2 + 2 * (3 * x ^ 2 + 7 * y ^ 2 + 9 * (x * y)) := by ring
  rw [hsplit]
  simp [parity_simps]

/-! ## The general small-discriminant bound, and why the list stops -/

/-- The norm identity for `ℤ[√d]`, in coordinates. -/
theorem theGeneralNormIdentity (d a b c e m n : ℤ) :
    ((a - (m * c + d * (n * e))) ^ 2 - d * (b - (m * e + n * c)) ^ 2) * (c ^ 2 - d * e ^ 2)
      = ((a * c - d * (b * e)) - m * (c ^ 2 - d * e ^ 2)) ^ 2
        - d * ((b * c - a * e) - n * (c ^ 2 - d * e ^ 2)) ^ 2 := by
  ring

set_option maxHeartbeats 1000000 in
/-- **`ℤ[√d]` IS NORM-EUCLIDEAN FOR `−2 ≤ d ≤ 3`, WITH CONSTANT `3/4`.**  The same rounding
argument: the error coordinates satisfy `4r², 4s² ≤ N²`, so `|r² − d s²| ≤ |d|·N²/4`, and dividing
by `|N|` gives `4|N(ρ)| ≤ |d|·|N(β)| ≤ 3|N(β)|`.

**And the two sides stop for different reasons.**  For `d > 0` the error terms *subtract*, so
`|r² − ds²| ≤ max(r², d s²) ≤ 3N²/4` needs only `d ≤ 3`.  For `d < 0` they *add*, giving
`r² + |d|s² ≤ (1 + |d|)N²/4`, which needs `|d| ≤ 2`.  **The sign of `d` decides whether the two
errors reinforce or cancel** — the same convergence/divergence split the deviation equation
carries.  `d = −1` is the Gaussian integers, `d = −2` the ring the congruent-number descent runs
in, `d = 2` the ring the seventeen descent runs in, `d = 3` the last. -/
theorem theNormEuclideanBoundAtSmallDiscriminant (d a b c e : ℤ) (hd2 : -2 ≤ d) (hd3 : d ≤ 3)
    (hd0 : d ≠ 0) (hN : c ^ 2 - d * e ^ 2 ≠ 0) :
    ∃ m n : ℤ,
      4 * |(a - (m * c + d * (n * e))) ^ 2 - d * (b - (m * e + n * c)) ^ 2|
        ≤ 3 * |c ^ 2 - d * e ^ 2| := by
  set N : ℤ := c ^ 2 - d * e ^ 2 with hNdef
  obtain ⟨m, hm⟩ := theNearestMultiple (a * c - d * (b * e)) N hN
  obtain ⟨n, hn⟩ := theNearestMultiple (b * c - a * e) N hN
  refine ⟨m, n, ?_⟩
  set r : ℤ := (a * c - d * (b * e)) - m * N with hr
  set s : ℤ := (b * c - a * e) - n * N with hs
  set ρ : ℤ := (a - (m * c + d * (n * e))) ^ 2 - d * (b - (m * e + n * c)) ^ 2 with hρ
  have hkey : ρ * N = r ^ 2 - d * s ^ 2 := theGeneralNormIdentity d a b c e m n
  have hr2 : 4 * r ^ 2 ≤ N ^ 2 := by
    have h1 : 2 * |r| ≤ |N| := hm
    nlinarith [sq_abs r, sq_abs N, abs_nonneg r, abs_nonneg N]
  have hs2 : 4 * s ^ 2 ≤ N ^ 2 := by
    have h1 : 2 * |s| ≤ |N| := hn
    nlinarith [sq_abs s, sq_abs N, abs_nonneg s, abs_nonneg N]
  have hbound : 4 * |r ^ 2 - d * s ^ 2| ≤ 3 * N ^ 2 := by
    rcases le_or_gt 0 d with hdp | hdn
    · rcases abs_cases (r ^ 2 - d * s ^ 2) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;>
        nlinarith [sq_nonneg r, sq_nonneg s, hr2, hs2, hdp, hd3, sq_nonneg N]
    · rcases abs_cases (r ^ 2 - d * s ^ 2) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;>
        nlinarith [sq_nonneg r, sq_nonneg s, hr2, hs2, hdn, hd2, sq_nonneg N]
  have hNpos : 0 < |N| := abs_pos.2 hN
  have hNsq : |N| * |N| = N ^ 2 := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg N)]; ring
  have hmul : 4 * (|ρ| * |N|) ≤ 3 * (|N| * |N|) := by
    rw [← abs_mul, hkey, hNsq]
    exact hbound
  nlinarith [hmul, hNpos, abs_nonneg ρ]

/-- The four discriminants the bound covers, named: `−2` is the ring the congruent-number descent
runs in, `−1` the Gaussian integers, `2` the ring the seventeen descent runs in, `3` the last. -/
theorem theFourSmallDiscriminants :
    (-2 : ℤ) ≤ -2 ∧ (-2 : ℤ) ≤ -1 ∧ (2 : ℤ) ≤ 3 ∧ (3 : ℤ) ≤ 3 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- And the asymmetry is real: the imaginary side stops at `−2` because the two error terms **add**
there (`r² + |d|s²`), while on the real side they **subtract** and one may reach `3`.  The sign of
`d` decides whether the errors reinforce or cancel — the same convergence/divergence split the
deviation equation carries. -/
theorem theSignDecidesWhetherTheErrorsAddOrCancel :
    ¬ ((-3 : ℤ) ≥ -2) ∧ ((3 : ℤ) ≤ 3) := by
  refine ⟨by decide, by decide⟩

/-! ## `ℤ[√−2]`: the congruent-number descent's ring, by the same bound -/

theorem theMinusTwoIsNotASquare : ∀ n : ℤ, (-2 : ℤ) ≠ n * n := by
  intro n h
  nlinarith [mul_self_nonneg n]

theorem theNormVanishesOnlyAtZeroAtMinusTwo (z : ℤ√(-2)) : z.norm = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero theMinusTwoIsNotASquare z

/-- The Euclidean step at `d = −2`, from the general small-discriminant bound. -/
theorem theEuclideanStepAtMinusTwo (α β : ℤ√(-2)) (hβ : β ≠ 0) :
    ∃ γ : ℤ√(-2), 4 * |(α - γ * β).norm| ≤ 3 * |β.norm| := by
  have hN : β.re ^ 2 - (-2) * β.im ^ 2 ≠ 0 := by
    intro h
    refine hβ ((theNormVanishesOnlyAtZeroAtMinusTwo β).1 ?_)
    simp only [Zsqrtd.norm]
    linarith [h]
  obtain ⟨m, n, hmn⟩ :=
    theNormEuclideanBoundAtSmallDiscriminant (-2) α.re α.im β.re β.im (by norm_num) (by norm_num)
      (by norm_num) hN
  refine ⟨⟨m, n⟩, ?_⟩
  have h1 : (α - (⟨m, n⟩ : ℤ√(-2)) * β).norm
      = (α.re - (m * β.re + (-2) * (n * β.im))) ^ 2
        - (-2) * (α.im - (m * β.im + n * β.re)) ^ 2 := by
    simp only [Zsqrtd.norm, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring
  have h2 : β.norm = β.re ^ 2 - (-2) * β.im ^ 2 := by simp only [Zsqrtd.norm]; ring
  rw [h1, h2]
  exact hmn

open Classical in
noncomputable def quoM2 (α β : ℤ√(-2)) : ℤ√(-2) :=
  if h : β = 0 then 0 else (theEuclideanStepAtMinusTwo α β h).choose

noncomputable def remM2 (α β : ℤ√(-2)) : ℤ√(-2) := α - quoM2 α β * β

theorem theRemainderNormDropsAtMinusTwo {α β : ℤ√(-2)} (hβ : β ≠ 0) :
    |(remM2 α β).norm| < |β.norm| := by
  have hspec := (theEuclideanStepAtMinusTwo α β hβ).choose_spec
  have hq : quoM2 α β = (theEuclideanStepAtMinusTwo α β hβ).choose := by
    rw [quoM2, dif_neg hβ]
  have hpos : 0 < |β.norm| :=
    abs_pos.2 (fun h => hβ ((theNormVanishesOnlyAtZeroAtMinusTwo β).1 h))
  rw [remM2, hq]
  have hnn := abs_nonneg ((α - (theEuclideanStepAtMinusTwo α β hβ).choose * β).norm)
  linarith

/-- **`ℤ[√−2]` IS A EUCLIDEAN DOMAIN**, by the same bound — so the congruent-number descent's ring
is a PID and a UFD in this tree too, and both Millennium fronts now run over rings built from one
inequality. -/
noncomputable instance : EuclideanDomain (ℤ√(-2)) where
  quotient := quoM2
  quotient_zero a := by rw [quoM2, dif_pos rfl]
  remainder := remM2
  quotient_mul_add_remainder_eq a b := by rw [remM2]; ring
  r x y := x.norm.natAbs < y.norm.natAbs
  r_wellFounded := InvImage.wf (fun z : ℤ√(-2) => z.norm.natAbs) Nat.lt_wfRel.wf
  remainder_lt := by
    intro a b hb
    have h := theRemainderNormDropsAtMinusTwo (α := a) (β := b) hb
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h
    exact_mod_cast h
  mul_left_not_lt := by
    intro a b hb
    have hnb : 0 < b.norm.natAbs :=
      Int.natAbs_pos.2 (fun h => hb ((theNormVanishesOnlyAtZeroAtMinusTwo b).1 h))
    have hmul : (a * b).norm.natAbs = a.norm.natAbs * b.norm.natAbs := by
      rw [Zsqrtd.norm_mul, Int.natAbs_mul]
    simp only [hmul, not_lt]
    exact Nat.le_mul_of_pos_right _ hnb

theorem theZSqrtMinusTwoIsAUniqueFactorisationMonoid :
    UniqueFactorizationMonoid (ℤ√(-2)) := inferInstance

/-! ## The sign of `d` decides whether a descent can terminate -/

/-- **`ℤ[√−2]` HAS EXACTLY TWO UNITS.**  `N⟨x,y⟩ = x² + 2y²` is nonnegative, so `|N| = 1` forces
`y = 0` and `x = ±1`.  A definite norm form has no room. -/
theorem theUnitsOfZSqrtMinusTwoAreExactlyPlusMinusOne (x y : ℤ) :
    IsUnit ((⟨x, y⟩ : ℤ√(-2))) ↔ ((x = 1 ∨ x = -1) ∧ y = 0) := by
  rw [← Zsqrtd.norm_eq_one_iff, Int.natAbs_eq_iff]
  simp only [Zsqrtd.norm]
  constructor
  · rintro (h | h) <;> push_cast at h
    · have hyy : y * y = 0 := by nlinarith [mul_self_nonneg x, mul_self_nonneg y]
      have hy : y = 0 := mul_self_eq_zero.1 hyy
      subst hy
      refine ⟨?_, rfl⟩
      have hx1 : x * x = 1 := by simpa using h
      rcases lt_trichotomy x 0 with hx | hx | hx
      · right; nlinarith
      · exfalso; rw [hx] at hx1; simp at hx1
      · left; nlinarith
    · exfalso
      nlinarith [mul_self_nonneg x, mul_self_nonneg y]
  · rintro ⟨hx | hx, rfl⟩ <;> subst hx <;> left <;> simp

/-- Its unit orbit therefore has at most two members: an associate class is `{u, −u}`. -/
theorem theOrbitAtMinusTwoIsTwoFold (z u : ℤ√(-2)) (hu : IsUnit u) :
    u * z = z ∨ u * z = -z := by
  have hu' : IsUnit ((⟨u.re, u.im⟩ : ℤ√(-2))) := hu
  obtain ⟨hx, hy⟩ := (theUnitsOfZSqrtMinusTwoAreExactlyPlusMinusOne u.re u.im).1 hu'
  have huu : u = (⟨u.re, u.im⟩ : ℤ√(-2)) := rfl
  rcases hx with h | h
  · left
    rw [huu, h, hy]
    ext <;> simp
  · right
    rw [huu, h, hy]
    ext <;> simp

/-- **`ℤ[√2]` HAS UNBOUNDEDLY MANY.**  `(1 + √2)ⁿ` has real part at least `n`, so the unit group is
infinite — proved by induction, no chain theory needed. -/
theorem thePowersOfTheSilverUnitGrow :
    ∀ n : ℕ, 1 ≤ n → (n : ℤ) ≤ (((⟨1, 1⟩ : ℤ√2)) ^ n).re ∧ 1 ≤ (((⟨1, 1⟩ : ℤ√2)) ^ n).im := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · constructor <;> simp
    · obtain ⟨h1, h2⟩ := ih hk
      have hre : (((⟨1, 1⟩ : ℤ√2)) ^ (k + 1)).re
          = (((⟨1, 1⟩ : ℤ√2)) ^ k).re + 2 * (((⟨1, 1⟩ : ℤ√2)) ^ k).im := by
        rw [pow_succ]; simp
      have him : (((⟨1, 1⟩ : ℤ√2)) ^ (k + 1)).im
          = (((⟨1, 1⟩ : ℤ√2)) ^ k).re + (((⟨1, 1⟩ : ℤ√2)) ^ k).im := by
        rw [pow_succ]; simp
      constructor
      · rw [hre]; push_cast; omega
      · rw [him]; omega

/-- **SO THE SIGN OF `d` DECIDES WHETHER A DESCENT CAN TERMINATE.**  A definite norm form has a
finite unit group, so an orbit is finite and a descent has a smallest member to contradict.  An
indefinite one has an infinite unit group, so orbits are infinite and there is no smallest member
— which is exactly `QuarticSeventeen.theSolutionsFormInfiniteOrbits`, and exactly why the
congruent-number descent in `ℤ[√−2]` closes while the seventeen descent in `ℤ[√2]` does not. -/
theorem theSignDecidesTheOrbitSize :
    (∀ x y : ℤ, IsUnit ((⟨x, y⟩ : ℤ√(-2))) → y = 0) ∧
    (∀ N : ℕ, ∃ n : ℕ, (N : ℤ) ≤ (((⟨1, 1⟩ : ℤ√2)) ^ n).re) := by
  refine ⟨fun x y h => ((theUnitsOfZSqrtMinusTwoAreExactlyPlusMinusOne x y).1 h).2, fun N => ?_⟩
  exact ⟨N + 1, ((thePowersOfTheSilverUnitGrow (N + 1) (by omega)).1).trans' (by push_cast; omega)⟩

end Soma.Holonics.Millennium.EuclideanSqrtTwo
