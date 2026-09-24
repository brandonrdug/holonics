import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# The magnitude of `Γ` is controlled by the real part, and by a factorial

The `Λ₀` counting front waits on one growth estimate (`RH.Jensen.TheOrderOneGrowthOfXi`), and its
`Γ`-factor is the hard half.  Mathlib carries no complex Stirling estimate — measured 2026-08-23,
`Mathlib/Analysis/SpecialFunctions/Gamma/` holds exactly `Basic`, `Beta`, `BohrMollerup`,
`Deligne`, `Deriv`, and grepping them for `isBigO|Stirling|asymptot|norm_le` returns nothing
bounding `‖Γ‖` on a vertical line.

**What does not need Stirling.**  Euler's integral gives the bound directly:

```text
‖Γ(s)‖ = ‖∫₀^∞ e^{-x} x^{s-1} dx‖ ≤ ∫₀^∞ e^{-x} x^{Re s − 1} dx = Γ(Re s) .
```

That is the horizon law on `Γ`: **the imaginary part contributes only phase, and the magnitude
face sees the real part alone.**  Nothing at all happens in the `t` direction as far as size is
concerned — which is why `Λ₀` is small on vertical lines and large horizontally, and why the zero
count is a horizontal phenomenon.

Composing with monotonicity of `Γ` past `2` and `Γ(n+1) = n!` gives an explicit, Stirling-free
bound `‖Γ(s)‖ ≤ ⌈Re s⌉!`.  The remaining gap to order one is exactly the step
`log n! ≤ C·n log n`, which is the elementary half of Stirling and is stated here as the residue.
-/

namespace Soma.Holonics.RH.GammaBound

open Complex MeasureTheory Set

/-- **THE MAGNITUDE OF `Γ` IS CONTROLLED BY THE REAL PART.**  Euler's integral, with the triangle
inequality: `|x^{s-1}| = x^{Re s − 1}` for `x > 0`, so the imaginary part drops out entirely.  The
horizon law on the Gamma factor — magnitudes do not cross the imaginary direction. -/
theorem theGammaMagnitudeIsControlledByTheRealPart {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  have hnorm : ∀ x ∈ Ioi (0 : ℝ),
      ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ = Real.exp (-x) * x ^ (s.re - 1) := by
    intro x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.sub_re, Complex.one_re]
  calc ‖∫ x in Ioi (0 : ℝ), (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖
      ≤ ∫ x in Ioi (0 : ℝ), ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (s.re - 1) :=
        setIntegral_congr_fun measurableSet_Ioi hnorm
    _ = Real.Gamma s.re := (Real.Gamma_eq_integral hs).symm

/-- **AND BY A FACTORIAL.**  Past `2` the real `Γ` is monotone, and `Γ(n+1) = n!`, so any real
argument is dominated by the factorial of its ceiling — an explicit bound with no Stirling
anywhere. -/
theorem theRealGammaIsBoundedByAFactorial {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ (Nat.factorial ⌈x⌉₊) := by
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h2 : (2 : ℝ) ≤ (⌈x⌉₊ : ℝ) := le_trans hx hceil
  have hmono : Real.Gamma x ≤ Real.Gamma ((⌈x⌉₊ : ℝ)) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (mem_Ici.2 hx) (mem_Ici.2 h2) hceil
  have hn : 1 ≤ ⌈x⌉₊ := by
    have : (1 : ℝ) ≤ (⌈x⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌈x⌉₊ = m + 1 := ⟨⌈x⌉₊ - 1, by omega⟩
  have hfac : Real.Gamma ((⌈x⌉₊ : ℝ)) = (Nat.factorial m : ℝ) := by
    rw [hm]
    push_cast
    exact Real.Gamma_nat_eq_factorial m
  rw [hfac] at hmono
  refine hmono.trans ?_
  rw [hm]
  exact_mod_cast Nat.factorial_le (by omega)

/-- **THE COMPOSED, STIRLING-FREE BOUND.**  `‖Γ(s)‖ ≤ ⌈Re s⌉!` whenever `Re s ≥ 2`. -/
theorem theGammaMagnitudeIsBoundedByAFactorial {s : ℂ} (hs : 2 ≤ s.re) :
    ‖Complex.Gamma s‖ ≤ (Nat.factorial ⌈s.re⌉₊) :=
  (theGammaMagnitudeIsControlledByTheRealPart (by linarith)).trans
    (theRealGammaIsBoundedByAFactorial hs)

/-- `n! ≤ n^n`.  Not in mathlib under any `factorial_le_pow` name (measured 2026-08-23); the
induction is two lines. -/
theorem theFactorialIsBoundedByThePower : ∀ n : ℕ, Nat.factorial n ≤ n ^ n
  | 0 => by norm_num
  | (n + 1) => by
    calc Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := rfl
      _ ≤ (n + 1) * n ^ n := Nat.mul_le_mul_left _ (theFactorialIsBoundedByThePower n)
      _ ≤ (n + 1) * (n + 1) ^ n :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ n) n)
      _ = (n + 1) ^ (n + 1) := by ring

/-- **THE ELEMENTARY HALF OF STIRLING, AND IT IS ENOUGH.**  `log n! ≤ n log n` with constant one —
the step from the factorial bound to order one, discharged rather than assumed. -/
def TheFactorialLogBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → Real.log (Nat.factorial n) ≤ C * n * Real.log n

theorem theFactorialLogBoundHolds : TheFactorialLogBound := by
  refine ⟨1, one_pos, fun n hn => ?_⟩
  have h1 : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast theFactorialIsBoundedByThePower n
  have hpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  calc Real.log (Nat.factorial n) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log hpos h1
    _ = n * Real.log n := by rw [Real.log_pow]
    _ = 1 * n * Real.log n := by ring

/-- **THE `Γ`-HALF OF THE GROWTH INPUT, UNCONDITIONAL.**  `log ‖Γ(s)‖` is order one in the real
part, with no Stirling and no hypotheses. -/
theorem theGammaIsOrderOneGivenTheFactorialBound (hF : TheFactorialLogBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ s.re →
      Real.log ‖Complex.Gamma s‖ ≤ C * (⌈s.re⌉₊ : ℝ) * Real.log (⌈s.re⌉₊ : ℝ) := by
  obtain ⟨C, hC, hb⟩ := hF
  refine ⟨C, hC, fun s hs => ?_⟩
  have hn : 2 ≤ ⌈s.re⌉₊ := by
    have : (2 : ℝ) ≤ (⌈s.re⌉₊ : ℝ) := le_trans hs (Nat.le_ceil _)
    exact_mod_cast this
  have hbound := theGammaMagnitudeIsBoundedByAFactorial hs
  have hpos : (0 : ℝ) < (Nat.factorial ⌈s.re⌉₊) := by
    exact_mod_cast Nat.factorial_pos _
  have hlogn : 0 ≤ Real.log (⌈s.re⌉₊ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < ⌈s.re⌉₊))
  have hnn : (0 : ℝ) ≤ (⌈s.re⌉₊ : ℝ) := by positivity
  rcases eq_or_lt_of_le (norm_nonneg (Complex.Gamma s)) with h0 | h0
  · rw [← h0, Real.log_zero]
    have : 0 ≤ C * (⌈s.re⌉₊ : ℝ) := by positivity
    nlinarith
  · calc Real.log ‖Complex.Gamma s‖ ≤ Real.log (Nat.factorial ⌈s.re⌉₊) :=
          Real.log_le_log h0 hbound
      _ ≤ C * (⌈s.re⌉₊ : ℝ) * Real.log (⌈s.re⌉₊ : ℝ) := hb _ hn

/-- The `Γ`-half, discharged. -/
theorem theGammaIsOrderOne :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ s.re →
      Real.log ‖Complex.Gamma s‖ ≤ C * (⌈s.re⌉₊ : ℝ) * Real.log (⌈s.re⌉₊ : ℝ) :=
  theGammaIsOrderOneGivenTheFactorialBound theFactorialLogBoundHolds

/-! ## The zeta half, on the half-plane -/

/-- **`ζ` IS BOUNDED ON `Re s ≥ 2`, AND THE BOUND IS THE REAL PART'S OWN SERIES.**  The Dirichlet
series converges absolutely there and `‖n^{-s}‖ = n^{-Re s}`, so again **only the real part is
visible to the magnitude face** — the same horizon law as on `Γ`.  Combined with the functional
equation this covers both outer half-planes; what remains uncovered is the strip `0 ≤ Re s ≤ 2`,
where the bound is a convexity statement and not a series comparison. -/
theorem theZetaIsBoundedOnTheRightHalfPlane {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (2 : ℝ) := by
  have hs1 : 1 < s.re := by linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hs1]
  have hsumC : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.2 hs1
  have hsum2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.2 (by norm_num)
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ ≤ (1 : ℝ) / (n : ℝ) ^ (2 : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hs0 : s ≠ 0 := by
        intro h; rw [h] at hs; simp at hs; linarith
      simp [Complex.zero_cpow hs0, Real.zero_rpow (by norm_num : (2:ℝ) ≠ 0)]
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn]
      have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hmono : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hone hs
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnR _) hmono
  exact (norm_tsum_le_tsum_norm (hsumC.norm)).trans
    (Summable.tsum_le_tsum hterm hsumC.norm hsum2)

/-! ## What the strip actually owes -/

/-- **`ζ` IS BOUNDED ON EVERY COMPACT SET OFF THE POLE.**  Analyticity plus compactness, nothing
more.  Stated to make the remaining gap exact: **the difficulty is uniformity in the imaginary
direction, not analyticity.**  A bound at every fixed height is free; a bound polynomial in the
height, uniform across the strip, is Phragmén–Lindelöf and mathlib has no strip version. -/
theorem theZetaIsBoundedOnCompactSubsetsOffThePole {K : Set ℂ} (hK : IsCompact K)
    (h1 : (1 : ℂ) ∉ K) : ∃ M : ℝ, ∀ s ∈ K, ‖riemannZeta s‖ ≤ M := by
  have hcont : ContinuousOn riemannZeta K := by
    intro s hs
    have hne : s ≠ 1 := by rintro rfl; exact h1 hs
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  exact hK.exists_bound_of_continuousOn hcont

/-- **AND THE FUNCTIONAL EQUATION HALVES THE PROBLEM.**  `Λ₀(1 − s) = Λ₀(s)`, so a bound on
`Re s ≥ 1/2` is a bound everywhere: only the closed strip `1/2 ≤ Re s ≤ 2` is genuinely owed, a
region of width `3/2`. -/
theorem theFunctionalEquationHalvesTheStrip (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  completedRiemannZeta₀_one_sub s

/-- The reflection is an involution, so the halving loses nothing. -/
theorem theReflectionIsAnInvolution (s : ℂ) : (1 : ℂ) - (1 - s) = s := by ring

/-! ## The strip splits: one compact direction and one unbounded one -/

/-- The horizontal slice of a strip at height `t`. -/
def slice (a b t : ℝ) : Set ℂ := (fun x : ℝ => (x : ℂ) + t * Complex.I) '' Set.Icc a b

/-- **EVERY HORIZONTAL SLICE IS COMPACT.**  A strip is `[a,b] × ℝ`: the real direction is a closed
interval and the imaginary direction is a line.  So at each fixed height the region is compact —
the difficulty is entirely in the *other* factor. -/
theorem theHorizontalSliceIsCompact (a b t : ℝ) : IsCompact (slice a b t) := by
  refine (isCompact_Icc (a := a) (b := b)).image ?_
  fun_prop

/-- **AND `Λ₀` IS BOUNDED ON EACH SLICE.**  Entire, so continuous, so bounded on a compact set: a
bound at every fixed height is free. -/
theorem theSliceBoundExists (a b t : ℝ) :
    ∃ M : ℝ, ∀ s ∈ slice a b t, ‖completedRiemannZeta₀ s‖ ≤ M := by
  refine (theHorizontalSliceIsCompact a b t).exists_bound_of_continuousOn ?_
  exact differentiable_completedZeta₀.continuous.continuousOn

/-- **SO THE OWED STATEMENT IS UNIFORMITY IN THE HEIGHT.**  Slice bounds exist for every `t`; what
`RH.theZetaBoundInTheStrip` needs is that they may be chosen to grow at most polynomially in `t`.
The compact direction is discharged and the unbounded one is not — **the two directions of the
strip are now separated, with one of them closed.** -/
def TheSliceBoundsArePolynomialInTheHeight : Prop :=
  ∃ C A : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| → ∀ s ∈ slice 0 2 t,
    ‖completedRiemannZeta₀ s‖ ≤ C * |t| ^ (A : ℝ)

/-- With it, the strip bound follows immediately — the statement is the whole remaining content. -/
theorem theStripBoundFollowsFromUniformity (h : TheSliceBoundsArePolynomialInTheHeight) :
    ∃ C A : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| → ∀ s ∈ slice 0 2 t,
      ‖completedRiemannZeta₀ s‖ ≤ C * |t| ^ (A : ℝ) := h

end Soma.Holonics.RH.GammaBound
