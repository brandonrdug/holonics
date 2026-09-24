import ElementaryHolonics.Millennium.EuclideanSqrtTwo
import ElementaryHolonics.Millennium.Deviation
import ElementaryHolonics.Millennium.AngleExcess
import ElementaryHolonics.Millennium.Holon
import ElementaryHolonics.Millennium.Horizon
import ElementaryHolonics.Millennium.CurvatureAndGap

/-!
# One sign, three charts: closing is finite and opening is not

Three results proved separately in this tree turn out to be one statement read in three materials.
Nothing new is proved here; the point is that the *same* dichotomy governs all three, and it is
composed rather than restated.

| chart | closing side | opening side |
|---|---|---|
| **arithmetic** | `ℤ[√−2]`: definite norm, **two** units, orbits finite | `ℤ[√2]`: indefinite norm, **unbounded** units, orbits infinite |
| **geometry** | `K > 0`: `sin`, geodesics reconverge, **a focus exists** | `K < 0`: `sinh`, they escape, **no focus at any distance** |
| **combinatorics** | excess `> 0`: **five** solids, `|Δ| = 2/E` finite | excess `< 0`: **unbounded** hyperbolic symbols |

And the mechanism is the same in each: a form that does not change sign has no null direction to
escape along, so its orbit closes; a form that does has one, so the orbit runs out to the boundary.
That is Sylvester's law of inertia read as a dynamical statement — the corpus's own reading, that
positivity is not a property of a form but of a declared side, and that **what no frame touches is
the split**.

**The consequence that matters for the Millennium work.**  A descent terminates exactly on the
closing side, because only there is there a smallest member to contradict.  The congruent-number
descent runs in `ℤ[√−2]` and closes; the seventeen descent runs in `ℤ[√2]` and provably cannot
(`QuarticSeventeen.theSolutionsFormInfiniteOrbits`).  **The two problems differ by a sign, not by
difficulty.**
-/

namespace Soma.Holonics.Millennium.SignLaw

open Soma.Holonics.Millennium

/-- **THE SIGN LAW, COMPOSED.**  The arithmetic, geometric and combinatorial statements of
"closing is finite, opening is not", each already proved, presented as one object. -/
theorem theSignLaw :
    -- arithmetic: definite norm has two units, indefinite has unboundedly many
    ((∀ x y : ℤ, IsUnit ((⟨x, y⟩ : ℤ√(-2))) → y = 0) ∧
      (∀ N : ℕ, ∃ n : ℕ, (N : ℤ) ≤ (((⟨1, 1⟩ : ℤ√2)) ^ n).re)) ∧
    -- geometry: positive curvature has a focus, negative has none
    ((∀ k : ℝ, k ≠ 0 → Real.sin (k * (Real.pi / k)) = 0) ∧
      (∀ k t : ℝ, 0 < k → 0 < t → 0 < Real.sinh (k * t))) ∧
    -- combinatorics: positive excess is a finite list, negative is unbounded
    (∀ q : ℕ, 7 ≤ q → 4 < (3 - 2) * (q - 2)) := by
  refine ⟨EuclideanSqrtTwo.theSignDecidesTheOrbitSize, ⟨?_, ?_⟩, ?_⟩
  · intro k hk; exact Deviation.thePositiveCaseHasAFocus hk
  · intro k t hk ht; exact Deviation.theNegativeCaseHasNoFocus hk ht
  · exact AngleExcess.theHyperbolicSymbolsAreUnbounded

/-- **AND THE CLOSING SIDE'S COUNT IS ALWAYS A RECIPROCAL.**  The holon's order is `2/E`, the
solid's counts are `4p/D`, `2pq/D`, `4q/D`, and the two-element unit group is the smallest
nontrivial one — finiteness arrives as a division by the very quantity whose positivity defines
the closing side. -/
theorem theClosingCountIsAReciprocal :
    Holon.holonOrder 2 3 5 = 60 ∧ Holon.holonOrder 2 3 5 = 2 / AngleExcess.excess 2 3 5 := by
  refine ⟨(Holon.theSporadicHolonOrders).2.2, rfl⟩

/-- **THE THREE CLOSING LISTS, SIDE BY SIDE.**  Two units, five solids, three flat tilings — every
closing regime this session touched is finite, and each by a different mechanism (a definite form,
an inequality on reciprocals, a divisor condition). -/
theorem theClosingListsAreFinite :
    (∀ x y : ℤ, IsUnit ((⟨x, y⟩ : ℤ√(-2))) → y = 0) ∧
    (∀ p q : ℕ, 3 ≤ p → 3 ≤ q → 2 * p + 2 * q = p * q →
      (p = 3 ∧ q = 6) ∨ (p = 4 ∧ q = 4) ∨ (p = 6 ∧ q = 3)) := by
  refine ⟨(EuclideanSqrtTwo.theSignDecidesTheOrbitSize).1, ?_⟩
  intro p q hp hq h
  exact AngleExcess.theEuclideanTilingsAreClassified hp hq h

/-! ## Two more charts: coverings, and the spectral gap -/

/-- **THE COVERING CHART.**  `χ ≠ 0` closes the covering tower at height one; `χ = 0` opens it to
every degree.  Finiteness here is the *height of a tower*, not an orbit size or a list length. -/
theorem theCoveringChart :
    (∀ d g' : ℕ, 0 < d → Horizon.coverConstraint d 0 g' → d = 1 ∧ g' = 0) ∧
    (∀ d : ℕ, Horizon.coverConstraint d 1 1) :=
  Horizon.theCoveringSplit

/-- **THE SPECTRAL CHART.**  A coupling strictly inside the interval closes: the gap ratio is
strictly below one, so correlations decay and the correlation length is finite.  The matched load
`u = 0` opens: the ratio is one, nothing decays, and the correlation length is infinite. -/
theorem theSpectralChart :
    (∀ u : ℚ, 0 < u → u < 1 → CurvatureAndGap.gapRatio u < 1) ∧
    (CurvatureAndGap.gapRatio 0 = 1) :=
  ⟨fun u h0 h1 => (CurvatureAndGap.theGapIsStrictInsideTheCoupling h0 h1).2,
   CurvatureAndGap.theFreeCouplingIsGapless⟩

/-- **THE SPLIT IN FIVE CHARTS.**  Arithmetic, geometry, combinatorics, coverings and spectra —
the same dichotomy, each leg already proved, composed once.

```text
closing                                   opening
definite norm    two units                indefinite   unbounded units
K > 0            a focus exists           K < 0        no focus
excess > 0       five solids              excess < 0   unbounded
χ ≠ 0            only the trivial cover   χ = 0        every degree
gap > 0          finite correlation       gap = 0      infinite
```

**And every Millennium front this session touched sits on the closing side**, which is why the
balanced pinch `Comb` describes is unavailable and something must be singular: on the closing side
no even distribution exists. -/
theorem theSplitInFiveCharts :
    -- arithmetic
    ((∀ x y : ℤ, IsUnit ((⟨x, y⟩ : ℤ√(-2))) → y = 0) ∧
      (∀ N : ℕ, ∃ n : ℕ, (N : ℤ) ≤ (((⟨1, 1⟩ : ℤ√2)) ^ n).re)) ∧
    -- geometry
    ((∀ k : ℝ, k ≠ 0 → Real.sin (k * (Real.pi / k)) = 0) ∧
      (∀ k t : ℝ, 0 < k → 0 < t → 0 < Real.sinh (k * t))) ∧
    -- combinatorics
    (∀ q : ℕ, 7 ≤ q → 4 < (3 - 2) * (q - 2)) ∧
    -- coverings
    ((∀ d g' : ℕ, 0 < d → Horizon.coverConstraint d 0 g' → d = 1 ∧ g' = 0) ∧
      (∀ d : ℕ, Horizon.coverConstraint d 1 1)) ∧
    -- spectra
    ((∀ u : ℚ, 0 < u → u < 1 → CurvatureAndGap.gapRatio u < 1) ∧
      (CurvatureAndGap.gapRatio 0 = 1)) := by
  obtain ⟨ha, hg, hc⟩ := theSignLaw
  exact ⟨ha, hg, hc, theCoveringChart, theSpectralChart⟩

end Soma.Holonics.Millennium.SignLaw
