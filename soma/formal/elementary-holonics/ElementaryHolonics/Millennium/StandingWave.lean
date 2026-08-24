import ElementaryHolonics.Millennium.Deviation
import ElementaryHolonics.Millennium.CurvatureAndGap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The standing wave is the chart: a boundary condition quantises the interior

Brandon, 2026-08-23: *"boundaries of partitions as nodes and antinodes… you probably need an
instantiation of a standing wave in order to prove a theorem, because a standing wave is like a
chart."*

Three things already proved in this tree turn out to be that object.

**A standing wave is two counter-propagating waves fused.**  `sin` is the difference of the two
exponential directions, and a node is where they cancel exactly — the balanced pinch, occurring at
a *discrete* set inside a continuum.  That is the same fusion as `RH.Balance`: on the critical line
the reflection and the conjugation coincide, and the fused locus is where the two pulls are one
pull.

**The boundary condition quantises.**  Fixing the ends at `0` and `L` forces `sin(kL) = 0`, so
`k ∈ {nπ/L}` — the interior spectrum is *discrete because the boundary is fixed*.  Boundary
determines interior, producing a **population** rather than a bound.

**And the lowest mode is the gap.**  No `k` with `0 < k < π/L` gives a node, and `k = π/L` does, so
the smallest positive mode is `π/L > 0`.  **That is the mass gap** — `CurvatureAndGap.ladder`'s
first rung, arriving from a boundary condition rather than from a spectrum by fiat, and it vanishes
exactly as `L → ∞`, which is the deconfined limit.

Everything below is proved; the connection to `Deviation` is that `sin` is the positive-curvature
solution, so **standing waves exist exactly on the closing side** and the escaping side has none.
-/

namespace Soma.Holonics.Millennium.StandingWave

open Real

/-! ## 1.  A standing wave is a fusion of two directions -/

/-- **THE STANDING WAVE IS THE DIFFERENCE OF THE TWO PROPAGATING DIRECTIONS.**  `2i·sin z =
e^{iz} − e^{−iz}`: a node is where the two cancel exactly. -/
theorem theStandingWaveIsTwoCounterPropagating (z : ℂ) :
    2 * Complex.I * Complex.sin z = Complex.exp (z * Complex.I) - Complex.exp (-z * Complex.I) := by
  rw [Complex.sin]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  field_simp
  linear_combination (Complex.exp (-(Complex.I * z))
    - Complex.exp (Complex.I * z)) * hI

/-- At a node the two directions are exactly opposite — the balanced pinch, at a point. -/
theorem theNodeIsWhereTheDirectionsCancel {z : ℂ} (h : Complex.sin z = 0) :
    Complex.exp (z * Complex.I) = Complex.exp (-z * Complex.I) := by
  have := theStandingWaveIsTwoCounterPropagating z
  rw [h, mul_zero] at this
  linear_combination -this

/-! ## 2.  The boundary condition quantises the interior -/

/-- **THE NODES ARE THE INTEGER MULTIPLES.**  Fixing the ends forces `sin(kL) = 0`, and that
happens exactly at `kL = nπ`: the interior spectrum is discrete **because** the boundary is
fixed. -/
theorem theNodesAreQuantisedByTheBoundary (k L : ℝ) :
    Real.sin (k * L) = 0 ↔ ∃ n : ℤ, k * L = n * π := by
  rw [Real.sin_eq_zero_iff]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩

/-- **AND THE LOWEST MODE IS STRICTLY POSITIVE.**  No `k` strictly between `0` and `π/L` is a
mode. -/
theorem theLowestModeIsBoundedBelow {L k : ℝ} (hL : 0 < L) (hk : 0 < k) (hlt : k < π / L) :
    Real.sin (k * L) ≠ 0 := by
  have h1 : 0 < k * L := mul_pos hk hL
  have h2 : k * L < π := by
    rw [lt_div_iff₀ hL] at hlt
    linarith
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-- And `π/L` is a mode, so the gap is exactly `π/L`. -/
theorem theFirstModeIsThePiOverL {L : ℝ} (hL : 0 < L) : Real.sin ((π / L) * L) = 0 := by
  rw [div_mul_cancel₀ _ (ne_of_gt hL), Real.sin_pi]

/-- **THE GAP IS THE BOUNDARY'S RECIPROCAL.**  Positive for every finite `L`, and it is the ladder's
first rung — a mass gap arriving from a boundary condition rather than assumed. -/
theorem theGapIsThePositiveFirstMode {L : ℝ} (hL : 0 < L) : 0 < π / L := by positivity

/-- **AND IT VANISHES IN THE INFINITE-VOLUME LIMIT.**  `π/L → 0`: the deconfined, gapless case is
the boundary going away, which is exactly `YangMillsLimit.theShrinkingFamilyHasNoUniformMassGap`'s
warning in continuous form — every finite box has a gap and the limit need not. -/
theorem theGapShrinksWithTheBox {L L' : ℝ} (hL : 0 < L) (hLL : L < L') : π / L' < π / L := by
  have hL' : 0 < L' := by linarith
  exact div_lt_div_of_pos_left Real.pi_pos hL hLL

/-! ## 3.  Standing waves exist only on the closing side -/

/-- **THE ESCAPING SIDE HAS NO NODES.**  `sinh` never vanishes for positive argument, so the
negative-curvature solution supports no standing wave at all: nodes are a closing-side
phenomenon, and the chart he describes exists exactly where the object closes. -/
theorem theEscapingSideHasNoNodes {k t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    Real.sinh (k * t) ≠ 0 :=
  ne_of_gt (Soma.Holonics.Millennium.Deviation.theNegativeCaseHasNoFocus hk ht)

/-- The two sides side by side: a node at `π/k` on the closing side, none anywhere on the other. -/
theorem theNodeExistsOnlyOnTheClosingSide {k : ℝ} (hk : 0 < k) :
    Real.sin (k * (π / k)) = 0 ∧ ∀ t : ℝ, 0 < t → Real.sinh (k * t) ≠ 0 :=
  ⟨Soma.Holonics.Millennium.Deviation.thePositiveCaseHasAFocus (ne_of_gt hk),
   fun t ht => theEscapingSideHasNoNodes hk ht⟩

/-! ## 4.  Counting the nodes: Weyl's law, and where the logarithm comes from -/

/-- **THE MODE CONDITION IS LINEAR.**  The `n`-th node sits at wavenumber `nπ/L`, so it lies below
a cutoff `K` exactly when `n ≤ KL/π`: **the count is linear in the cutoff and in the box size.**
That is Weyl's law in one dimension, and the density of states is the constant `L/π`. -/
theorem theModeConditionIsLinear {L : ℝ} (hL : 0 < L) (K : ℝ) (n : ℕ) :
    (n : ℝ) * π / L ≤ K ↔ (n : ℝ) ≤ K * L / π := by
  rw [div_le_iff₀ hL, le_div_iff₀ Real.pi_pos]

/-- **THE DENSITY OF STATES IS THE BOX SIZE OVER `π`.**  Doubling the box doubles the number of
modes below any cutoff — the count is `⌊KL/π⌋` and nothing in it grows with `K` faster than
linearly. -/
theorem theDensityOfStatesIsTheBoxOverPi {L L' : ℝ} (hL : 0 < L) (h : L < L') (K : ℝ)
    (hK : 0 < K) : K * L / π < K * L' / π := by
  have := Real.pi_pos
  apply div_lt_div_of_pos_right _ this
  nlinarith

/-!
The comparison with the `T log T` zeta zero count is an interpretation, not a theorem in this
module.  Establishing it requires a global zero-counting formula and an archimedean asymptotic;
the fixed-box mode identities above supply neither one on their own.
-/

/-- The node spacing is uniform in a fixed box — `π/L` between consecutive modes, independent of
which mode.  Contrast: the zeta zeros' mean spacing near height `T` is `2π/log(T/2π)`, which
shrinks.  **Uniform spacing is the fixed-box signature and its absence is the `Γ`-factor's.** -/
theorem theNodeSpacingIsUniform {L : ℝ} (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * π / L - (n : ℝ) * π / L = π / L := by
  push_cast
  field_simp
  ring

end Soma.Holonics.Millennium.StandingWave
