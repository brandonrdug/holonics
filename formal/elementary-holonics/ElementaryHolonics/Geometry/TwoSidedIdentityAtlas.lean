import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The certified identities of the two-sided angle, and of a helical triple

This file is **exterior verification** of what `holonic_engine::identity_atlas` discovered. Nothing
here searches: each theorem is one basis vector the exact kernel returned, restated as a statement
about the chart's own parametrization, and each lowers to `linear_combination`, `field_simp` or
`ring`. The denominator and domain obligations of the atlas's charts travel as hypotheses rather
than being assumed away.

## What is stated

* `twoSidedPythagorasNumerator` and `twoSidedPythagoras` — the T0 generator `C² + k S² = 1`, over a
  variable curvature `k`, in the winding-`e` half-angle chart. The numerator form is exactly the
  certificate the atlas returns (a zero polynomial); the divided form carries the nonvanishing
  denominator as a hypothesis.
* `twoSidedCosineAddition` and `twoSidedSineAddition` — the T1 addition laws, **uniformly in `k`**.
  Setting `k = 1, 0, -1` is the circular, Galilean and hyperbolic collapse and needs no separate
  proof.
* `galileanPrincipalChartIsNotTheFibre` — the coverage falsifier. At `k = 0` the fibre `C² = 1` has
  the two components `C = 1` and `C = -1`; the half-turn winding lands on the second, so `C - 1` is
  *not* an identity of the fibre although the principal winding alone certifies it. This is
  `V(xy)`'s `y = 0` chart wrongly certifying `y`, in the configuration the atlas walks.
* `transferredLawOfSinesKillingPart` and `transferredLawOfSinesReciprocalPart` — the T2 relations
  for three helical axes. Jacobi's adjugate theorem holds over any commutative ring, hence over
  `A_k = A[ι]/(ι² - k)`; splitting it into its `1`-part and its `ι`-part gives the transferred law
  of cosines and the transferred law of sines for the triple, carrying the Killing form, the
  reciprocal (Klein) form, the pitches, the spreads and the quadrances. At `k = 0` this is the
  Euclidean screw (dual-number) case.

None of these theorems is new mathematics: the first four are the rational parametrization of a
conic and the group law of `A_k`, and the last two are Jacobi's adjugate identity transported by
the classical transfer principle. What is new here is that a machine returned them as the kernel of
a declared face map and certified every basis vector of that kernel.
-/

namespace Soma.Holonics.IdentityAtlas

section OneAngle

variable {F : Type*} [Field F]

/-- The two-sided cosine in the half-angle chart of winding `e`: `C_k(δ)` with `t = tan(δ/2)` for
`k = 1`, `δ/2` for `k = 0` and `tanh(δ/2)` for `k = -1`. -/
def twoSidedCos (e t k : F) : F := e * (1 - k * t ^ 2) / (1 + k * t ^ 2)

/-- The two-sided sine in the same chart. -/
def twoSidedSin (e t k : F) : F := e * (2 * t) / (1 + k * t ^ 2)

/--
**The certificate the atlas returns for the T0 generator: a zero polynomial.**

This is the substituted numerator, before any division, and it is what the Rust owner checks.
-/
theorem twoSidedPythagorasNumerator (e t k : F) (he : e ^ 2 = 1) :
    (e * (1 - k * t ^ 2)) ^ 2 + k * (e * (2 * t)) ^ 2 - (1 + k * t ^ 2) ^ 2 = 0 := by
  linear_combination ((1 - k * t ^ 2) ^ 2 + 4 * k * t ^ 2) * he

/--
**`C² + k S² = 1` on the declared chart**, with its nonvanishing denominator carried as a
hypothesis. The two windings are `e = 1` and `e = -1`, and `-1 = e^{iπ}` is the half-turn.
-/
theorem twoSidedPythagoras (e t k : F) (he : e ^ 2 = 1) (h : 1 + k * t ^ 2 ≠ 0) :
    twoSidedCos e t k ^ 2 + k * twoSidedSin e t k ^ 2 = 1 := by
  unfold twoSidedCos twoSidedSin
  field_simp
  linear_combination ((1 - k * t ^ 2) ^ 2 + 4 * k * t ^ 2) * he

/-- The two-sided cosine of the composed angle, in the winding `(e₁, e₂)` chart. The sum's winding
is not free: it is `e₁ e₂`, forced by the group law. -/
def sumCos (e₁ e₂ t₁ t₂ k : F) : F :=
  e₁ * e₂ * ((1 - k * t₁ ^ 2) * (1 - k * t₂ ^ 2) - 4 * k * (t₁ * t₂)) /
    ((1 + k * t₁ ^ 2) * (1 + k * t₂ ^ 2))

/-- The two-sided sine of the composed angle. -/
def sumSin (e₁ e₂ t₁ t₂ k : F) : F :=
  e₁ * e₂ * (2 * (t₁ + t₂) * (1 - k * (t₁ * t₂))) /
    ((1 + k * t₁ ^ 2) * (1 + k * t₂ ^ 2))

/--
**The addition law for the two-sided cosine, uniformly in the curvature.**

`k = 1` is `cos(a + b) = cos a cos b - sin a sin b`; `k = 0` is the Galilean collapse, where the
cosine is constant and the law degenerates; `k = -1` is `cosh(a + b) = cosh a cosh b + sinh a sinh b`.
-/
theorem twoSidedCosineAddition (e₁ e₂ t₁ t₂ k : F)
    (h₁ : 1 + k * t₁ ^ 2 ≠ 0) (h₂ : 1 + k * t₂ ^ 2 ≠ 0) :
    sumCos e₁ e₂ t₁ t₂ k =
      twoSidedCos e₁ t₁ k * twoSidedCos e₂ t₂ k
        - k * (twoSidedSin e₁ t₁ k * twoSidedSin e₂ t₂ k) := by
  unfold sumCos twoSidedCos twoSidedSin
  field_simp
  ring

/--
**The addition law for the two-sided sine, uniformly in the curvature.**
-/
theorem twoSidedSineAddition (e₁ e₂ t₁ t₂ k : F)
    (h₁ : 1 + k * t₁ ^ 2 ≠ 0) (h₂ : 1 + k * t₂ ^ 2 ≠ 0) :
    sumSin e₁ e₂ t₁ t₂ k =
      twoSidedSin e₁ t₁ k * twoSidedCos e₂ t₂ k
        + twoSidedCos e₁ t₁ k * twoSidedSin e₂ t₂ k := by
  unfold sumSin twoSidedCos twoSidedSin
  field_simp
  ring

/--
**The coverage falsifier.**

At `k = 0` the fibre of the two-sided circle is `C² = 1`, which has the two components `C = 1` and
`C = -1`. The principal winding covers only the first, so on that chart alone `C - 1` substitutes to
the zero polynomial and would be certified. The half-turn winding lands on the second component and
refuses it: the point below satisfies the fibre's equation and has `C - 1 ≠ 0`.

A chart family that omits a component certifies a non-identity. This is the concrete instance of
`V(xy)` charted only on `y = 0`.
-/
theorem galileanPrincipalChartIsNotTheFibre (t : ℚ) :
    twoSidedCos (1 : ℚ) t 0 = 1 ∧
      twoSidedCos (-1 : ℚ) t 0 = -1 ∧
      twoSidedCos (-1 : ℚ) t 0 ^ 2 + 0 * twoSidedSin (-1 : ℚ) t 0 ^ 2 = 1 ∧
      twoSidedCos (-1 : ℚ) t 0 - 1 ≠ 0 := by
  unfold twoSidedCos twoSidedSin
  norm_num

end OneAngle

section HelicalTriple

variable {A : Type*} [CommRing A]

/-- The determinant of a symmetric `3 × 3` matrix over `A`. -/
def symDet (a₁₁ a₁₂ a₁₃ a₂₂ a₂₃ a₃₃ : A) : A :=
  a₁₁ * (a₂₂ * a₃₃ - a₂₃ * a₂₃) - a₁₂ * (a₁₂ * a₃₃ - a₂₃ * a₁₃)
    + a₁₃ * (a₁₂ * a₂₃ - a₂₂ * a₁₃)

/-- `tr(adj A · B)` for symmetric `A` and `B`: the first mixed coefficient of `det (A + x B)`. -/
def adjPairing (a₁₁ a₁₂ a₁₃ a₂₂ a₂₃ a₃₃ b₁₁ b₁₂ b₁₃ b₂₂ b₂₃ b₃₃ : A) : A :=
  (a₂₂ * a₃₃ - a₂₃ * a₂₃) * b₁₁ + (a₁₁ * a₃₃ - a₁₃ * a₁₃) * b₂₂
    + (a₁₁ * a₂₂ - a₁₂ * a₁₂) * b₃₃
    + 2 * ((a₁₃ * a₂₃ - a₁₂ * a₃₃) * b₁₂)
    + 2 * ((a₁₂ * a₂₃ - a₁₃ * a₂₂) * b₁₃)
    + 2 * ((a₁₂ * a₁₃ - a₁₁ * a₂₃) * b₂₃)

/--
**The transferred law of cosines for three helical axes: the `1`-part.**

`K` is the Killing form `u_i · u_j` of the three axis directions and `R` the reciprocal (Klein)
form `u_i · v_j + v_i · u_j`; `K₁₁` is the quadrance of axis 1 and `R₁₁ = 2 h₁ Q₁` its pitch
receiver. `K₁₁K₂₂ - K₁₂²` is quadrance × spread of the pair `(1, 2)`, and `K₁₁K₂₃ - K₁₂K₁₃` is the
cross at axis 1 — the numerator of the classical law of cosines.

The statement is the `1`-component of Jacobi's adjugate identity
`(G₁₁G₂₂ - G₁₂²)(G₁₁G₃₃ - G₁₃²) - (G₁₁G₂₃ - G₁₂G₁₃)² = G₁₁ · det G` for the two-sided Gram
`G = K + ι R` with `ι² = k`.
-/
theorem transferredLawOfSinesKillingPart
    (K₁₁ K₁₂ K₁₃ K₂₂ K₂₃ K₃₃ R₁₁ R₁₂ R₁₃ R₂₂ R₂₃ R₃₃ k : A) :
    (K₁₁ * K₂₂ + k * (R₁₁ * R₂₂) - K₁₂ * K₁₂ - k * (R₁₂ * R₁₂))
          * (K₁₁ * K₃₃ + k * (R₁₁ * R₃₃) - K₁₃ * K₁₃ - k * (R₁₃ * R₁₃))
        + k * ((K₁₁ * R₂₂ + R₁₁ * K₂₂ - 2 * (K₁₂ * R₁₂))
          * (K₁₁ * R₃₃ + R₁₁ * K₃₃ - 2 * (K₁₃ * R₁₃)))
        - (K₁₁ * K₂₃ + k * (R₁₁ * R₂₃) - K₁₂ * K₁₃ - k * (R₁₂ * R₁₃)) ^ 2
        - k * (K₁₁ * R₂₃ + R₁₁ * K₂₃ - K₁₂ * R₁₃ - R₁₂ * K₁₃) ^ 2 =
      K₁₁ * (symDet K₁₁ K₁₂ K₁₃ K₂₂ K₂₃ K₃₃
            + k * adjPairing R₁₁ R₁₂ R₁₃ R₂₂ R₂₃ R₃₃ K₁₁ K₁₂ K₁₃ K₂₂ K₂₃ K₃₃)
        + k * (R₁₁ * (adjPairing K₁₁ K₁₂ K₁₃ K₂₂ K₂₃ K₃₃ R₁₁ R₁₂ R₁₃ R₂₂ R₂₃ R₃₃
            + k * symDet R₁₁ R₁₂ R₁₃ R₂₂ R₂₃ R₃₃)) := by
  simp only [symDet, adjPairing]
  ring

/--
**The transferred law of sines for three helical axes: the `ι`-part.**

This is the component that carries the pitches and the moments, and it is the statement that has no
Euclidean shadow: at `k = 0` it is the dual-angle (screw) law for three lines, whose classical form
is Study's spatial law of cosines.
-/
theorem transferredLawOfSinesReciprocalPart
    (K₁₁ K₁₂ K₁₃ K₂₂ K₂₃ K₃₃ R₁₁ R₁₂ R₁₃ R₂₂ R₂₃ R₃₃ k : A) :
    (K₁₁ * K₂₂ + k * (R₁₁ * R₂₂) - K₁₂ * K₁₂ - k * (R₁₂ * R₁₂))
          * (K₁₁ * R₃₃ + R₁₁ * K₃₃ - 2 * (K₁₃ * R₁₃))
        + (K₁₁ * R₂₂ + R₁₁ * K₂₂ - 2 * (K₁₂ * R₁₂))
          * (K₁₁ * K₃₃ + k * (R₁₁ * R₃₃) - K₁₃ * K₁₃ - k * (R₁₃ * R₁₃))
        - 2 * ((K₁₁ * K₂₃ + k * (R₁₁ * R₂₃) - K₁₂ * K₁₃ - k * (R₁₂ * R₁₃))
          * (K₁₁ * R₂₃ + R₁₁ * K₂₃ - K₁₂ * R₁₃ - R₁₂ * K₁₃)) =
      K₁₁ * (adjPairing K₁₁ K₁₂ K₁₃ K₂₂ K₂₃ K₃₃ R₁₁ R₁₂ R₁₃ R₂₂ R₂₃ R₃₃
            + k * symDet R₁₁ R₁₂ R₁₃ R₂₂ R₂₃ R₃₃)
        + R₁₁ * (symDet K₁₁ K₁₂ K₁₃ K₂₂ K₂₃ K₃₃
            + k * adjPairing R₁₁ R₁₂ R₁₃ R₂₂ R₂₃ R₃₃ K₁₁ K₁₂ K₁₃ K₂₂ K₂₃ K₃₃) := by
  simp only [symDet, adjPairing]
  ring

end HelicalTriple

end Soma.Holonics.IdentityAtlas

-- Every theorem above is axiom-clean: `propext`, `Classical.choice` and `Quot.sound` only, and no
-- `sorryAx`. These are the standing invariant's check, taken here rather than asserted elsewhere.
#print axioms Soma.Holonics.IdentityAtlas.twoSidedPythagorasNumerator
#print axioms Soma.Holonics.IdentityAtlas.twoSidedPythagoras
#print axioms Soma.Holonics.IdentityAtlas.twoSidedCosineAddition
#print axioms Soma.Holonics.IdentityAtlas.twoSidedSineAddition
#print axioms Soma.Holonics.IdentityAtlas.galileanPrincipalChartIsNotTheFibre
#print axioms Soma.Holonics.IdentityAtlas.transferredLawOfSinesKillingPart
#print axioms Soma.Holonics.IdentityAtlas.transferredLawOfSinesReciprocalPart
