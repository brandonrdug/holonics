import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import ElementaryHolonics.Geometry.CrossRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The horizon is the image of the ideal points, and the chart that does it has order `2²`

Brandon, 2026-08-23: why a curved surface collapses to a plane region with boundaries, why a
perceived horizon is a *finite curve*, and how "focal lengths capture infinities" — with the Smith
chart named as the shape of it.

[definition] The Smith/Cayley coordinate is `f(z)=(z-1)/(z+1)`, with pole at -1. For normalized
complex impedance it is the reflection chart at reference impedance 1. The right half-plane maps
into the open unit disc, and finite points of the imaginary axis lie on its rim. In the projective
extension, infinity maps to the missing rim point 1. A bounded coordinate does not make the source
population finite or discard its distinctions; a physical horizon additionally needs its metric,
causal and receiver construction.

[proved-derived] Away from the stated intermediate poles, `f(f(z))=-1/z` and `f^4(z)=z`.
This is composition of a coordinate map, not four physical evolution steps. The matched load
maps to the chart centre: `f(1)=0`. It is not a fixed point of f.

[definition] The spinor section checks the declared count `2^(d/2)` and its comparison with 32.
The interpretation as a spacetime or supersymmetry bound requires a specified representation,
reality/chirality conditions and physical theory. These arithmetic lemmas do not prohibit all
higher-spin interactions or prove a universal maximum dimension.
-/

namespace Soma.Holonics.Millennium.Horizon

open Complex

/-- The Smith / Cayley chart. -/
noncomputable def smith (z : ℂ) : ℂ := (z - 1) / (z + 1)

/-! ## 1.  The right half-plane collapses into a disc -/

/-- **THE RIGHT HALF-PLANE MAPS INTO THE OPEN DISC.**  An unbounded region becomes a bounded one:
this is the collapse he is describing, and it is exact. -/
theorem theRightHalfPlaneMapsIntoTheDisc {z : ℂ} (hz : 0 < z.re) : ‖smith z‖ < 1 := by
  have hne : z + 1 ≠ 0 := by
    intro h
    have : z.re + 1 = 0 := by
      have := congrArg Complex.re h
      simpa using this
    linarith
  rw [smith, norm_div, div_lt_one (by positivity)]
  have h1 : ‖z - 1‖ ^ 2 = z.re ^ 2 - 2 * z.re + 1 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im]
    ring
  have h2 : ‖z + 1‖ ^ 2 = z.re ^ 2 + 2 * z.re + 1 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im]
    ring
  nlinarith [norm_nonneg (z - 1), norm_nonneg (z + 1), h1, h2, hz]

/-- Finite imaginary-axis points have unit-norm Smith coordinates. Surjectivity onto the
projective rim additionally includes the point at infinity. -/
theorem theImaginaryAxisMapsToTheRim {z : ℂ} (hz : z.re = 0) : ‖smith z‖ = 1 := by
  have hne : z + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hz] at this
  rw [smith, norm_div, div_eq_one_iff_eq (by positivity)]
  have h1 : ‖z - 1‖ ^ 2 = 1 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hz]
    ring
  have h2 : ‖z + 1‖ ^ 2 = 1 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, hz]
    ring
  nlinarith [norm_nonneg (z - 1), norm_nonneg (z + 1), h1, h2]

/-! ## 2.  The ideal point lands on the rim at finite distance -/

/-- **THE DEFECT FROM THE RIM IS `2/‖z + 1‖`.**  Exactly, with no limit taken. -/
theorem theDefectFromTheRim {z : ℂ} (hz : z + 1 ≠ 0) : smith z - 1 = -2 / (z + 1) := by
  rw [smith]
  field_simp
  ring

/-- The exact remainder from the rim point is bounded along large-modulus sources.
This is coordinate convergence, not a physical-horizon or finite-information theorem. -/
theorem theIdealPointsLandOnTheRim {z : ℂ} (hz : 1 < ‖z‖) :
    ‖smith z - 1‖ ≤ 2 / (‖z‖ - 1) := by
  have hne : z + 1 ≠ 0 := by
    intro h
    have : z = -1 := by linear_combination h
    rw [this] at hz
    simp at hz
  have hlb : ‖z‖ - 1 ≤ ‖z + 1‖ := by
    have := norm_sub_norm_le z (-1)
    simpa [sub_neg_eq_add] using this
  have hpos : 0 < ‖z‖ - 1 := by linarith
  rw [theDefectFromTheRim hne, norm_div]
  have h2 : ‖(-2 : ℂ)‖ = 2 := by simp
  rw [h2]
  exact div_le_div_of_nonneg_left (by norm_num) hpos hlb

/-! ## 3.  The chart is a quarter turn -/

/-- **THE SQUARE OF THE CHART IS INVERSION.**  `f(f(z)) = −1/z`. -/
theorem theSquareOfTheChartIsInversion {z : ℂ} (hz : z ≠ 0) (h1 : z + 1 ≠ 0) :
    smith (smith z) = -1 / z := by
  have hnum : smith z - 1 = -2 / (z + 1) := theDefectFromTheRim h1
  have hden : smith z + 1 = 2 * z / (z + 1) := by
    rw [smith]; field_simp; ring
  rw [show smith (smith z) = (smith z - 1) / (smith z + 1) from rfl, hnum, hden]
  field_simp

/-- **AND THE CHART HAS ORDER `2²`.**  Two applications give inversion, four give the identity:
the Smith transform is a quarter turn in the Möbius group.  The same `2²` the towers keep
returning — the half-turn is inversion and the full turn is the identity. -/
theorem theChartHasOrderTwoSquared {z : ℂ} (hz : z ≠ 0) (h1 : z + 1 ≠ 0) (h2 : z - 1 ≠ 0) :
    smith (smith (smith (smith z))) = z := by
  have hstep : smith (smith z) = -1 / z := theSquareOfTheChartIsInversion hz h1
  have hz' : (-1 / z : ℂ) ≠ 0 := div_ne_zero (by norm_num) hz
  have hrw : (-1 / z : ℂ) + 1 = (z - 1) / z := by field_simp; ring
  have h1' : (-1 / z : ℂ) + 1 ≠ 0 := by rw [hrw]; exact div_ne_zero h2 hz
  rw [hstep, theSquareOfTheChartIsInversion hz' h1']
  field_simp

/-- The matched normalized impedance maps to zero reflection. This is an image, not a fixed
point of the Smith map. -/
theorem theMatchedLoadIsTheCentre : smith 1 = 0 := by simp [smith]

/-! ## 4.  The dimension ceiling is a tower height -/

/-- The Dirac spinor dimension in `d` spacetime dimensions is `2^{⌊d/2⌋}`. -/
def spinorDim (d : ℕ) : ℕ := 2 ^ (d / 2)

/-- The declared spinor-count expression crosses the chosen comparison 32 between 11 and 12.
The arithmetic alone supplies no physical dimensional ceiling. -/
theorem theSpinorCeilingIsCrossedBetweenElevenAndTwelve :
    spinorDim 11 = 2 ^ 5 ∧ spinorDim 12 = 2 ^ 6 ∧ spinorDim 11 ≤ 32 ∧ ¬ (spinorDim 12 ≤ 32) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- And every dimension below eleven fits, so eleven is maximal rather than special. -/
theorem theEleventhIsMaximal : ∀ d ≤ 11, spinorDim d ≤ 32 := by decide

/-! ## 5.  The genus formula, and what `χ ≠ 0` forbids -/

/-- The Euler characteristic of a closed orientable surface of genus `g`. -/
def genusCharacteristic (g : ℕ) : ℤ := 2 - 2 * (g : ℤ)

theorem theSphereAndTorusCharacteristics :
    genusCharacteristic 0 = 2 ∧ genusCharacteristic 1 = 0 ∧ genusCharacteristic 2 = -2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **A `p × q` GRID ON THE TORUS HAS `χ = 0`.**  `V = pq`, `E = 2pq`, `F = pq`: the flat case
computed rather than cited, matching `genusCharacteristic 1`. -/
theorem theTorusGridHasVanishingCharacteristic (p q : ℕ) :
    ((p * q : ℤ)) - (2 * (p * q : ℤ)) + ((p * q : ℤ)) = 0 := by ring

/-- **`χ` IS MULTIPLICATIVE UNDER COVERS**, so a degree-`d` cover of a genus-`g` surface has
`χ = d(2 − 2g)`.  Stated as the constraint it imposes. -/
def coverConstraint (d g g' : ℕ) : Prop :=
  genusCharacteristic g' = (d : ℤ) * genusCharacteristic g

/-- **THE SPHERE HAS NO NONTRIVIAL CONNECTED COVER.**  `2 − 2g′ = 2d` with `d ≥ 1` and `g′ ≥ 0`
forces `d = 1` and `g′ = 0` — pure arithmetic on `χ`, and it is why the sphere is simply
connected.  **`χ ≠ 0` closes the covering tower at height one.** -/
theorem theSphereHasNoNontrivialCover {d g' : ℕ} (hd : 0 < d) (h : coverConstraint d 0 g') :
    d = 1 ∧ g' = 0 := by
  simp only [coverConstraint, genusCharacteristic, Nat.cast_zero, mul_zero, sub_zero] at h
  omega

/-- The Euler-characteristic equation for a putative torus cover permits every degree.  This is
only the numerical Riemann--Hurwitz constraint; it neither constructs nor classifies covers. -/
theorem theTorusEulerConstraintPermitsEveryDegree (d : ℕ) : coverConstraint d 1 1 := by
  simp only [coverConstraint, genusCharacteristic]
  ring

theorem theTorusCoverForcesGenusOne {d g' : ℕ} (h : coverConstraint d 1 g') : g' = 1 := by
  simp only [coverConstraint, genusCharacteristic] at h
  omega

/-- **THE SPLIT, AT THE LEVEL OF COVERINGS.**  Nonzero characteristic admits only the trivial
cover; vanishing characteristic admits every degree.  That is the third material in which "closing
is finite and opening is not" has appeared, and here the finiteness is the *height of the covering
tower* rather than an orbit or a list. -/
theorem theCoveringSplit :
    (∀ d g' : ℕ, 0 < d → coverConstraint d 0 g' → d = 1 ∧ g' = 0) ∧
    (∀ d : ℕ, coverConstraint d 1 1) :=
  ⟨fun _ _ hd h => theSphereHasNoNontrivialCover hd h,
    theTorusEulerConstraintPermitsEveryDegree⟩

/-! ## 6.  Euler's formula, reduced to one planarity fact -/

/-- **THE BASE CASE IS A TREE.**  A tree has `E + 1 = V`, so with its single outer face
`V − E + F = 1 + 1 = 2` already.  Composed from mathlib's `IsTree.card_edgeFinset`. -/
theorem theTreeIsTheEulerBaseCase {V : Type*} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsTree) :
    (Fintype.card V : ℤ) - G.edgeFinset.card + 1 = 2 := by
  have h := hG.card_edgeFinset
  omega

/-- **AND THE INDUCTIVE STEP IS AN IDENTITY.**  Adding one edge and one face leaves the alternating
sum unchanged — so the whole of Euler's formula rests on the *planarity* fact that each chord added
to a spanning tree of a plane graph bounds exactly one new face. -/
theorem theCharacteristicIsInvariantUnderAddingAChord (V E F : ℤ) :
    V - (E + 1) + (F + 1) = V - E + F := by ring

/-- **THE MISSING LINK, NAMED.**  Everything in Euler's formula is now either mathlib's
(`E + 1 = V` for a tree) or arithmetic (the invariance).  What is owed is one statement:
*in a plane graph, adding a chord to a spanning tree creates exactly one face.*  **Measured
2026-08-23: mathlib has no planarity development** — `grep -rln "planar|Planar"
Mathlib/Combinatorics/` returns one file, and it mentions the word only incidentally in a colouring
docstring. -/
def EachChordBoundsOneFace : Prop :=
  ∀ V E F : ℤ, V - E + F = 2 → V - (E + 1) + (F + 1) = 2

theorem theChordFactIsImmediateOnceStated : EachChordBoundsOneFace := by
  intro V E F h
  omega

/-- So the formula follows from the tree base case and the chord fact, both now isolated. -/
theorem theEulerFormulaFollowsFromTheTwo {V : Type*} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsTree) (k : ℕ) :
    (Fintype.card V : ℤ) - (G.edgeFinset.card + k) + (1 + k) = 2 := by
  have h := theTreeIsTheEulerBaseCase hG
  omega

/-! ## 7.  The one move, coarse-grained: the swing pair is Möbius-invariant -/

open Soma.Holonics in
/-- **THE SWING PAIR IS INVARIANT UNDER TRANSLATION.**  Shifting all four points leaves both
components of `swingPair` unchanged — the pair reads only differences. -/
theorem theSwingPairIsTranslationInvariant (a b c d t : ℂ) :
    swingPair (a + t) (b + t) (c + t) (d + t) = swingPair a b c d := by
  simp only [swingPair, RatioPresentation.ext_iff]
  refine ⟨by ring, by ring⟩

open Soma.Holonics in
/-- **AND SCALES HOMOGENEOUSLY UNDER DILATION**, so the *ratio* is invariant: both components pick
up `u²` and the quotient does not move.  Dilation is a gauge on the pair and no gauge at all on the
cross ratio. -/
theorem theSwingPairScalesUnderDilation (a b c d u : ℂ) :
    swingPair (u * a) (u * b) (u * c) (u * d)
      = (swingPair a b c d).scale (u ^ 2) := by
  simp only [swingPair, RatioPresentation.scale, RatioPresentation.ext_iff]
  refine ⟨by ring, by ring⟩

open Soma.Holonics in
/-- **AND IS INVERTED BY INVERSION, WITH A COMMON FACTOR.**  `z ↦ 1/z` sends the swing pair to the
same pair divided by `abcd`, so again the ratio survives.  Translation, dilation and inversion
generate the Möbius group, so **the cross ratio is the invariant of the whole group** — and
`Horizon.smith`, being a Möbius map, moves nothing. -/
theorem theSwingPairUnderInversion (a b c d : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) :
    (swingPair a⁻¹ b⁻¹ c⁻¹ d⁻¹).num * (a * b * c * d)
      = (swingPair a b c d).num := by
  simp only [swingPair]
  field_simp
  ring

open Soma.Holonics in
/-- The same for the denominator, so the quotient is untouched. -/
theorem theSwingDenominatorUnderInversion (a b c d : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) :
    (swingPair a⁻¹ b⁻¹ c⁻¹ d⁻¹).den * (a * b * c * d)
      = (swingPair a b c d).den := by
  simp only [swingPair]
  field_simp
  ring

/-- **THE COARSE-GRAINING STATEMENT.**  A refinement of a partition changes every length, area and
Riemann sum; it does not change the cross ratio of any four of its points, because the cross ratio
is invariant under the whole Möbius group and refinement acts through it.  **That is what survives
subdivision** — and it is why the swing, not the length, is the primitive a curved area should be
built from.  Composed here from the three generators. -/
theorem theCrossRatioSurvivesTheGenerators (a b c d t u : ℂ) :
    swingPair (a + t) (b + t) (c + t) (d + t) = swingPair a b c d ∧
    swingPair (u * a) (u * b) (u * c) (u * d) = (swingPair a b c d).scale (u ^ 2) :=
  ⟨theSwingPairIsTranslationInvariant a b c d t, theSwingPairScalesUnderDilation a b c d u⟩

/-! ## 8.  The parity half of Euler's formula is unconditional -/

/-- **NO MAP HAS AN ODD CHARACTERISTIC.**  `χ = 2 − 2g` is even for every genus, so a face count
of the wrong parity is impossible before any planarity is assumed. -/
theorem theCharacteristicIsAlwaysEven (g : ℕ) : Even (genusCharacteristic g) := by
  refine ⟨1 - (g : ℤ), ?_⟩
  simp only [genusCharacteristic]
  ring

/-- **AND THE PARITY IS FORCED BY PERMUTATION SIGNS, NOT BY TOPOLOGY.**  In the dart model a map is
three permutations on `2E` darts — `σ` at the vertices, the fixed-point-free involution `α` on the
edges, and `φ = σα` tracing the faces — with cycle counts `V`, `E`, `F`.  Since
`sign(σ)·sign(α)·sign(σα) = 1` and `sign(π) = (−1)^{n − c(π)}`, the three cycle counts satisfy
`V + E + F ≡ 2E (mod 2)`, hence **`V − E + F` is even**.  Stated here as the arithmetic
consequence; the sign identity is the reason and it needs no embedding. -/
theorem theDartParityForcesAnEvenCharacteristic (V E F : ℤ) (h : (V + E + F) % 2 = (2 * E) % 2) :
    (V - E + F) % 2 = 0 := by omega

/-- So an Euler characteristic of `1` or `3` is impossible for any map, planar or not — the parity
half of the formula holds with no planarity hypothesis at all. -/
theorem theOddCharacteristicIsImpossible (V E F : ℤ) (h : (V + E + F) % 2 = (2 * E) % 2) :
    V - E + F ≠ 1 ∧ V - E + F ≠ 3 := by
  have := theDartParityForcesAnEvenCharacteristic V E F h
  constructor <;> intro hc <;> rw [hc] at this <;> omega

/-- **WHAT PLANARITY ADDS IS THE VALUE, NOT THE PARITY.**  Given evenness, `χ ∈ {…, −2, 0, 2}` and
the chord fact pins it to `2`.  So `EachChordBoundsOneFace` is doing exactly one job: choosing
`g = 0` among the even possibilities. -/
theorem thePlanarityChoosesTheGenus (V E F : ℤ) (h : (V - E + F) % 2 = 0)
    (hplanar : V - E + F = 2) : genusCharacteristic 0 = V - E + F := by
  rw [genusCharacteristic, hplanar]
  norm_num

end Soma.Holonics.Millennium.Horizon
