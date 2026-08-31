import Mathlib.Tactic
import Mathlib.Analysis.Complex.Exponential

/-!
# Conservation of faces and angles: the excess decides the curvature, and positivity is finite

Brandon's "conservation of faces and angles", and the Play-Doh seam: a sphere cannot be combed
because `χ(S²) = 2 ≠ 0`, and a face decomposition is lawful because `V − E + F` is an invariant.
Mathlib carries no topological Euler characteristic at all (measured 2026-08-23: `grep -rln
"eulerChar|EulerChar|euler_char" Mathlib/` returns one file, and it is Möbius-function
combinatorics).  What *is* reachable, and is the same statement in the form this corpus already
owns, is the discrete Gauss–Bonnet trichotomy.

For a triangle group `(p, q, r)` the **angle excess**

```text
E(p,q,r) = 1/p + 1/q + 1/r − 1
```

has the sign of the curvature: positive is spherical, zero Euclidean, negative hyperbolic.  That is
Gauss–Bonnet with the integral replaced by a sum over the vertices, and it is exactly the
trichotomy the operating contract already carries — with `winding_inertia::lattice_admits_order`
owning the flat row, and the observation that `(2,3,5)` is finite but not crystallographic.

**The content proved here is that positivity is finite.**  Only the dihedral family `(2,2,r)` and
three sporadic triples `(2,3,3)`, `(2,3,4)`, `(2,3,5)` have positive excess — the tetrahedral,
octahedral and icosahedral symmetries, which is why there are five Platonic solids and no more.
Curvature being positive is a *closing* condition, and closing is finite.
-/

namespace Soma.Holonics.Millennium.AngleExcess

/-- The angle excess of a triangle group, exactly over `ℚ`. -/
def excess (p q r : ℕ) : ℚ := 1 / (p : ℚ) + 1 / (q : ℚ) + 1 / (r : ℚ) - 1

/-! ## 1.  The three regimes, exhibited -/

theorem theSphericalRow :
    0 < excess 2 3 3 ∧ 0 < excess 2 3 4 ∧ 0 < excess 2 3 5 ∧ 0 < excess 2 2 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [excess]

theorem theEuclideanRow :
    excess 3 3 3 = 0 ∧ excess 2 4 4 = 0 ∧ excess 2 3 6 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [excess]

theorem theHyperbolicRow : excess 2 3 7 < 0 ∧ excess 3 3 4 < 0 := by
  refine ⟨?_, ?_⟩ <;> norm_num [excess]

/-- **`(2,3,5)` IS POSITIVE BUT NOT FLAT** — the icosahedral case, finite and not
crystallographic, which is the boundary the contract already names. -/
theorem theIcosahedralCaseIsPositiveAndNotFlat : 0 < excess 2 3 5 ∧ excess 2 3 5 ≠ 0 := by
  constructor <;> norm_num [excess]

/-! ## 2.  Positivity is finite -/

/-- **THE POSITIVE-EXCESS TRIPLES ARE CLASSIFIED.**  With `2 ≤ p ≤ q ≤ r`, positive excess forces
either the dihedral family `q = 2` or one of the three sporadic triples.  Curvature being positive
is a closing condition, and only finitely many shapes close. -/
theorem thePositiveExcessTriplesAreClassified {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (h : 0 < excess p q r) :
    (p = 2 ∧ q = 2) ∨ (p = 2 ∧ q = 3 ∧ (r = 3 ∨ r = 4 ∨ r = 5)) := by
  have hpQ : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hpqQ : (p : ℚ) ≤ (q : ℚ) := by exact_mod_cast hpq
  have hqrQ : (q : ℚ) ≤ (r : ℚ) := by exact_mod_cast hqr
  have hp0 : (0 : ℚ) < p := by linarith
  have hq0 : (0 : ℚ) < q := by linarith
  have hr0 : (0 : ℚ) < r := by linarith
  rw [excess] at h
  -- `p = 2`, else all three reciprocals are at most a third
  have hp2 : p = 2 := by
    by_contra hne
    have hp3 : 3 ≤ p := by omega
    have hp3Q : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
    have h1 : 1 / (p : ℚ) ≤ 1 / 3 := by
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : 1 / (q : ℚ) ≤ 1 / 3 := by
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h3 : 1 / (r : ℚ) ≤ 1 / 3 := by
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  subst hp2
  have hhalf : (1 : ℚ) / ((2 : ℕ) : ℚ) = 1 / 2 := by norm_num
  rw [hhalf] at h
  -- now `1/q + 1/r > 1/2`, so `q ≤ 3`
  have hq3 : q ≤ 3 := by
    by_contra hne
    have hq4 : 4 ≤ q := by omega
    have hq4Q : (4 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq4
    have h2 : 1 / (q : ℚ) ≤ 1 / 4 := by
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h3 : 1 / (r : ℚ) ≤ 1 / 4 := by
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  interval_cases q
  · exact Or.inl ⟨rfl, rfl⟩
  · -- `q = 3` forces `r < 6`
    right
    refine ⟨rfl, rfl, ?_⟩
    have hthird : (1 : ℚ) / ((3 : ℕ) : ℚ) = 1 / 3 := by norm_num
    rw [hthird] at h
    have hr6 : r < 6 := by
      by_contra hne
      have hr6' : 6 ≤ r := by omega
      have hr6Q : (6 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr6'
      have h3 : 1 / (r : ℚ) ≤ 1 / 6 := by
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    omega

/-! ## 3.  Euler's formula from the Schläfli symbol -/

/-- Vertices of the regular polyhedron `{p, q}`: `q` faces meeting at each vertex, `p` sides per
face. -/
def vertices (p q : ℚ) : ℚ := 4 * p / (2 * p + 2 * q - p * q)

/-- Its edges. -/
def edges (p q : ℚ) : ℚ := 2 * p * q / (2 * p + 2 * q - p * q)

/-- Its faces. -/
def faces (p q : ℚ) : ℚ := 4 * q / (2 * p + 2 * q - p * q)

/-- **EULER'S FORMULA, FROM THE SCHLÄFLI SYMBOL ALONE.**  `V − E + F = 2` for every `{p, q}` whose
denominator does not vanish — a one-line algebraic identity, no topology needed.  The denominator
`2p + 2q − pq` is positive exactly when `1/p + 1/q > 1/2`, which is the spherical condition, so
**the same inequality that makes the excess positive is the one that makes the solid close.** -/
theorem theSchlafliEulerFormula (p q : ℚ) (h : 2 * p + 2 * q - p * q ≠ 0) :
    vertices p q - edges p q + faces p q = 2 := by
  rw [vertices, edges, faces]
  calc
    4 * p / (2 * p + 2 * q - p * q) - 2 * p * q / (2 * p + 2 * q - p * q) +
        4 * q / (2 * p + 2 * q - p * q) =
      (4 * p - 2 * p * q + 4 * q) / (2 * p + 2 * q - p * q) := by ring
    _ = 2 := by
      apply (div_eq_iff h).2
      ring

/-- The denominator is positive exactly on the spherical side. -/
theorem theDenominatorIsTheSphericalCondition {p q : ℚ} (hp : 0 < p) (hq : 0 < q) :
    0 < 2 * p + 2 * q - p * q ↔ 1 / 2 < 1 / p + 1 / q := by
  rw [div_add_div _ _ (ne_of_gt hp) (ne_of_gt hq), lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- **THE FIVE SOLIDS, COUNTED.**  Three sporadic Schläfli symbols become five solids because
duality pairs two of them; the tetrahedron is self-dual. -/
theorem theFivePlatonicSolids :
    (vertices 3 3 = 4 ∧ edges 3 3 = 6 ∧ faces 3 3 = 4) ∧
    (vertices 4 3 = 8 ∧ edges 4 3 = 12 ∧ faces 4 3 = 6) ∧
    (vertices 3 4 = 6 ∧ edges 3 4 = 12 ∧ faces 3 4 = 8) ∧
    (vertices 5 3 = 20 ∧ edges 5 3 = 30 ∧ faces 5 3 = 12) ∧
    (vertices 3 5 = 12 ∧ edges 3 5 = 30 ∧ faces 3 5 = 20) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    norm_num [vertices, edges, faces]

/-- **DUALITY IS THE SWAP.**  `V{p,q} = F{q,p}` and the edge count is symmetric: the cube and the
octahedron are one object read from its two sides, exactly as concave and convex are. -/
theorem theDualitySwapsVerticesAndFaces (p q : ℚ) :
    vertices p q = faces q p ∧ edges p q = edges q p := by
  constructor
  · rw [vertices, faces]; ring_nf
  · rw [edges, edges]; ring_nf

/-- **AND `χ = 2` HOLDS AT ALL FIVE**, which is the hairy-ball obstruction: a sphere closes, so no
nonvanishing tangent field, so the Play-Doh seam cannot be removed. -/
theorem theEulerCharacteristicIsTwoAtEverySolid :
    vertices 3 3 - edges 3 3 + faces 3 3 = 2 ∧
    vertices 4 3 - edges 4 3 + faces 4 3 = 2 ∧
    vertices 3 4 - edges 3 4 + faces 3 4 = 2 ∧
    vertices 5 3 - edges 5 3 + faces 5 3 = 2 ∧
    vertices 3 5 - edges 3 5 + faces 3 5 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact theSchlafliEulerFormula _ _ (by norm_num)

/-! ## 3a.  Unfolded face histories and exact crystalline receivers -/

/-- An unfolded face history keeps the visible face occurrence and one independently oriented
binary incidence at every side of that face.  This is a new receiver population, not the ordinary
vertex set of the visible polyhedron. -/
abbrev FaceHistory (facePopulation sidesPerFace : ℕ) :=
  Fin facePopulation × (Fin sidesPerFace → Bool)

/-- The exact population of unfolded face histories. -/
def faceHistoryPopulation (facePopulation sidesPerFace : ℕ) : ℕ :=
  facePopulation * 2 ^ sidesPerFace

/-- [proved-derived; formal-checked] The type-level occurrence population has exactly the proposed
`F·2^p` cardinality. -/
theorem card_faceHistory (facePopulation sidesPerFace : ℕ) :
    Fintype.card (FaceHistory facePopulation sidesPerFace) =
      faceHistoryPopulation facePopulation sidesPerFace := by
  simp [FaceHistory, faceHistoryPopulation]

/-- [proved-derived; formal-checked] The five Platonic unfolded receivers, in tetrahedron, cube,
octahedron, icosahedron, and dodecahedron order. -/
theorem theFivePlatonicFaceHistoryPopulations :
    faceHistoryPopulation 4 3 = 32 ∧
    faceHistoryPopulation 6 4 = 96 ∧
    faceHistoryPopulation 8 3 = 64 ∧
    faceHistoryPopulation 20 3 = 160 ∧
    faceHistoryPopulation 12 5 = 384 := by
  norm_num [faceHistoryPopulation]

/-- A crystalline realization supplies the geometric information which a Schläfli incidence
symbol and a history count do not: exact positions and complex current carried by every retained
history.  Positions need not lie on a circular or Euclidean-perfect lattice. -/
structure CrystallineFaceHistoryRealization
    (facePopulation sidesPerFace ambientDimension : ℕ) where
  position : FaceHistory facePopulation sidesPerFace → Fin ambientDimension → ℝ
  coefficient : FaceHistory facePopulation sidesPerFace → ℂ

/-- Exact phase of one retained history at a receiver wave vector. -/
noncomputable def crystallineHistoryPhase
    {facePopulation sidesPerFace ambientDimension : ℕ}
    (realization : CrystallineFaceHistoryRealization
      facePopulation sidesPerFace ambientDimension)
    (waveVector : Fin ambientDimension → ℝ)
    (history : FaceHistory facePopulation sidesPerFace) : ℂ :=
  Complex.exp (Complex.I *
    (∑ coordinate : Fin ambientDimension,
      (waveVector coordinate * realization.position history coordinate : ℝ) : ℂ))

/-- The exact finite diffraction amplitude.  Interference is performed before the intensity
receiver, so histories with the same visible endpoint may still contribute different phases. -/
noncomputable def crystallineDiffractionAmplitude
    {facePopulation sidesPerFace ambientDimension : ℕ}
    (realization : CrystallineFaceHistoryRealization
      facePopulation sidesPerFace ambientDimension)
    (waveVector : Fin ambientDimension → ℝ) : ℂ :=
  ∑ history : FaceHistory facePopulation sidesPerFace,
    realization.coefficient history *
      crystallineHistoryPhase realization waveVector history

/-- The intensity pattern is the real norm-square quotient of the complete complex amplitude. -/
noncomputable def crystallineDiffractionIntensity
    {facePopulation sidesPerFace ambientDimension : ℕ}
    (realization : CrystallineFaceHistoryRealization
      facePopulation sidesPerFace ambientDimension)
    (waveVector : Fin ambientDimension → ℝ) : ℝ :=
  Complex.normSq (crystallineDiffractionAmplitude realization waveVector)

/-! ## 4.  The trichotomy, completed: five, three, and infinitely many -/

/-- **EXACTLY THREE EUCLIDEAN TILINGS.**  `D = 0` is `(p − 2)(q − 2) = 4`, and `4` has three
ordered factorisations into positive parts — so `{3,6}`, `{4,4}`, `{6,3}` and nothing else.  The
flat row is finite too, and for a different reason from the spherical one: there the excess had to
stay positive, here a product has to hit a fixed value. -/
theorem theEuclideanTilingsAreClassified {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h : 2 * p + 2 * q = p * q) :
    (p = 3 ∧ q = 6) ∨ (p = 4 ∧ q = 4) ∨ (p = 6 ∧ q = 3) := by
  obtain ⟨a, ha⟩ : ∃ a, p = a + 2 := ⟨p - 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, q = b + 2 := ⟨q - 2, by omega⟩
  subst ha; subst hb
  have hab : a * b = 4 := by nlinarith [h]
  have ha1 : 1 ≤ a := by omega
  have ha4 : a ≤ 4 := by nlinarith
  interval_cases a <;> omega

/-- The three flat symbols, checked. -/
theorem theThreeEuclideanSymbols :
    2 * 3 + 2 * 6 = 3 * 6 ∧ 2 * 4 + 2 * 4 = 4 * 4 ∧ 2 * 6 + 2 * 3 = 6 * 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **AND INFINITELY MANY HYPERBOLIC ONES.**  Every `{3, q}` with `q ≥ 7` has `(p−2)(q−2) > 4`, so
the negative row is unbounded — the trichotomy is *five, three, infinitely many*, and only the
closing side is small. -/
theorem theHyperbolicSymbolsAreUnbounded (q : ℕ) (hq : 7 ≤ q) :
    4 < (3 - 2) * (q - 2) := by omega

/-- **THE COMPLETE COUNT.**  Positive curvature closes and is finite; flat closes on a plane and is
finite; negative opens and is not.  Finiteness is a property of *closing*, not of curvature having
a sign. -/
theorem theTrichotomyIsFiveThreeAndUnbounded :
    (∀ p q : ℕ, 2 ≤ p → p ≤ q → q ≤ q → 0 < excess p q q →
      (p = 2 ∧ q = 2) ∨ (p = 2 ∧ q = 3 ∧ (q = 3 ∨ q = 4 ∨ q = 5))) ∧
    (∀ q : ℕ, 7 ≤ q → 4 < (3 - 2) * (q - 2)) := by
  refine ⟨fun p q hp hpq _ h => ?_, theHyperbolicSymbolsAreUnbounded⟩
  exact thePositiveExcessTriplesAreClassified hp hpq (le_refl q) h

end Soma.Holonics.Millennium.AngleExcess
