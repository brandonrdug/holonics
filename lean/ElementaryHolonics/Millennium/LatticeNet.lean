import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# The smallest `Z₂` gauge net: a congruence whose sign moves, a localization that meets in its
intersection, and a gap that depends on the sector

**This file has no Yang–Mills content and its heading must not be read as one.**  `Z₂` is finite
and abelian; the Clay problem (Jaffe–Witten, Clay Mathematics Institute) is for compact **simple**
groups on `ℝ⁴` with Wightman axioms, and `Z₂` gauge theory has no continuum limit that is a
Yang–Mills theory.  What is enacted here is the *transfer-matrix formalism* on the smallest exact
carrier, and every theorem below would be true and unchanged had the Yang–Mills problem never been
posed.  The honest description is: it repairs open items in this development's own reflected
positivity datum, using lattice gauge theory as the material.

What is proved, all of it over `ℚ`, `ZMod 2` and finite index types, with no square root taken
anywhere and no floating point:

* **the crossing is a rational congruence and its middle sign moves.**  The single-link temporal
  coupling `!![1, u; u, 1]` factors as `L Λ Lᵀ` with `Λ = diag(1, 1 − u²)` over `ℚ`, so the round
  trip pays for `|u| < 1`, is degenerate at `u = 1`, and **fails at `u = 2` at an exhibited
  probe**.  That failure is the point: this development's standing positivity organ computes
  `xᵀ(MᵀM)x = |Mx|² ≥ 0`, which cannot fail for any probe, and a check that cannot fail carries no
  evidence.  Here the coupling alone is varied and the sign moves.
* **the localization meets in the intersection of its regions.**  `localNet R` — the span of the
  characters supported inside `R` — is isotone, is carried onto `localNet (σ R)` by a link
  involution, and satisfies `localNet R₁ ⊓ localNet R₂ = localNet (R₁ ∩ R₂)`.  For **disjoint**
  regions that intersection is the vacuum line `ℚ · χ_∅`, which keeps the vacuum instead of
  refusing it.  This is the object `ReflectedPositivity.lean`'s `TheHalfExchangeIsNotRequired`
  names as open: containment is too weak and disjointness too strong, and the intersection law is
  the statement that refutes both at once.  It also separates the two classical reflection planes
  — through **links** (disjoint regions, meet is the vacuum line) and through **sites** (regions
  sharing links, meet strictly larger) — which the abstract datum cannot distinguish at all.
* **the transfer operator is self-adjoint in a declared rational metric.**  For positive diagonal
  `D` and symmetric `C`, `(D C)ᵀ D⁻¹ = D⁻¹ (D C)`, both sides being `C`.  The `D^{1/2}` of the
  physics literature never enters and the carrier never leaves `ℚ`.
* **the gap depends on the sector.**  On a spatial circle at zero magnetic coupling the ungauged
  first-excited-to-ground ratio is `(1 − u)/(1 + u)`, **independent of the volume**; the Gauss-law
  (cycle-space) sector of the circle has exactly two elements, so the *physical* ratio is
  `((1 − u)/(1 + u))^L` and is **not uniform in the volume** — an exact area law with the string
  tension as the exact rate.  Same operator, two receiver sectors, two different volume laws: a
  gap figure quoted without its sector is a receiver face presented as the object.
* **the magnetic coupling moves the physical gap.**  On the single-plaquette net the physical
  block is `2 × 2` with `tr = a + b`, `det = a b (1 − u_s²)`, `a = (1+u_t)⁴`, `b = (1−u_t)⁴`.  The
  rational invariant `(tr² − 4 det)/det`, which equals `(x − y)²/(x y)` for the spectral pair and
  therefore determines the ratio, is **strictly increasing in `u_s`**; at `u_t = 1/2` it is
  `6400/81` at `u_s = 0` and `25924/243` at `u_s = 1/2`.
* **the spectrum leaves `ℚ` and the file does not follow it.**  The discriminant at that witness is
  `6481/256`, `6481` is prime, and **no rational squares to it** — so the eigenvalues there are
  quadratic irrational while every quantity the file computes is rational.  That is what "no square
  root is taken anywhere" means, stated as a theorem rather than as a habit.
* **a fixed lattice gap has no continuum limit.**  This development's own bar — *no mass-gap
  language without a scaling family* — is proved rather than merely declared: if the gap is held
  fixed in lattice units while the spacing refines, no `Δ > 0` satisfies the scaling relation.

**What this file does NOT claim**, and the boundary is the whole of it: no continuum limit, no
scaling family, no correlation length, no lattice spacing, no statement about any compact simple
group, and no use of the phrase *mass gap* as a claim about anything.  The character basis is
**declared, not derived** — the transform tying it to the configuration basis is carried in
section 8 as a named-open `Prop` and is proved for no `n` here — and the single-plaquette transfer
matrix is likewise declared rather than derived from a plaquette action.  Section 8 also records
**two boundaries for which no `Prop` is deposited at all**, with the reason in each case: the
sharper four-plaquette anti-vacuity witness, whose only available formulation in this carrier was
`False` in disguise, and the continuum family, whose only available formulation was satisfiable by
choosing the spacing law to be the gap — a fake open item, which is as defective as a fake
theorem.

**Primary falsifier, recorded as the boundary and refuted in section 4.**  Exhibit disjoint link
regions `R₁, R₂` and a vector in `localNet R₁ ⊓ localNet R₂` with a nonzero coordinate at some `S`
not contained in `R₁ ∩ R₂`.  It is stated as `TheLocalNetsMeetOutsideTheirIntersection` and its
negation is proved.  **Second falsifier, refuted in section 6**: if the physical gap invariant of
the single-plaquette net were independent of `u_s`, the construction would be a tensor-power
tautology and the file would have to be withdrawn rather than patched; it is stated as
`TheMagneticCouplingIsSpectrallyInert` and its negation is proved.  A standing weakness is
recorded with it: that a `2 × 2` block's discriminant depends on its own off-diagonal is nearly
automatic, and the sharper witness — the `2 × 2` periodic net, whose physical block is
`32 × 32` and whose spectrum is not closed form — is not in this file.

**Classical imports, cited and not proved here.**  Reflection positivity for the Wilson action
under link reflection, and the strong-coupling cluster expansion giving exponential clustering and
the area law uniformly in volume: Osterwalder and Seiler, *Gauge field theories on a lattice*, Ann.
Phys. 110 (1978) 440–471.  The self-adjoint strictly positive transfer matrix: Lüscher, Comm. Math.
Phys. 54 (1977) 283–292.  Extension to reflection planes containing sites: Menotti and Pelissetto,
Comm. Math. Phys. 113 (1987) 369–373.  The reconstruction axioms and the `H₊/N_Θ` quotient:
Osterwalder and Schrader, Comm. Math. Phys. (1973) and (1975).  The lattice action, the Wilson loop
and the strong-coupling area law: Wilson, Phys. Rev. D 10 (1974) 2445.  `Z₂` gauge theory, its
duality with the Ising model and the absence of a local order parameter: Wegner, J. Math. Phys. 12
(1971) 2259.  A net of local algebras, isotone with a reversing reflection: Haag and Kastler, J.
Math. Phys. 5 (1964) 848 — section 4 is that structure with a Lean type signature attached, and
its only content beyond the 1964 definition is the intersection law.  The scaling family a
continuum limit would need is fixed by asymptotic freedom: Gross and Wilczek, and Politzer, Phys.
Rev. Lett. 30 (1973) 1343 and 1346.  Ultraviolet stability by block-spin renormalization for
`SU(2)`/`SU(3)` in finite volume: Balaban, Comm. Math. Phys., 1984–1989.  **None of these is used
below; each is named so the instances are read at their true height.**

**Measured 2026-08-21, with this file present.**
`grep -rn -i "mass gap" formal/elementary-holonics/ElementaryHolonics --include='*.lean'`
→ 5 hits: an aside label in `Lines.lean`, a disclaimer in `ReflectedPositivity.lean`, and three in
this file — the boundary sentence above, the pattern in this command, and the closing sentence
below.  **None of the five is a claim**, and the count is stated with this file included precisely
so that it stays true after the file is added.
`grep -rli "lattice gauge\|reflection positiv\|Osterwalder" Mathlib --include='*.lean'` over
`.lake/packages/mathlib` at `v4.27.0` → 0 files.
`grep -ic "kronecker" Mathlib/LinearAlgebra/Matrix/PosDef.lean` → 0.
Those commands measure those names over those scopes; they are not claims that no related content
exists under another name.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here is a claim about any
named conjecture, and the phrase "mass gap" appears nowhere as a claim.
-/

namespace Soma.Holonics.Millennium.LatticeNet

/-! ## 1. One link: the crossing, its congruence, and the sign that moves

The temporal coupling on a single `Z₂` link, in the configuration basis, is `!![1, u; u, 1]` with
`u` a declared rational.  Everything in this section is exact over `ℚ`. -/

/-- The single-link temporal crossing. -/
def crossing (u : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![1, u; u, 1]

/-- The unit-lower factor of the congruence. -/
def congruenceLower (u : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; u, 1]

/-- The middle factor of the congruence.  **Its second entry is the sign that moves.** -/
def congruenceMiddle (u : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1 - u ^ 2]

/-- **The crossing is a rational congruence.**  `L Λ Lᵀ = C`, exactly over `ℚ`, with no root
extracted and no completion of the field. -/
theorem theCrossingIsARationalCongruence (u : ℚ) :
    congruenceLower u * congruenceMiddle u * (congruenceLower u).transpose = crossing u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [congruenceLower, congruenceMiddle, crossing, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply]
  ring

/-- The quadratic form the crossing carries. -/
def crossingForm (u x y : ℚ) : ℚ := x ^ 2 + 2 * u * x * y + y ^ 2

/-- **The form really is the matrix's form** — the probe passes through `mulVec` and the dot
product, not through a renamed expression. -/
theorem theCrossingFormIsTheFormOfTheCrossing (u x y : ℚ) :
    ![x, y] ⬝ᵥ (crossing u).mulVec ![x, y] = crossingForm u x y := by
  simp [crossing, crossingForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- **The congruence, read on the form**: the whole coupling dependence sits in one coefficient. -/
theorem theCongruenceExhibitsTheMovingSign (u x y : ℚ) :
    crossingForm u x y = (x + u * y) ^ 2 + (1 - u ^ 2) * y ^ 2 := by
  unfold crossingForm; ring

/-- **The middle sign moves with the coupling and nothing else.**  Positive inside, degenerate at
the boundary, negative outside. -/
theorem theMiddleSignMovesWithTheCoupling (u : ℚ) :
    (|u| < 1 → 0 < 1 - u ^ 2) ∧ (u = 1 → 1 - u ^ 2 = 0) ∧ (1 < u → 1 - u ^ 2 < 0) := by
  refine ⟨fun h => ?_, fun h => by rw [h]; norm_num, fun h => by nlinarith⟩
  rw [abs_lt] at h
  nlinarith [h.1, h.2]

/-- **The net pays its round trip inside the coupling.**  Non-negativity for every rational probe,
obtained from the congruence rather than from a square that cannot fail. -/
theorem theNetPaysInsideTheCoupling (u : ℚ) (h1 : -1 < u) (h2 : u < 1) (x y : ℚ) :
    0 ≤ crossingForm u x y := by
  rw [theCongruenceExhibitsTheMovingSign]
  have hpos : 0 < 1 - u ^ 2 := by nlinarith
  nlinarith [sq_nonneg (x + u * y), mul_nonneg hpos.le (sq_nonneg y)]

/-- **The net refuses outside the coupling, at an exhibited probe.**  One link, `F = (1, −1)`,
`u = 2`, value `−2`.  Every other input is held fixed and only the coupling moves, so the
positivity above is attributable to the coupling and the congruence's middle factor is
load-bearing. -/
theorem theNetRefusesOutsideTheCoupling :
    crossingForm 2 1 (-1) = -2 ∧ crossingForm 2 1 (-1) < 0 := by
  constructor <;> norm_num [crossingForm]

/-! ## 2. The character basis: the spectrum and the ungauged ratio

In the character basis the tensor-power crossing is diagonal, with the entry at a character `S`
depending only on how many links are *defective* for `S`.  **The basis is declared here, not
derived**; the transform is section 8's named-open `Prop`. -/

/-- The character-basis eigenvalue of the crossing at a character with `aligned` aligned links and
`defect` defective ones. -/
def crossingEigenvalue (aligned defect : ℕ) (u : ℚ) : ℚ := (1 + u) ^ aligned * (1 - u) ^ defect

/-- The character-basis crossing on `n` links, at the character indexed by `S`. -/
def characterCrossing {n : ℕ} (u : ℚ) (S : Finset (Fin n)) : ℚ :=
  crossingEigenvalue (n - S.card) S.card u

/-- **The spectrum is ordered by the defect count**: moving one link from defective to aligned
strictly raises the eigenvalue, for every coupling strictly inside the interval. -/
theorem theSpectrumIsOrderedByTheDefectCount (u : ℚ) (hu0 : 0 < u) (hu1 : u < 1) (a d : ℕ) :
    crossingEigenvalue a (d + 1) u < crossingEigenvalue (a + 1) d u := by
  have h1 : (0 : ℚ) < 1 + u := by linarith
  have h2 : (0 : ℚ) < 1 - u := by linarith
  have hX : (0 : ℚ) < (1 + u) ^ a * (1 - u) ^ d := by positivity
  have key : 0 < u * ((1 + u) ^ a * (1 - u) ^ d) := mul_pos hu0 hX
  simp only [crossingEigenvalue, pow_succ]
  nlinarith [key]

/-- **The ungauged gap ratio does not see the volume.**  First excited over ground is
`(1 − u)/(1 + u)` on every number of links. -/
theorem theUngaugedGapRatioDoesNotSeeTheVolume (u : ℚ) (hu : 1 + u ≠ 0) (L : ℕ) :
    crossingEigenvalue L 1 u / crossingEigenvalue (L + 1) 0 u = (1 - u) / (1 + u) := by
  have hp : ((1 : ℚ) + u) ^ L ≠ 0 := pow_ne_zero _ hu
  simp only [crossingEigenvalue, pow_succ, pow_zero, mul_one]
  field_simp

/-! ## 3. The Gauss-law sector, and the gap that depends on it

The physical sector is the `𝔽₂` cycle space — the configurations the boundary map annihilates.
For the spatial circle it has exactly two elements, so the physical spectrum is two eigenvalues and
the physical ratio is the volume power of the ungauged one. -/

/-- The circle's boundary condition: a link assignment is a cycle when every vertex is balanced. -/
def circleCycle (L : ℕ) (f : ZMod L → ZMod 2) : Prop := ∀ v : ZMod L, f v + f (v - 1) = 0

/-- **The cycle space of the three-link circle is the constant sector.**  By exhaustion over all
eight assignments. -/
theorem theCycleSpaceOfTheThreeCircleIsTheConstantSector :
    ∀ f : ZMod 3 → ZMod 2, circleCycle 3 f → ∀ v, f v = f 0 := by
  unfold circleCycle
  decide

/-- **The cycle space of the four-link circle is the constant sector.**  By exhaustion over all
sixteen assignments. -/
theorem theCycleSpaceOfTheFourCircleIsTheConstantSector :
    ∀ f : ZMod 4 → ZMod 2, circleCycle 4 f → ∀ v, f v = f 0 := by
  unfold circleCycle
  decide

/-- **The cycle space of the five-link circle is the constant sector.**  By exhaustion over all
thirty-two assignments. -/
theorem theCycleSpaceOfTheFiveCircleIsTheConstantSector :
    ∀ f : ZMod 5 → ZMod 2, circleCycle 5 f → ∀ v, f v = f 0 := by
  unfold circleCycle
  decide

/-- **The gauged gap ratio is the volume power of the ungauged one.**  The physical sector of the
circle carries exactly the empty and the full character, so the physical ratio is
`((1 − u)/(1 + u))^L`.  This is the area law with the string tension as the exact rate.

**DEFINITIONAL after `div_pow` — the content is the sector identification above, not this step.** -/
theorem theGaugedGapRatioIsTheVolumePower (u : ℚ) (L : ℕ) :
    crossingEigenvalue 0 L u / crossingEigenvalue L 0 u = ((1 - u) / (1 + u)) ^ L := by
  simp only [crossingEigenvalue, pow_zero, one_mul, mul_one, div_pow]

/-- **The physical gap ratio is not uniform in the volume.**  For every declared floor there is a
circle whose gauged ratio falls below it — while the ungauged ratio, by the theorem above, never
moves at all.  Two receiver sectors of one operator, two different volume laws. -/
theorem theGaugedGapRatioIsNotUniformInTheVolume (u c : ℚ) (hu0 : 0 < u) (hu1 : u < 1)
    (hc : 0 < c) : ∃ L : ℕ, crossingEigenvalue 0 L u / crossingEigenvalue L 0 u < c := by
  have h1 : (0 : ℚ) < 1 + u := by linarith
  have hr1 : (1 - u) / (1 + u) < 1 := by
    rw [div_lt_one h1]; linarith
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hc hr1
  exact ⟨L, by rw [theGaugedGapRatioIsTheVolumePower]; exact hL⟩

/-- **And the decay rate is exact and volume-independent**, which is what an area law says: the
ratio at volume `L` is exactly the `L`-th power of one fixed rate.

**DEFINITIONAL — this is the previous theorem read as a bound.** -/
theorem theGaugedGapRatioDecaysAtTheExactStringTension (u : ℚ) (L : ℕ) :
    crossingEigenvalue 0 L u / crossingEigenvalue L 0 u ≤ ((1 - u) / (1 + u)) ^ L :=
  le_of_eq (theGaugedGapRatioIsTheVolumePower u L)

/-! ## 4. The localization, and the primary falsifier

A region is a finite set of links; `localNet R` is the coordinate subspace of the character space
spanned by the characters supported inside `R`.  This is the Haag–Kastler net (1964) with a Lean
type signature attached, and its only content beyond that definition is the intersection law. -/

variable {E : Type*} [DecidableEq E]

/-- The local net at a region: the characters supported inside it. -/
def localNet (R : Finset E) : Submodule ℚ (Finset E → ℚ) where
  carrier := {f | ∀ S : Finset E, ¬ S ⊆ R → f S = 0}
  add_mem' := by
    intro f g hf hg S hS
    simp only [Pi.add_apply, hf S hS, hg S hS, add_zero]
  zero_mem' := by intro S _; rfl
  smul_mem' := by
    intro c f hf S hS
    simp only [Pi.smul_apply, hf S hS, smul_eq_mul, mul_zero]

omit [DecidableEq E] in
/-- **DEFINITIONAL — `Iff.rfl`.** -/
@[simp] theorem mem_localNet {R : Finset E} {f : Finset E → ℚ} :
    f ∈ localNet R ↔ ∀ S : Finset E, ¬ S ⊆ R → f S = 0 := Iff.rfl

omit [DecidableEq E] in
/-- **The net is isotone.**  A larger region carries everything a smaller one does. -/
theorem theLocalNetIsIsotone {R₁ R₂ : Finset E} (h : R₁ ⊆ R₂) : localNet R₁ ≤ localNet R₂ := by
  intro f hf S hS
  exact hf S fun hSR => hS (hSR.trans h)

/-- **The two nets meet in the net of the intersection.**

This is the statement that refutes containment as too weak and disjointness as too strong at the
same time, and it is the object the abstract reflected-positivity datum cannot carry, because that
datum has one declared half and no regions at all.  Honestly graded: the local net is a
subset-indexed coordinate subspace, so the proof is the corresponding statement about `Finset`
subsets, `S ⊆ R₁ ∩ R₂ ↔ S ⊆ R₁ ∧ S ⊆ R₂`, and nothing deeper. -/
theorem theLocalNetsMeetInTheirIntersection (R₁ R₂ : Finset E) :
    localNet R₁ ⊓ localNet R₂ = localNet (R₁ ∩ R₂) := by
  ext f
  simp only [Submodule.mem_inf, mem_localNet]
  constructor
  · rintro ⟨h1, h2⟩ S hS
    rw [Finset.subset_inter_iff] at hS
    rcases not_and_or.mp hS with h | h
    · exact h1 S h
    · exact h2 S h
  · intro h
    exact ⟨fun S hS => h S fun hc => hS (hc.trans Finset.inter_subset_left),
      fun S hS => h S fun hc => hS (hc.trans Finset.inter_subset_right)⟩

/-- The vacuum character. -/
def vacuum : Finset E → ℚ := fun S => if S = ∅ then 1 else 0

/-- **The empty region carries exactly the vacuum line.** -/
theorem theEmptyRegionCarriesTheVacuumLine :
    localNet (∅ : Finset E) = Submodule.span ℚ {(vacuum : Finset E → ℚ)} := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_span_singleton]
    refine ⟨f ∅, ?_⟩
    funext S
    by_cases hS : S = ∅
    · subst hS; simp [vacuum]
    · have hns : ¬ S ⊆ (∅ : Finset E) := by
        rw [Finset.subset_empty]; exact hS
      simp [vacuum, hS, hf S hns]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    show (vacuum : Finset E → ℚ) ∈ localNet (∅ : Finset E)
    intro S hS
    have hns : S ≠ ∅ := by
      rw [Finset.subset_empty] at hS; exact hS
    simp [vacuum, hns]

/-- **Disjoint regions meet in the vacuum line.**  The intersection law *keeps* the vacuum rather
than refusing it — which is the difference between a localization and a disjointness hypothesis.
This is the link-reflection case; when the two regions share links, as they do for a reflection
plane through sites, the meet is strictly larger and the theorem above says exactly how much. -/
theorem theDisjointRegionsMeetInTheVacuumLine {R₁ R₂ : Finset E} (h : Disjoint R₁ R₂) :
    localNet R₁ ⊓ localNet R₂ = Submodule.span ℚ {(vacuum : Finset E → ℚ)} := by
  rw [theLocalNetsMeetInTheirIntersection, Finset.disjoint_iff_inter_eq_empty.mp h,
    theEmptyRegionCarriesTheVacuumLine]

/-- **The primary falsifier of this file, stated so it can be checked.**  If two local nets met at
a coordinate outside the intersection of their regions, the localization would not be the object
that carries the exchange and the repair proposed here would be wrong. -/
def TheLocalNetsMeetOutsideTheirIntersection (E : Type*) [DecidableEq E] : Prop :=
  ∃ (R₁ R₂ S : Finset E) (f : Finset E → ℚ),
    f ∈ localNet R₁ ⊓ localNet R₂ ∧ f S ≠ 0 ∧ ¬ S ⊆ R₁ ∩ R₂

/-- **The primary falsifier does not fire.** -/
theorem theLocalNetsDoNotMeetOutsideTheirIntersection :
    ¬ TheLocalNetsMeetOutsideTheirIntersection E := by
  rintro ⟨R₁, R₂, S, f, hf, hfS, hS⟩
  rw [theLocalNetsMeetInTheirIntersection] at hf
  exact hfS (hf S hS)

/-- The reflection on regions, induced by an involution of the links. -/
def regionReflection (σ : E ≃ E) (S : Finset E) : Finset E := S.image σ

/-- **The region reflection is an involution.** -/
theorem theRegionReflectionIsAnInvolution (σ : E ≃ E) (hσ : ∀ e, σ (σ e) = e) (S : Finset E) :
    regionReflection σ (regionReflection σ S) = S := by
  unfold regionReflection
  rw [Finset.image_image]
  have hcomp : (σ : E → E) ∘ (σ : E → E) = id := by funext e; exact hσ e
  rw [hcomp, Finset.image_id]

/-- The reflection on the character space. -/
def characterReflection (σ : E ≃ E) (f : Finset E → ℚ) : Finset E → ℚ :=
  fun S => f (regionReflection σ S)

/-- **The character reflection is `ℚ`-linear.**  **DEFINITIONAL — `rfl`.** -/
theorem theCharacterReflectionIsLinear (σ : E ≃ E) (c : ℚ) (f g : Finset E → ℚ) :
    characterReflection σ (c • f + g)
      = c • characterReflection σ f + characterReflection σ g := rfl

/-- **The reflection carries the net at a region onto the net at the reflected region.**  Isotone
net, reversing reflection: the two fields the abstract datum has and the concrete one owes. -/
theorem theReflectionCarriesTheNetOntoTheReflectedRegion
    (σ : E ≃ E) (hσ : ∀ e, σ (σ e) = e) (R : Finset E) (f : Finset E → ℚ)
    (hf : f ∈ localNet R) : characterReflection σ f ∈ localNet (regionReflection σ R) := by
  intro S hS
  refine hf _ fun hc => hS ?_
  have h2 : regionReflection σ (regionReflection σ S) ⊆ regionReflection σ R :=
    Finset.image_subset_image hc
  rwa [theRegionReflectionIsAnInvolution σ hσ S] at h2

/-! ## 5. The declared metric

The physics literature symmetrizes `D C` to `D^{1/2} C D^{1/2}` to make the transfer operator
Hermitian in the standard inner product.  Over `ℚ` that square root does not exist, and it is not
needed: `D C` is self-adjoint for the metric `D⁻¹`, which is a declaration a receiver makes rather
than a quantity anyone extracts.  Honestly graded: this is textbook similarity, and the gain is
narrow and real — the whole line stays inside `ℚ` and is therefore kernel-checkable. -/

/-- **The rational transfer is self-adjoint in the declared metric**, with no square root taken
anywhere.  Both sides are `C`. -/
theorem theRationalTransferIsSelfAdjointInTheDeclaredMetric {n : ℕ} (d : Fin n → ℚ)
    (hd : ∀ i, d i ≠ 0) (C : Matrix (Fin n) (Fin n) ℚ) (hC : C.transpose = C) :
    (Matrix.diagonal d * C).transpose * Matrix.diagonal (fun i => (d i)⁻¹)
      = Matrix.diagonal (fun i => (d i)⁻¹) * (Matrix.diagonal d * C) := by
  have hright : Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹)
      = (1 : Matrix (Fin n) (Fin n) ℚ) := by
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => d i * (d i)⁻¹) = fun _ : Fin n => (1 : ℚ) := by
      funext i; exact mul_inv_cancel₀ (hd i)
    rw [this]
    simp
  have hleft : Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d
      = (1 : Matrix (Fin n) (Fin n) ℚ) := by
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => (d i)⁻¹ * d i) = fun _ : Fin n => (1 : ℚ) := by
      funext i; exact inv_mul_cancel₀ (hd i)
    rw [this]
    simp
  calc (Matrix.diagonal d * C).transpose * Matrix.diagonal (fun i => (d i)⁻¹)
      = C * (Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹)) := by
        rw [Matrix.transpose_mul, hC, Matrix.diagonal_transpose, mul_assoc]
    _ = C := by rw [hright, mul_one]
    _ = Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d * C := by rw [hleft, one_mul]
    _ = Matrix.diagonal (fun i => (d i)⁻¹) * (Matrix.diagonal d * C) := mul_assoc _ _ _

/-! ## 6. The single-plaquette net, and the gap that moves with the magnetic coupling

Four links, four vertices, cycle-space dimension one, physical sector of dimension two.  In that
sector the transfer matrix is `2 × 2` and is **declared** here, not derived from an action; what is
proved is its trace and determinant, and that the rational gap invariant built from them is
strictly monotone in the magnetic coupling. -/

/-- The declared physical transfer matrix of the single-plaquette net. -/
def plaquetteTransfer (ut us : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 + ut) ^ 4, us * (1 - ut) ^ 4; us * (1 + ut) ^ 4, (1 - ut) ^ 4]

/-- **Its trace is the sum of the two temporal weights** and does not see the magnetic coupling. -/
theorem thePlaquetteTransferHasTheDeclaredTrace (ut us : ℚ) :
    (plaquetteTransfer ut us).trace = (1 + ut) ^ 4 + (1 - ut) ^ 4 := by
  rw [plaquetteTransfer, Matrix.trace_fin_two_of]

/-- **Its determinant carries the magnetic coupling**, as `1 − u_s²`. -/
theorem thePlaquetteTransferHasTheDeclaredDeterminant (ut us : ℚ) :
    (plaquetteTransfer ut us).det = (1 + ut) ^ 4 * (1 - ut) ^ 4 * (1 - us ^ 2) := by
  rw [plaquetteTransfer, Matrix.det_fin_two_of]; ring

/-- The rational gap invariant of a spectral pair, read off its trace and determinant. -/
def gapInvariant (tr det : ℚ) : ℚ := (tr ^ 2 - 4 * det) / det

/-- **The invariant is the squared splitting over the product**, so it is a statement about the
spectral pair and not about the coordinates the matrix was written in.  No root is extracted. -/
theorem theGapInvariantIsTheSquaredSplittingOverTheProduct (x y : ℚ) :
    (x - y) ^ 2 / (x * y) = gapInvariant (x + y) (x * y) := by
  unfold gapInvariant
  congr 1
  ring

/-- **The invariant determines the ratio.**  On `(0, 1]` the map `r ↦ (1 − r)²/r` is injective, so
two different invariants are two different gaps and never a reparametrisation. -/
theorem theGapInvariantDeterminesTheRatio {r₁ r₂ : ℚ} (h1 : 0 < r₁) (h1' : r₁ ≤ 1)
    (h2 : 0 < r₂) (h2' : r₂ ≤ 1) (h : (1 - r₁) ^ 2 / r₁ = (1 - r₂) ^ 2 / r₂) : r₁ = r₂ := by
  rw [div_eq_div_iff (ne_of_gt h1) (ne_of_gt h2)] at h
  have key : (r₂ - r₁) * (1 - r₁ * r₂) = 0 := by linear_combination h
  rcases mul_eq_zero.mp key with h' | h'
  · linarith
  · have hprod : r₁ * r₂ = 1 := by linarith
    have ha : 1 ≤ r₁ := by nlinarith [mul_nonneg h1.le (sub_nonneg.mpr h2')]
    have hb : 1 ≤ r₂ := by nlinarith [mul_nonneg h2.le (sub_nonneg.mpr h1')]
    linarith

/-- The gap invariant of the single-plaquette physical sector. -/
def plaquetteGapInvariant (ut us : ℚ) : ℚ :=
  gapInvariant ((1 + ut) ^ 4 + (1 - ut) ^ 4) ((1 + ut) ^ 4 * (1 - ut) ^ 4 * (1 - us ^ 2))

/-- **The invariant rises with the magnetic parameter**, for any positive temporal weights.  The
difference of the two cross-multiplied sides is exactly `a b (a + b)² (s₂ − s₁)`. -/
theorem theGapInvariantRisesWithTheMagneticParameter (a b s₁ s₂ : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hs : s₁ < s₂) (hs₂ : s₂ < 1) :
    gapInvariant (a + b) (a * b * (1 - s₁)) < gapInvariant (a + b) (a * b * (1 - s₂)) := by
  have h1 : (0 : ℚ) < 1 - s₁ := by linarith
  have h2 : (0 : ℚ) < 1 - s₂ := by linarith
  have d1 : 0 < a * b * (1 - s₁) := mul_pos (mul_pos ha hb) h1
  have d2 : 0 < a * b * (1 - s₂) := mul_pos (mul_pos ha hb) h2
  unfold gapInvariant
  rw [div_lt_div_iff₀ d1 d2]
  have expand : ((a + b) ^ 2 - 4 * (a * b * (1 - s₂))) * (a * b * (1 - s₁))
      - ((a + b) ^ 2 - 4 * (a * b * (1 - s₁))) * (a * b * (1 - s₂))
      = a * b * (a + b) ^ 2 * (s₂ - s₁) := by ring
  have key : 0 < a * b * (a + b) ^ 2 * (s₂ - s₁) :=
    mul_pos (mul_pos (mul_pos ha hb) (pow_pos (by linarith) 2)) (by linarith)
  linarith

/-- **The magnetic coupling raises the physical gap invariant.**  Strict monotonicity, so the
witness below is one point of a monotone family rather than an isolated coincidence. -/
theorem theMagneticCouplingRaisesThePhysicalGapInvariant (ut us₁ us₂ : ℚ) (h0 : 0 < ut)
    (h1 : ut < 1) (k0 : 0 ≤ us₁) (k1 : us₁ < us₂) (k2 : us₂ < 1) :
    plaquetteGapInvariant ut us₁ < plaquetteGapInvariant ut us₂ := by
  have ha : (0 : ℚ) < (1 + ut) ^ 4 := pow_pos (by linarith) 4
  have hb : (0 : ℚ) < (1 - ut) ^ 4 := pow_pos (by linarith) 4
  have hsq : us₁ ^ 2 < us₂ ^ 2 := by nlinarith
  have hsq2 : us₂ ^ 2 < 1 := by nlinarith
  exact theGapInvariantRisesWithTheMagneticParameter _ _ _ _ ha hb hsq hsq2

/-- **The magnetic coupling moves the physical gap, at two exhibited rational points.**  This is
the file's second falsifier run: at `u_t = 1/2` the invariant is `6400/81` at `u_s = 0` and
`25924/243` at `u_s = 1/2`.  Had they agreed, the construction would be a tensor-power tautology
and the file would have to be withdrawn rather than patched. -/
theorem theMagneticCouplingMovesThePhysicalGap :
    plaquetteGapInvariant (1 / 2) 0 = 6400 / 81 ∧
      plaquetteGapInvariant (1 / 2) (1 / 2) = 25924 / 243 ∧
      plaquetteGapInvariant (1 / 2) 0 ≠ plaquetteGapInvariant (1 / 2) (1 / 2) := by
  refine ⟨by norm_num [plaquetteGapInvariant, gapInvariant], ?_, ?_⟩
  · norm_num [plaquetteGapInvariant, gapInvariant]
  · norm_num [plaquetteGapInvariant, gapInvariant]

/-- **The second falsifier, stated so it can be checked.**  If the magnetic coupling carried no
spectral content, the returned classification would be the preimage of a field the construction
authored. -/
def TheMagneticCouplingIsSpectrallyInert : Prop :=
  ∀ ut us : ℚ, plaquetteGapInvariant ut us = plaquetteGapInvariant ut 0

/-- **The second falsifier does not fire.** -/
theorem theMagneticCouplingIsNotSpectrallyInert : ¬ TheMagneticCouplingIsSpectrallyInert := by
  intro h
  exact theMagneticCouplingMovesThePhysicalGap.2.2 (h (1 / 2) (1 / 2)).symm

/-- **The physical spectrum leaves `ℚ` at the witness point, and the file never follows it there.**

At `u_t = u_s = 1/2` the discriminant is `6481/256`, and `6481` is prime, so neither eigenvalue is
rational and the gap ratio is a quadratic irrational.  Every theorem in section 6 is nevertheless
stated on `trace`, `det` and `(tr² − 4 det)/det`, which are rational; that is what "no square root
is taken anywhere" means, and this theorem is what makes the phrase a claim rather than a habit.

Imported and not proved here: irrationality of the square root of a prime, and the primality of
`6481` is discharged by `norm_num`. -/
theorem thePlaquetteSpectrumLeavesTheRationals : ¬ ∃ x : ℚ, x ^ 2 = 6481 / 256 := by
  rintro ⟨x, hx⟩
  have h : (16 * x) ^ 2 = (6481 : ℚ) := by rw [mul_pow, hx]; norm_num
  have hy : ((16 * x : ℚ) : ℝ) ^ 2 = ((6481 : ℕ) : ℝ) := by exact_mod_cast h
  have hp : Nat.Prime 6481 := by norm_num
  have hirr : Irrational (Real.sqrt ((6481 : ℕ) : ℝ)) := hp.irrational_sqrt
  rw [← hy, Real.sqrt_sq_eq_abs, ← Rat.cast_abs] at hirr
  exact (Rat.not_irrational _) hirr

/-- **And the discriminant at that point really is `6481/256`.**  So the theorem above is about the
witness the file exhibits, not about a number chosen to be irrational. -/
theorem theWitnessDiscriminantIsTheStatedRational :
    ((1 + (1 : ℚ) / 2) ^ 4 + (1 - (1 : ℚ) / 2) ^ 4) ^ 2
        - 4 * ((1 + (1 : ℚ) / 2) ^ 4 * (1 - (1 : ℚ) / 2) ^ 4 * (1 - ((1 : ℚ) / 2) ^ 2))
      = 6481 / 256 := by
  norm_num

/-! ## 7. The bar: no gap language without a scaling family

This development's standing bar on this target is that a lattice figure may not be quoted as a
physical gap without a continuum limit carrying a lattice spacing, a volume and a scaling of a
correlation length.  Here the bar is proved rather than declared. -/

/-- What a continuum gap would have to exhibit: a spacing refining to nothing and a gap sequence
whose ratio to the spacing settles on a positive limit. -/
def AScalingFamilyRelatesTheGapToASpacing (gap spacing : ℕ → ℚ) (Δ : ℚ) : Prop :=
  0 < Δ ∧ (∀ n, 0 < spacing n) ∧
    (∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → spacing n < ε) ∧
    (∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |gap n / spacing n - Δ| < ε)

/-- **A gap held fixed in lattice units has no continuum limit.**  No spacing refinement and no
positive `Δ` satisfy the relation.  So a lattice gap figure is not a physical gap awaiting a
conversion factor; without a family relating the coupling to the spacing there is nothing for the
figure to converge to, and this file carries no such family. -/
theorem theFixedLatticeGapAdmitsNoContinuumLimit (g : ℚ) (hg : 0 < g) (spacing : ℕ → ℚ) (Δ : ℚ) :
    ¬ AScalingFamilyRelatesTheGapToASpacing (fun _ => g) spacing Δ := by
  rintro ⟨hΔ, hpos, hto0, hconv⟩
  obtain ⟨N₁, hN₁⟩ := hconv 1 one_pos
  have hden : (0 : ℚ) < Δ + 2 := by linarith
  have hden' : (Δ : ℚ) + 2 ≠ 0 := ne_of_gt hden
  obtain ⟨N₂, hN₂⟩ := hto0 (g / (Δ + 2)) (div_pos hg hden)
  have habs : |g / spacing (max N₁ N₂) - Δ| < 1 := hN₁ _ (le_max_left _ _)
  have hsmall : spacing (max N₁ N₂) < g / (Δ + 2) := hN₂ _ (le_max_right _ _)
  have hs : 0 < spacing (max N₁ N₂) := hpos _
  have hs' : spacing (max N₁ N₂) ≠ 0 := ne_of_gt hs
  rw [abs_lt] at habs
  have hlow : spacing (max N₁ N₂) * (Δ + 2) < g := by
    calc spacing (max N₁ N₂) * (Δ + 2) < g / (Δ + 2) * (Δ + 2) :=
          mul_lt_mul_of_pos_right hsmall hden
      _ = g := by field_simp
  have hhigh : g < (Δ + 1) * spacing (max N₁ N₂) := by
    have hr : g / spacing (max N₁ N₂) < Δ + 1 := by linarith [habs.2]
    calc g = g / spacing (max N₁ N₂) * spacing (max N₁ N₂) := by field_simp
      _ < (Δ + 1) * spacing (max N₁ N₂) := mul_lt_mul_of_pos_right hr hs
  linarith

/-! ## 8. What is not established here

Two items are named `Prop`s, each with its falsifier, never an axiom and never a `sorry`.  Neither
is `True` in disguise: each is a real statement whose truth is not settled by anything above.  Two
further items are recorded in words at the end of this section, with the reason no `Prop` is
deposited for them — because in this carrier the only formulations available were `False` in
disguise and vacuously satisfiable respectively, and a fake open item misleads a later reader
exactly as much as a fake theorem does. -/

/-- The configuration-basis crossing on `n` links: the tensor power of `!![1, u; u, 1]`, written
directly as a product over links. -/
def configurationCrossing {n : ℕ} (u : ℚ) (a b : Fin n → ZMod 2) : ℚ :=
  ∏ e : Fin n, (if a e = b e then 1 else u)

/-- The character `χ_S`, as a sign on configurations. -/
def characterSign {n : ℕ} (S : Finset (Fin n)) (b : Fin n → ZMod 2) : ℚ :=
  (-1) ^ (S.filter fun e => b e = 1).card

/-- **The character basis is declared, not derived.**

Sections 2 and 3 work in the character basis and state the spectrum there; nothing above proves
that the declared diagonal really is the configuration-basis crossing in another basis.  The
statement that would close it is the eigenvector equation below, and it is **proved for no `n`
here** — mathlib at `v4.27.0` carries no Kronecker-preserves-positivity lemma to lean on
(`grep -ic "kronecker" Mathlib/LinearAlgebra/Matrix/PosDef.lean` → 0, measured 2026-08-21), so the
transform would have to be proved by induction on the link count.

*Falsifier: an `n`, a `u`, an `S` and an `a` at which the two sides differ.  If one exists, every
spectral statement in sections 2 and 3 is a statement about a declared diagonal and about nothing
else, and the word "crossing" in their names is unearned.* -/
def TheCharacterIsAnEigenvectorOfTheConfigurationCrossing : Prop :=
  ∀ (n : ℕ) (u : ℚ) (S : Finset (Fin n)) (a : Fin n → ZMod 2),
    ∑ b : Fin n → ZMod 2, configurationCrossing u a b * characterSign S b
      = characterCrossing u S * characterSign S a

/-- **The cycle space is computed by exhaustion at three sizes, and three sizes are not a family.**

Section 3 settles the three-, four- and five-link circles by `decide`.  The statement for every
circle is not proved here, and the gauged-sector theorems are therefore statements about a sector
that has been *checked* at three volumes rather than *derived* at all of them.

*Falsifier: a circle length at which some non-constant assignment is annihilated by the boundary
map.  If one exists, the physical sector is larger than two elements at that volume and the
volume law of section 3 is wrong there.* -/
def TheCycleSpaceIsTheConstantSectorForEveryCircle : Prop :=
  ∀ L : ℕ, 3 ≤ L → ∀ f : ZMod L → ZMod 2, circleCycle L f → ∀ v, f v = f 0

/-! ### Two things that are NOT deposited as `Prop`s, and why

**The sharper anti-vacuity witness.**  That a `2 × 2` block's discriminant depends on its own
off-diagonal entry is nearly automatic, so section 6 moves the question one step rather than
settling it.  The witness that would settle it is the `2 × 2` periodic net — eight links, four
plaquettes, cycle-space dimension five, a physical block of dimension thirty-two — whose spectrum
is not closed form and whose minimal-cycle reading can genuinely be wrong.  **No `Prop` is stated
for it here**, because every formulation available in this carrier is either about an object the
file does not build or is settled by an unintended witness: the first draft of one, `∀ g : ℚ → ℚ,
∃ u_t u_s, g (gap u_t u_s) ≠ gap u_t u_s`, is refuted by the identity function and was therefore
`False` in disguise, which is exactly as defective as `True` in disguise.  The open item is
recorded here in words, with its discharge: build the thirty-two-dimensional physical block over
`ℚ`, compute its characteristic polynomial exactly, and read the gap by sector.

**The continuum family.**  Section 7 proves that a gap fixed in lattice units admits no continuum
limit; what it does not do is exhibit any family at all — no function from a coupling to a lattice
spacing, no correlation length, no volume sequence carrying one.  **No `Prop` is stated for it
here either.**  Any statement of the form *there exist a spacing law, a coupling sequence and a
`Δ > 0` satisfying the scaling relation* is satisfiable in this carrier by choosing the spacing law
to be the gap itself, so it would be a fake open item: true, cheap, and asserting nothing about the
physics.  What makes the classical question non-trivial is that the spacing law is fixed
independently, by a renormalization condition — asymptotic freedom in the Yang–Mills case (Gross
and Wilczek, and Politzer, 1973) — and this carrier cannot express one.  That is the honest form of
this development's bar: **no mass-gap language without a scaling family, and no scaling family
without a law fixing the spacing before the gap is measured.**  For `Z₂` in three dimensions the
Wegner (1971) duality with the Ising model says what to expect anyway: the transition is the
gapless Ising fixed point, so there is no positive continuum gap to find. -/

end Soma.Holonics.Millennium.LatticeNet
