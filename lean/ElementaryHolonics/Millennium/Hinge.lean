import Mathlib.Tactic
import Mathlib.Combinatorics.Matroid.Circuit

/-!
# Hinge: the body-hinge flex, and the cocircuit reading of the degree of redundancy

A **body-hinge** pattern is what a rigidity count collapses to.  Replace each rigid piece of a bar
framework by one planar infinitesimal rigid motion `M = (a, b, c)`, acting as
`p ↦ (a − c·p₂, b + c·p₁)`; then every bar *inside* a piece is stationary for free, and the only
surviving equations are the ones at the shared vertices.  This file is the exact rational calculus
of that reduction, and one consequence of it.

## What is proved

* **The motion stationarizes every bar** — `theMotionStationarizesEveryBar`, one `ring`.  This is
  the gauge, and it is the entire source of the `−3` in the Laman count `2|X| − 3`.  It is also the
  labour-saving of the whole file: *one* lemma discharges every within-piece bar equation, however
  many bars a piece has.
* **A hinge is a coboundary condition** — `theHingeIsACoboundaryCondition`.  Two motions agree at a
  point `h` exactly when their translation difference is the rotation-rate difference times `h`,
  read off the two coordinates with opposite hands.  So on the hinge graph (nodes = pieces,
  edges = shared vertices) the only conditions are that two explicit `1`-cochains built from
  `δc` be coboundaries — two conditions per independent cycle.
* **The triangle of bodies is rigid off the hinge area** —
  `theTriangleOfBodiesIsRigidOffTheHingeArea`, for *arbitrary* rational hinges.  The obstruction is
  the `3 × 3` determinant `det[[1,1,1],[h₁ₓ,h₂ₓ,h₃ₓ],[h₁ᵧ,h₂ᵧ,h₃ᵧ]]`, which
  `theHingeAreaIsTheThreeByThreeDeterminant` identifies with twice the signed area of the hinge
  triangle.  Nonzero area forces `M₁ = M₂ = M₃`; the proof is Cramer's rule written out as two
  `linear_combination`s.
* **Its control: the collinear triangle flexes** — `theCollinearTriangleOfBodiesFlexes`, at hinges
  `(0,0), (1,0), (2,0)`, with `M₁ = (0,0,0)`, `M₂ = (0,0,−1)`, `M₃ = (0,−2,1)` satisfying all three
  hinge conditions and `M₁ ≠ M₂`.  **The count cannot tell the two triangles apart**: three pieces,
  three hinges, cycle rank one, the same `Σ(2|Xᵢ| − 3)` on both.  Only the orientation datum can,
  and `theSeparatingDatumIsTheHingeArea` exhibits it as `1` against `0`.  This is the
  phase-object reading at the level of a configuration, and it is why the generic combinatorial
  oracle (below) answers *rigid* for both.
* **The quadrilateral of bodies flexes** — `theQuadrilateralOfBodiesFlexes`, at the unit square's
  corners, with `M₁ = (0,0,0)`, `M₂ = (0,0,1)`, `M₃ = (0,1,0)`, `M₄ = (1,0,1)` satisfying all eight
  scalar hinge equations, together with `theQuadrilateralFlexIsNotOneMotion`, which exhibits the
  non-hinge point `(2,3)` where two of the fields disagree.  That last is not decoration: a witness
  satisfying every hinge equation could still have been one motion in disguise, and this is the
  check that it is not.
* **The assembled brace-free cycle carries the flex** — `theBraceFreeBodyCycleCarriesTheFlex`
  packages the two: every bar inside every piece is stationary, all four hinges agree, and the
  assembled field is not a single motion.  It holds for *arbitrary* point sets inside the four
  pieces, which is the sense in which one lemma stands in for forty bar equations.
* **The cocircuit reading of the degree of redundancy** — `theCocircuitIsTheMinimalBasisMeetingSet`
  and `theCocircuitIsTheMinimalRankDroppingSet`, both discharged by Mathlib's own
  `Matroid.isCocircuit_iff_minimal` and `Matroid.isCocircuit_iff_minimal_compl_nonspanning`.  A
  deletion set drops the rank iff it meets every basis, so the minimal ones are exactly the
  cocircuits and the answer to *"how few bars destroy rigidity"* is the **cogirth**, defined here as
  `cogirth`.  `theCogirthIsAtMostEveryCocircuit` grounds that definition against an exhibited
  cocircuit.

`theMotionStationarizesEveryBar`, `theHingeAreaIsTheThreeByThreeDeterminant` and
`theSeparatingDatumIsTheHingeArea` are `ring`/`norm_num`-class facts and say so; nothing here hides
a computation behind a tactic that could not have failed, and both controls — the collinear flex
against the non-collinear rigidity, and the separating non-hinge point against the hinge
agreements — can come out the other way and are the reason the positive statements carry anything.

## What is refused, and what is only recorded

**Parts two and three of the specification are NOT formalized here.**  They need a generic rigidity
matroid, a `(2,3)`-pebble game and an integer max-flow, none of which exists in `Mathlib` and none
of which this file builds.  What is formalized is `cogirth` and the cocircuit characterization; the
separation itself is stated as the named-open predicate
`theCogirthSitsStrictlyBelowEveryCutReading` and **is not proved**.  A predicate applied to an
arbitrary matroid is satisfiable by an arbitrary matroid: the load-bearing half — that the matroid
in question is the generic planar rigidity matroid of the graph below — is exactly the half not
carried in Lean, and saying otherwise would be the defect this repository convicts elsewhere.

**The intended witness, measured 2026-08-21 and recorded so a later session need not re-derive it.**
`G*` is four copies of `K₅` identified cyclically at four hinge vertices — `B₁ ∩ B₂ = {h₁}`,
`B₂ ∩ B₃ = {h₂}`, `B₃ ∩ B₄ = {h₃}`, `B₄ ∩ B₁ = {h₄}` — plus two brace edges joining interior
vertices of `B₁` to interior vertices of `B₃`.  Measured by an exact `(2,3)`-pebble game
(integer arithmetic, no floats) and an integer Ford–Fulkerson max-flow, over the whole vertex set
and all `42` edges and all `C(42,2) = 861` pairs:

```text
n = 16   m = 42   2n − 3 = 29
rank(G* minus both braces) = 28 = 2n − 4        exactly one degree of freedom
rank(G* minus one brace)   = 29                 one brace kills it
rank(G*)                   = 29                 G* is rigid
coloops                    = none               G* is REDUNDANTLY rigid
size-2 rank-dropping pairs = {b₁, b₂} and nothing else
  ⟹ d(G*) = 2, and the minimum cocircuit population is the single pair {b₁, b₂}
δ(G*) = 4    λ(G*) = 4    min_v λ(G* − v) = 3    m − 2n + 4 = 14
  ⟹ d(G*) = 2 < 3 = the least of the four polynomial cut readings
```

The pebble game was validated first against `K₃…K₇` (ranks `3,5,7,9,11`), `K₅ − e` (`7`, rigid),
`C₄` (`4`), `K₃,₃` (`9`, rigid), and rank-invariance over 200 random edge orderings.  It then
reproduced this file's own flex arithmetic independently: two `K₅` at one hinge returned
`2n − 4` (`t = 2, γ = 0`, one freedom), three `K₅` in a hinge cycle returned `2n − 3` (`t = 3,
γ = 1`, rigid), four `K₅` in a hinge cycle returned `2n − 4` (`t = 4, γ = 1`, one freedom) — which
is `(t − 1) − 2γ` in all three cases.  Note what that cross-check *cannot* see: it answers *rigid*
for the three-body cycle because it is a generic combinatorial oracle, while
`theCollinearTriangleOfBodiesFlexes` exhibits a placement of the same pattern that flexes.  The
budget `2γ + 2 ≤ t` is the generic condition, and `hingeBudgetAdmitsAFlex` is named for it, with
`theBudgetRefusesThreeBodiesAndAdmitsFour` discharging the two instances this file also settles by
exhibited flexes.

**The pinning problem is not open the way it is usually listed, and this correction is part of the
deed.**  For **rigid** graphs the minimum pinning set for generic global rigidity in the plane is
computable in polynomial time, and has been since 2021: Király and Mihálykó (EGRES TR-2021-04;
SIAM J. Discrete Math. 36(4), 2022) prove that the optimum takes **one vertex from each atom**, the
atoms being pairwise disjoint, and their argument is combinatorial — MCT sets, 3-ends, atoms — and
never touches a stress matrix.  A listing of the pinning problem as open is accurate **only for the
non-rigid class**, where their factor-`2` approximation (pin to rigid by Fekete 2006, then pin the
rigid result to globally rigid) is the best known.  Any reading of pinning as *realizer supply* that
presents itself as adding a step to the rigid case is a restatement of a solved theorem; the
surviving open half is narrow and specific, and it is the non-rigid one.

**Provenance and imports, graded honestly.**  The inequality `2γ + 2 ≤ t` is rederived here from
the hinge coboundary conditions and is algebraically the Lovász–Yemini budget rewritten; it is
almost certainly folklore in the body-hinge counting literature (Tay–Whiteley 1984 and successors)
and is graded *rederived, provenance unverified* — a search that did not find it measures the
search.  The exhaustiveness of the `1`-thin cover family rests on Lovász–Yemini (1982) and on the
fact that the rigidity matroid's components induce a `1`-thin cover (Berg–Jordán 2003); **both are
imported and neither is verified here**, so the upper-bound half of any tightness claim survives and
the tightness half does not.  Reading the reflection across a `2`-separator as a defect invisible to
every distance receiver is Hendrickson's 1992 observation in other words, and renaming it buys
nothing on its own.  And the separation itself is a foothold rather than a result: every minimally
rigid graph already has cogirth `1` while its edge connectivity is at least `2`, so *cogirth is not
a cut* is trivially true and known — what `G*` adds is that the separation persists **inside the
redundantly rigid class**, with both directions closed exactly and the causing pattern named.  One
gap is in the derivation rather than in the literature: the merging analysis behind the cycle-rank
parametrization was done for connected hinge structures only, and mixed covers — several components,
some carrying cycles — were not analysed at all.

**Cited, not proved here** (each a classical theorem about real frameworks): Asimow–Roth (1978) for
the rigidity matrix, `ker R` = infinitesimal flexes and `ker Rᵀ` = self-stresses; Laman (1970) for
the `(2,3)`-count characterization of independence; Lovász–Yemini (1982) for the `1`-thin cover rank
formula; Hendrickson (1992) for the necessity of redundant rigidity and `3`-connectivity;
Jackson–Jordán (2005) for their sufficiency at `n ≥ 4`; Connelly (2005) and Gortler–Healy–Thurston
(2010) for the maximal-rank stress characterization of generic global rigidity; Jacobs–Hendrickson
(1997) and Lee–Streinu (2008) for the pebble game; Jensen–Korte (1982) for the independence-oracle
lower bound; Cunningham (1985) for the polynomially solved `(k,k)` analogue.  Nothing below states
or uses any of them.

**Measured 2026-08-21** over `Mathlib` at `v4.27.0`, from
`.lake/packages/mathlib`: `grep -rli "cogirth" Mathlib --include='*.lean'` → 0 files; likewise
`"pebble"` → 0, `"rigidity matroid"` → 0, `"infinitesimal flex"` → 0, `"laman"` → 0,
`"bar framework"` → 0.  Those commands measure those names over that scope and are not a claim that
no related content exists under another name; `Mathlib.Combinatorics.Matroid` does exist and is used
here for the cocircuit statements.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here is a claim about any
named conjecture: `theCogirthSitsStrictlyBelowEveryCutReading` and `hingeBudgetAdmitsAFlex` are
`def`s naming propositions, not theorems asserting them, and the boundary is that this file settles
the hinge calculus over `ℚ` and settles nothing about the complexity of computing a cogirth.
-/

namespace Soma.Holonics.Millennium.Hinge

/-! ## 1. The carriers

A planar point over `ℚ`, the dot pairing written out, and a planar infinitesimal rigid motion as
the triple `(a, b, c)` — translation `(a, b)` plus rotation rate `c`. -/

/-- A planar point (or velocity) over `ℚ`. -/
abbrev Pt : Type := ℚ × ℚ

/-- The planar dot pairing, written out. -/
def dot (a b : Pt) : ℚ := a.1 * b.1 + a.2 * b.2

/-- A planar infinitesimal rigid motion: translation `(a, b)` and rotation rate `c`. -/
abbrev Motion : Type := ℚ × ℚ × ℚ

/-- The velocity a motion assigns to a point: `p ↦ (a − c·p₂, b + c·p₁)`. -/
def vel (M : Motion) (p : Pt) : Pt := (M.1 - M.2.2 * p.2, M.2.1 + M.2.2 * p.1)

/-! ## 2. The motion stationarizes every bar

Every bar inside a rigid piece is free, for one reason, once.  This is the gauge — the three
parameters no relative measurement sees — and it is where the `−3` of `2|X| − 3` comes from.  It is
also the entire economy of the body-hinge reduction: however many bars a piece carries, they are all
discharged by this single lemma. -/

/-- **The motion stationarizes every bar.**  For any motion and any two points, the bar vector is
orthogonal to the relative velocity, so the bar's length is stationary at first order. -/
theorem theMotionStationarizesEveryBar (M : Motion) (p q : Pt) :
    dot (p - q) (vel M p - vel M q) = 0 := by
  simp only [dot, vel, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The velocity field determines the motion.**  Two samples suffice: the value at the origin
fixes the translation and the value at `(1,0)` then fixes the rotation rate.  This is what makes
"the assembled field is not one motion" checkable by exhibiting a single disagreeing point. -/
theorem theVelocityFieldDeterminesTheMotion (M N : Motion)
    (h0 : vel M (0, 0) = vel N (0, 0)) (h1 : vel M (1, 0) = vel N (1, 0)) : M = N := by
  obtain ⟨a, b, c⟩ := M
  obtain ⟨a', b', c'⟩ := N
  simp only [vel, Prod.mk.injEq] at h0 h1
  obtain ⟨e1, e2⟩ := h0
  obtain ⟨-, e3⟩ := h1
  norm_num at e1 e2 e3
  have hc : c = c' := by linarith
  subst e1; subst e2; subst hc; rfl

/-! ## 3. The hinge is a coboundary condition

Two pieces sharing a vertex must assign it the same velocity.  Written out, that is two scalar
equations in the *difference* of the two rotation rates, with the two coordinates entering with
opposite hands.  On the hinge graph — nodes the pieces, edges the shared vertices — this says
exactly that two explicit `1`-cochains built from `δc` are coboundaries, which is two conditions per
independent cycle. -/

/-- **The hinge condition, written as a coboundary condition.**  `vel M h = vel N h` holds exactly
when the translation difference is the rotation-rate difference against `h`, with the sign carrying
the hand. -/
theorem theHingeIsACoboundaryCondition (M N : Motion) (h : Pt) :
    vel M h = vel N h ↔
      (M.1 - N.1 = (M.2.2 - N.2.2) * h.2 ∧ M.2.1 - N.2.1 = -((M.2.2 - N.2.2) * h.1)) := by
  simp only [vel, Prod.mk.injEq]
  constructor
  · rintro ⟨u, v⟩
    exact ⟨by linear_combination u, by linear_combination v⟩
  · rintro ⟨u, v⟩
    exact ⟨by linear_combination u, by linear_combination v⟩

/-! ## 4. The triangle of bodies, and the determinant that decides it

Three pieces hinged in a cycle: cycle rank `γ = 1`, `t = 3` pieces, so the budget `2γ + 2 ≤ t`
fails and the pattern should be rigid.  It is — but only off a determinant, and the determinant is
invisible to the count. -/

/-- Twice the signed area of the hinge triangle. -/
def hingeArea (h1 h2 h3 : Pt) : ℚ :=
  (h2.1 - h1.1) * (h3.2 - h1.2) - (h3.1 - h1.1) * (h2.2 - h1.2)

/-- **The hinge area is the obstruction determinant.**  It equals
`det[[1,1,1],[h₁ₓ,h₂ₓ,h₃ₓ],[h₁ᵧ,h₂ᵧ,h₃ᵧ]]`, expanded along the first row.  *The proof is `ring`.* -/
theorem theHingeAreaIsTheThreeByThreeDeterminant (h1 h2 h3 : Pt) :
    hingeArea h1 h2 h3 =
      (h2.1 * h3.2 - h3.1 * h2.2) - (h1.1 * h3.2 - h3.1 * h1.2)
        + (h1.1 * h2.2 - h2.1 * h1.2) := by
  simp only [hingeArea]
  ring

/-- **The triangle of bodies is rigid off the hinge area.**  Three motions agreeing pairwise at
three hinges of nonzero hinge area are equal.  The three rotation-rate differences sum to zero
identically and satisfy two further equations; Cramer's rule on that `3 × 3` homogeneous system
multiplies each difference by the determinant, so a nonzero determinant kills them all, and the
translations follow.  Holds for arbitrary rational hinges. -/
theorem theTriangleOfBodiesIsRigidOffTheHingeArea
    (M1 M2 M3 : Motion) (h1 h2 h3 : Pt)
    (e12 : vel M1 h1 = vel M2 h1)
    (e23 : vel M2 h2 = vel M3 h2)
    (e31 : vel M3 h3 = vel M1 h3)
    (hA : hingeArea h1 h2 h3 ≠ 0) :
    M1 = M2 ∧ M2 = M3 := by
  obtain ⟨a12, b12⟩ := (theHingeIsACoboundaryCondition M1 M2 h1).mp e12
  obtain ⟨a23, b23⟩ := (theHingeIsACoboundaryCondition M2 M3 h2).mp e23
  obtain ⟨a31, b31⟩ := (theHingeIsACoboundaryCondition M3 M1 h3).mp e31
  have hAeq : (M1.2.2 - M2.2.2) * (h1.2 - h3.2) + (M2.2.2 - M3.2.2) * (h2.2 - h3.2) = 0 := by
    linear_combination -a12 - a23 - a31
  have hBeq : (M1.2.2 - M2.2.2) * (h1.1 - h3.1) + (M2.2.2 - M3.2.2) * (h2.1 - h3.1) = 0 := by
    linear_combination b12 + b23 + b31
  have hx : hingeArea h1 h2 h3 * (M1.2.2 - M2.2.2) = 0 := by
    simp only [hingeArea]
    linear_combination (-(h2.1 - h3.1)) * hAeq + (h2.2 - h3.2) * hBeq
  have hy : hingeArea h1 h2 h3 * (M2.2.2 - M3.2.2) = 0 := by
    simp only [hingeArea]
    linear_combination (h1.1 - h3.1) * hAeq + (-(h1.2 - h3.2)) * hBeq
  have c12 : M1.2.2 - M2.2.2 = 0 := by
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h hA
    · exact h
  have c23 : M2.2.2 - M3.2.2 = 0 := by
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd h hA
    · exact h
  constructor
  · rw [Prod.ext_iff]
    refine ⟨by linear_combination a12 + h1.2 * c12, ?_⟩
    rw [Prod.ext_iff]
    exact ⟨by linear_combination b12 - h1.1 * c12, by linear_combination c12⟩
  · rw [Prod.ext_iff]
    refine ⟨by linear_combination a23 + h2.2 * c23, ?_⟩
    rw [Prod.ext_iff]
    exact ⟨by linear_combination b23 - h2.1 * c23, by linear_combination c23⟩

/-- The non-collinear hinge triangle. -/
def n1 : Pt := (0, 0)
/-- The non-collinear hinge triangle. -/
def n2 : Pt := (1, 0)
/-- The non-collinear hinge triangle. -/
def n3 : Pt := (0, 1)

/-- The collinear hinge triangle: the same three pieces, the same three hinges, the same count. -/
def c1 : Pt := (0, 0)
/-- The collinear hinge triangle. -/
def c2 : Pt := (1, 0)
/-- The collinear hinge triangle. -/
def c3 : Pt := (2, 0)

/-- **The separating datum is the hinge area, and only the hinge area.**  The two triangles carry
the same number of pieces, the same number of hinges, the same cycle rank and the same
`Σ(2|Xᵢ| − 3)`; the areas are `1` and `0`.  *The proof is `norm_num`* — the point is not the
computation but that the count is absent from it. -/
theorem theSeparatingDatumIsTheHingeArea :
    hingeArea n1 n2 n3 = 1 ∧ hingeArea c1 c2 c3 = 0 := by
  constructor <;> norm_num [hingeArea, n1, n2, n3, c1, c2, c3]

/-- **The non-collinear triangle of bodies is rigid.**  Three pieces hinged at `(0,0)`, `(1,0)`,
`(0,1)` are forced into one common motion. -/
theorem theNonCollinearTriangleOfBodiesIsRigid (M1 M2 M3 : Motion)
    (e12 : vel M1 n1 = vel M2 n1) (e23 : vel M2 n2 = vel M3 n2) (e31 : vel M3 n3 = vel M1 n3) :
    M1 = M2 ∧ M2 = M3 :=
  theTriangleOfBodiesIsRigidOffTheHingeArea M1 M2 M3 n1 n2 n3 e12 e23 e31
    (by rw [theSeparatingDatumIsTheHingeArea.1]; norm_num)

/-! ## 5. The control: the collinear triangle flexes

The same pattern, the same count, hinges moved onto a line.  A rational witness exists and is
exhibited.  This is the control that makes the theorem above a finding rather than a tautology: the
hypothesis `hingeArea ≠ 0` can fail, and when it fails the conclusion fails with it. -/

/-- The collinear witness: the first piece stands still. -/
def L1 : Motion := (0, 0, 0)
/-- The collinear witness: the second piece turns backwards about the shared origin. -/
def L2 : Motion := (0, 0, -1)
/-- The collinear witness: the third piece turns forwards, translated to match. -/
def L3 : Motion := (0, -2, 1)

/-- **The collinear triangle of bodies flexes.**  All three hinge conditions hold at `(0,0)`,
`(1,0)`, `(2,0)`, and the first two motions differ.  Same piece count, same hinge count, same cycle
rank as the rigid triangle — the count is blind to the difference. -/
theorem theCollinearTriangleOfBodiesFlexes :
    vel L1 c1 = vel L2 c1 ∧ vel L2 c2 = vel L3 c2 ∧ vel L3 c3 = vel L1 c3 ∧ L1 ≠ L2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [vel, L1, L2, L3, c1, c2, c3, Prod.ext_iff]

/-- **The collinear flex is seen at a non-hinge point.**  At `(3,5)` the first two pieces assign
`(0,0)` and `(5,−3)`, so the assembled field is genuinely two fields and not one motion wearing two
labels. -/
theorem theCollinearFlexSeparatesAtANonHingePoint : vel L1 (3, 5) ≠ vel L2 (3, 5) := by
  norm_num [vel, L1, L2, Prod.ext_iff]

/-! ## 6. The quadrilateral of bodies flexes

Four pieces hinged in a cycle: `t = 4`, `γ = 1`, so the budget `2γ + 2 ≤ t` is met with equality —
three unknowns in the rotation-rate difference space against two conditions — and a flex is forced
for *every* placement of the hinges.  This is the four-bar linkage, and here it is over `ℚ` at the
unit square. -/

/-- The quadrilateral's hinges: the corners of the unit square. -/
def q1 : Pt := (0, 0)
/-- The quadrilateral's hinges. -/
def q2 : Pt := (1, 0)
/-- The quadrilateral's hinges. -/
def q3 : Pt := (1, 1)
/-- The quadrilateral's hinges. -/
def q4 : Pt := (0, 1)

/-- The quadrilateral witness, first piece. -/
def Q1 : Motion := (0, 0, 0)
/-- The quadrilateral witness, second piece. -/
def Q2 : Motion := (0, 0, 1)
/-- The quadrilateral witness, third piece. -/
def Q3 : Motion := (0, 1, 0)
/-- The quadrilateral witness, fourth piece. -/
def Q4 : Motion := (1, 0, 1)

/-- **The quadrilateral of bodies flexes.**  All four hinge equalities hold — eight scalar
equations — at the corners of the unit square. -/
theorem theQuadrilateralOfBodiesFlexes :
    vel Q1 q1 = vel Q2 q1 ∧ vel Q2 q2 = vel Q3 q2 ∧
      vel Q3 q3 = vel Q4 q3 ∧ vel Q4 q4 = vel Q1 q4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [vel, Q1, Q2, Q3, Q4, q1, q2, q3, q4, Prod.ext_iff]

/-- **The quadrilateral flex is not one motion.**  The witness could have satisfied every hinge
equation while being a single rigid motion in four disguises; it does not.  The motions differ, and
they differ at the non-hinge point `(2,3)`, where the first two assign `(0,0)` and `(−3,2)`. -/
theorem theQuadrilateralFlexIsNotOneMotion :
    Q1 ≠ Q2 ∧ vel Q1 (2, 3) ≠ vel Q2 (2, 3) := by
  constructor <;> norm_num [vel, Q1, Q2, Prod.ext_iff]

/-- The four pieces' motions, indexed. -/
def quadMotion : Fin 4 → Motion
  | 0 => Q1
  | 1 => Q2
  | 2 => Q3
  | 3 => Q4

/-- **The brace-free body cycle carries the flex.**  Three statements in one: every bar inside every
piece is stationary, for *arbitrary* points of that piece; all four hinges agree; and the assembled
field is not one motion.  The first conjunct is the whole labour saving — it stands in for every
within-piece bar equation at once, whatever the pieces are, so enlarging the pieces from triangles
to `K₅`s or to anything else costs nothing. -/
theorem theBraceFreeBodyCycleCarriesTheFlex :
    (∀ (i : Fin 4) (p q : Pt), dot (p - q) (vel (quadMotion i) p - vel (quadMotion i) q) = 0) ∧
      (vel (quadMotion 0) q1 = vel (quadMotion 1) q1 ∧
        vel (quadMotion 1) q2 = vel (quadMotion 2) q2 ∧
        vel (quadMotion 2) q3 = vel (quadMotion 3) q3 ∧
        vel (quadMotion 3) q4 = vel (quadMotion 0) q4) ∧
      vel (quadMotion 0) (2, 3) ≠ vel (quadMotion 1) (2, 3) := by
  refine ⟨fun i p q => theMotionStationarizesEveryBar _ p q, ?_, ?_⟩
  · simpa [quadMotion] using theQuadrilateralOfBodiesFlexes
  · simpa [quadMotion] using theQuadrilateralFlexIsNotOneMotion.2

/-! ## 7. The budget, named

The hinge coboundary conditions give two conditions per independent cycle of the hinge graph against
`t − 1` free rotation-rate differences, so the generic flex dimension is `(t − 1) − 2γ` and a
nontrivial flex exists generically exactly when `2γ + 2 ≤ t`.  The general statement is **not proved
here**; the predicate is named so its instances can be, and the two smallest instances are settled
above by exhibited flexes rather than by the count. -/

/-- The generic hinge budget: `t` pieces with hinge-graph cycle rank `γ` admit a nontrivial flex
exactly when this holds.  **Named, not proved** in general.  It is the *generic* condition:
`theCollinearTriangleOfBodiesFlexes` exhibits a placement with `t = 3, γ = 1` that flexes anyway,
so the budget is a statement about the combinatorial pattern and not about every configuration. -/
def hingeBudgetAdmitsAFlex (t gamma : ℕ) : Prop := 2 * gamma + 2 ≤ t

/-- **The budget refuses three bodies in a cycle and admits four.**  The two instances this file
also settles directly: `theTriangleOfBodiesIsRigidOffTheHingeArea` for the first,
`theQuadrilateralOfBodiesFlexes` for the second.  *The proof is `decide`.* -/
theorem theBudgetRefusesThreeBodiesAndAdmitsFour :
    ¬ hingeBudgetAdmitsAFlex 3 1 ∧ hingeBudgetAdmitsAFlex 4 1 := by
  constructor <;> simp only [hingeBudgetAdmitsAFlex] <;> decide

/-! ## 8. The cocircuit reading of the degree of redundancy

*How few bars must be removed to destroy rigidity* is not a fresh question: a deletion set drops the
rank exactly when it meets every basis, so the minimal such sets are the cocircuits and the answer is
the cogirth.  Both readings are Mathlib's, and quoting them here is the point — the restatement is
kernel-checked rather than asserted. -/

/-- **A cocircuit is exactly a minimal set meeting every basis.**  Mathlib's
`Matroid.isCocircuit_iff_minimal`, quoted so the reading is discharged rather than asserted: `F`
drops the rank iff `F` meets every basis. -/
theorem theCocircuitIsTheMinimalBasisMeetingSet {α : Type*} (M : Matroid α) (K : Set α) :
    M.IsCocircuit K ↔ Minimal (fun X => ∀ B, M.IsBase B → (X ∩ B).Nonempty) K :=
  Matroid.isCocircuit_iff_minimal

/-- **A cocircuit is exactly a minimal set whose deletion stops spanning.**  Mathlib's
`Matroid.isCocircuit_iff_minimal_compl_nonspanning`: the same object read as *the smallest attack
that drops the rank*, which is the form the destroying-rigidity question is posed in. -/
theorem theCocircuitIsTheMinimalRankDroppingSet {α : Type*} (M : Matroid α) (K : Set α) :
    M.IsCocircuit K ↔ Minimal (fun X => ¬ M.Spanning (M.E \ X)) K :=
  Matroid.isCocircuit_iff_minimal_compl_nonspanning

/-- The **cogirth**: the least size of a cocircuit.  For the generic planar rigidity matroid of a
rigid graph this is exactly the degree of redundancy — the fewest bars whose removal destroys
rigidity. -/
noncomputable def cogirth {α : Type*} (M : Matroid α) : ℕ∞ :=
  sInf (Set.encard '' {K | M.IsCocircuit K})

/-- **The cogirth is at most every exhibited cocircuit.**  The grounding fact for the definition:
an exhibited attack is an upper bound, which is the direction any witness supplies. -/
theorem theCogirthIsAtMostEveryCocircuit {α : Type*} (M : Matroid α) (K : Set α)
    (hK : M.IsCocircuit K) : cogirth M ≤ K.encard :=
  sInf_le ⟨K, hK, rfl⟩

/-- **NAMED OPEN — stated here, not proved here.**  The separation claim: a matroid whose cogirth is
`2` while every polynomial cut reading of the underlying graph returns at least `3`.  The intended
witness is `G*`, recorded in the module docstring with its measured values
(`d = 2`, `δ = 4`, `λ = 4`, `min_v λ(G − v) = 3`, `m − 2n + 4 = 14`, no coloops).

**The load-bearing half is deliberately absent.**  This predicate says nothing about *which*
matroid `M` is; the content of the claim is that `M` is the generic planar rigidity matroid of
`G*` and that the three numerals are that graph's cut invariants, and neither is expressible here
without a rigidity matroid and a max-flow that `Mathlib` does not carry.  Applied to an arbitrary
matroid and three arbitrary naturals this is satisfiable by arbitrary data, and it is named rather
than proved for exactly that reason. -/
def theCogirthSitsStrictlyBelowEveryCutReading {α : Type*} (M : Matroid α)
    (minDegree edgeConnectivity minVertexDeletedEdgeConnectivity : ℕ) : Prop :=
  cogirth M = 2 ∧ 3 ≤ minDegree ∧ 3 ≤ edgeConnectivity ∧
    3 ≤ minVertexDeletedEdgeConnectivity

end Soma.Holonics.Millennium.Hinge
