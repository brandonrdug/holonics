import Mathlib.Tactic

/-!
# The winding ledger — the crossings are derived, the net is a face, and two populations share one

Every polygon-level identity below is closed by kernel computation (`rfl` / `decide`) on exact
`ℤ × ℤ` carriers; the structural statements around them are proved by `omega`, `ring`, `field_simp`
and `linarith`.  Nothing is approximated and no floating point appears.

This is the Lean carrier of the crossing ledger behind
`crates/relational-geometry/src/exact_analysis.rs`'s `polygon_winding`, ported at Brandon's
direction together with the standing falsifier recorded against it — *two different crossing
populations producing the same net*.

**What is proved.**

* **The crossing event is a typed record, and it is never pre-summed.**  A `Crossing` carries where
  on the boundary it happened (`site`, the segment index in boundary order), the two endpoints that
  produced it, and the **hand** — the direction of passage.  A net is what remains after the hands
  are subtracted; the record exists so the subtraction is a later reading and not the only thing
  that survives.
* **The incidence condition is geometric, not authored.**  The sign test that decides a crossing —
  `s.2 < 0 ∧ 0 < e.2 ∧ 0 < cross s e` upward, `0 < s.2 ∧ e.2 < 0 ∧ cross s e < 0` downward — is
  proved to be exactly the statement that the segment meets the horizontal axis at a point of
  **positive** abscissa: `theCrossingSiteIsTheAffineMeetingWithTheAxis` computes the meeting point
  over `ℚ` as `cross s e / (e.2 - s.2)`, and the two hand theorems prove that quotient positive
  under each condition.  So both hands cross **one declared ray**, and the two tests are not two
  conventions but one ray read from two sides.  The two hands are also proved mutually exclusive.
* **The ledger is derived from the polygon, never declared.**  `ledger` closes the vertex list into
  indexed segments and filters them through that condition.  Five polygons are exhibited with their
  complete ledgers — site, endpoints and hand for every entry — computed, not listed as data the
  theorem then restates.  This is the rule that a returned classification may not be the preimage of
  a field the driver authored: the hand column here is a function of the coordinates.
* **The net is a receiver face of the ledger.**  `theNetIsAFaceOfTheLedger`: any two ledgers with
  the same hand column have the same net, so the net factors through a strict quotient of the
  record — it reads one column and deletes the other three.
* **THE FALSIFIER, AS A THEOREM.**  `theTwoPopulationsShareOneNet` exhibits two closed polygonal
  paths — a square around the origin, and a notched loop that crosses the ray `+ − +` — whose
  ledgers have lengths `1` and `3`, whose hand columns differ, and whose nets are **both `+1`**.
  A second instance is the cancelling pair: a loop that meets the ray twice and encloses nothing has
  the same net `0` as one that never approaches it, with totals `2` and `0`.
* **And the converse control.**  `theNetSeparatesTheEnclosingLoopFromTheStraddlingOne` and
  `theNetSeparatesALoopFromItsReversal` exhibit pairs the net *does* separate.  Without them the
  blindness above would be a receipt that could not have come out otherwise.
* **Winding about a declared point, on two polygons.**  A square winds once about an interior point
  and not at all about an exterior one; a doubled loop winds **twice**, its ledger carrying two
  distinct upward sites at abscissae `1` and `2` — not one site counted twice.  Reversing a loop
  swaps the hands and negates the net while the population size stands.
* **The declared ray is an aperture, and the aperture is exhibited moving the population.**  The
  Rust searches `k = 0 … 32` for a rotation `p ↦ (p₁ + k p₂, p₂ − k p₁)` putting no vertex on the
  axis.  `theApertureRotationScalesTheCrossByAPositiveFactor` proves that rotation multiplies every
  pairing by `1 + k²`, so it never reverses a hand; the diamond is shown to need parameter `1` and
  to become the square once rotated.  Then `theApertureMovesThePopulationAndNotTheNet`: one polygon,
  two admissible parameters, crossing populations `2` and `0`, net `0` in both.  A crossing count
  reported without its aperture is a receiver face presented as the object.

**Named open, with a real statement and two proved instances.**  `TheJumpLawAcrossOneEdge` says
that when a straight move from `a` to `b` properly crosses exactly one edge of the polygon, clears
every vertex, and leaves both endpoints transversal to the ray, the winding changes by exactly the
hand of that meeting.  It is **not proved here** for general polygons.  Two instances are proved —
entering and leaving a square, with *different* hands and jumps `+1` and `−1` — which discharges
vacuity: the hypotheses are satisfiable and the conclusion is not constant.

**Imported and not proved here** (cited so the instances are read at their true height): the
argument principle, which is what makes a crossing net a winding number for the image of an analytic
map (Cauchy); and the crossing-count algorithm for point-in-polygon and winding number
(Alciatore–Miranda 1995; Hormann–Agathos 2001).  Nothing below states or uses either; what is proved
is the exact integer combinatorics of the ledger and eleven exhibited witnesses.

**Measured 2026-08-21**, over `.lake/packages/mathlib/Mathlib` at `v4.27.0`:
`grep -rli "winding" .lake/packages/mathlib/Mathlib --include='*.lean'` → `0` files;
`grep -rli "argument principle" .lake/packages/mathlib/Mathlib --include='*.lean'` → `0` files;
`grep -rli "turning number\|rotation number" …` → `2` files.  Those commands measure those names
over that scope and are not a claim that no related content exists under another name.

`Millennium/Crossings.lean` owns the sibling object — an **authored** crossing table over strands,
its net/total inequality and its linking readings.  Nothing here duplicates it: there the population
is declared data, here it is computed from coordinates, and that difference is the whole point of
this file.

Every theorem is discharged and none depends on `sorryAx`.

**Boundary.**  This file makes no claim about Navier–Stokes, about any named conjecture, and about
any analytic function: no `η`, no `ζ`, no zero of anything appears, and the polygon here is a
polygon rather than the image of a boundary under a map.  It does not prove the argument principle,
does not prove that the crossing net equals a topological winding number, does not prove that the
net is invariant under the ray parameter in general (only that the parameter cannot reverse a hand,
plus one exhibited pair), and does not prove the jump law it names.  It owns the **ledger species** —
populations retained, nets derived — at its home carrier and nothing above it.
-/

namespace Soma.Holonics.Millennium.WindingLedger

/-! ## 1. The carrier: exact lattice points and the pairing that decides a hand -/

/-- A point of the plane over the exact integer carrier.  The Rust carrier is `RatComplex`; the
witnesses below are integral, and `ℤ` is the sub-carrier on which the kernel computes. -/
abbrev Pt : Type := ℤ × ℤ

/-- The exact pairing `a₁b₂ − a₂b₁`.  Its sign is the hand of the ordered pair. -/
def cross (a b : Pt) : ℤ := a.1 * b.2 - a.2 * b.1

/-- The hand of a passage: which way the boundary went through the ray.  This is a direction, not a
magnitude, and the file never stores it as a bare sign on a state. -/
inductive Hand where
  /-- The passage went upward through the ray, in the sense the boundary orientation declares. -/
  | withTurn
  /-- The passage went downward through the ray. -/
  | againstTurn
  deriving DecidableEq, Repr

/-- The hand read as an integer.  This is the *only* place a hand becomes a number. -/
def handSign : Hand → ℤ
  | .withTurn => 1
  | .againstTurn => -1

/-- **One crossing event.**  Position (`site`, the boundary segment index, plus the two endpoints
that produced the passage) and direction (`hand`), carried together and never pre-summed. -/
structure Crossing where
  /-- Where on the boundary: the segment index, in boundary order. -/
  site : ℕ
  /-- The endpoint the segment left. -/
  start : Pt
  /-- The endpoint the segment reached. -/
  finish : Pt
  /-- Which way it passed. -/
  hand : Hand
  deriving DecidableEq, Repr

/-- Upward through the ray: the segment leaves below the axis, arrives above it, and the pairing is
positive — which `theWithTurnCrossingSitsOnThePositiveRay` proves means the meeting abscissa is
positive. -/
def crossesWithTurn (s e : Pt) : Bool :=
  decide (s.2 < 0) && decide (0 < e.2) && decide (0 < cross s e)

/-- Downward through the same ray. -/
def crossesAgainstTurn (s e : Pt) : Bool :=
  decide (0 < s.2) && decide (e.2 < 0) && decide (cross s e < 0)

/-- **The two hands cannot both fire on one segment.**  The second coordinate of the departure point
cannot be both negative and positive. -/
theorem theTwoHandsCannotBothFire (s e : Pt) :
    ¬(crossesWithTurn s e = true ∧ crossesAgainstTurn s e = true) := by
  simp only [crossesWithTurn, crossesAgainstTurn, Bool.and_eq_true, decide_eq_true_eq]
  rintro ⟨⟨⟨h1, -⟩, -⟩, ⟨⟨h2, -⟩, -⟩⟩
  omega

/-- **The meeting point with the axis, computed exactly.**  For a segment whose endpoints sit at
different heights, the affine parameter `t = −s₂/(e₂ − s₂)` lands the segment on the axis, and the
abscissa there is exactly `cross s e / (e₂ − s₂)`.  This is what the sign tests above are testing,
and it is why they are geometry rather than convention. -/
theorem theCrossingSiteIsTheAffineMeetingWithTheAxis (s e : Pt) (d t : ℚ)
    (hd : d = (e.2 : ℚ) - (s.2 : ℚ)) (hd0 : d ≠ 0) (ht : t = -(s.2 : ℚ) / d) :
    (s.1 : ℚ) + t * ((e.1 : ℚ) - (s.1 : ℚ)) = (cross s e : ℚ) / d ∧
      (s.2 : ℚ) + t * ((e.2 : ℚ) - (s.2 : ℚ)) = 0 := by
  subst ht
  subst hd
  constructor
  · rw [eq_div_iff hd0, cross]
    push_cast
    field_simp
    ring
  · field_simp
    ring

/-- **An upward crossing sits on the positive ray.**  Numerator and denominator are both
positive. -/
theorem theWithTurnCrossingSitsOnThePositiveRay (s e : Pt) (h : crossesWithTurn s e = true) :
    0 < (cross s e : ℚ) / ((e.2 : ℚ) - (s.2 : ℚ)) := by
  simp only [crossesWithTurn, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hs, he⟩, hc⟩ := h
  apply div_pos
  · exact_mod_cast hc
  · have : (s.2 : ℚ) < (e.2 : ℚ) := by exact_mod_cast hs.trans he
    linarith

/-- **A downward crossing sits on the same positive ray.**  Numerator and denominator are both
negative, so the quotient is again positive: the two hands are two ways through **one** ray, not two
declared rays. -/
theorem theAgainstTurnCrossingSitsOnTheSamePositiveRay (s e : Pt)
    (h : crossesAgainstTurn s e = true) :
    0 < (cross s e : ℚ) / ((e.2 : ℚ) - (s.2 : ℚ)) := by
  simp only [crossesAgainstTurn, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hs, he⟩, hc⟩ := h
  have hnum : ((cross s e : ℤ) : ℚ) < 0 := by exact_mod_cast hc
  have hden : (e.2 : ℚ) - (s.2 : ℚ) < 0 := by
    have : (e.2 : ℚ) < (s.2 : ℚ) := by exact_mod_cast he.trans hs
    linarith
  exact div_pos_of_neg_of_neg hnum hden

/-! ## 2. The ledger: the crossing population of a closed polygon, computed

The boundary of a vertex list is closed — the last vertex returns to the first — and every segment
carries its index in boundary order, which is the address a receiver needs to ask *where* the
boundary is doing work.  `RayCrossings` in the Rust holds the same two arms by segment index. -/

/-- The indexed segments of a closed boundary, emitted in boundary order with the wrap-around
segment last. -/
def boundaryWalk : ℕ → Pt → List Pt → List (ℕ × Pt × Pt)
  | _, _, [] => []
  | i, first, [last] => [(i, last, first)]
  | i, first, a :: b :: t => (i, a, b) :: boundaryWalk (i + 1) first (b :: t)

/-- The closed boundary of a vertex list. -/
def closedSegments : List Pt → List (ℕ × Pt × Pt)
  | [] => []
  | v :: rest => boundaryWalk 0 v (v :: rest)

/-- The crossing event of one indexed segment, if it has one. -/
def eventOf : ℕ × Pt × Pt → Option Crossing
  | (i, s, e) =>
      if crossesWithTurn s e then some ⟨i, s, e, .withTurn⟩
      else if crossesAgainstTurn s e then some ⟨i, s, e, .againstTurn⟩
      else none

/-- **THE LEDGER.**  The crossing population of a closed polygonal path against the declared ray,
derived from the incidence condition segment by segment.  Nothing here is declared: the hand column
is a function of the coordinates. -/
def ledger (vs : List Pt) : List Crossing := (closedSegments vs).filterMap eventOf

/-- The hand column alone — the ledger with position deleted. -/
def hands (L : List Crossing) : List Hand := L.map Crossing.hand

/-- **The net**: the ledger's sum.  One reading of the population, and not the population. -/
def net (L : List Crossing) : ℤ := ((hands L).map handSign).sum

/-- **The total**: how many passages happened, both hands.  The other reading. -/
def total (L : List Crossing) : ℕ := L.length

/-- Translation of the plane so that a declared point becomes the ray's basepoint. -/
def shift (c p : Pt) : Pt := (p.1 - c.1, p.2 - c.2)

/-- The ledger of a polygon against the ray issuing from a declared point. -/
def ledgerAbout (c : Pt) (vs : List Pt) : List Crossing := ledger (vs.map (shift c))

/-- The winding of a closed polygon about a declared point: the net of its ledger. -/
def windingAbout (c : Pt) (vs : List Pt) : ℤ := net (ledgerAbout c vs)

/-! ## 3. The net is a receiver face of the ledger -/

/-- **The net is a face of the ledger.**  It reads the hand column and deletes site and endpoints,
so any two populations agreeing on that one column agree on the net.  The converse is false and
`theTwoPopulationsShareOneNet` exhibits the failure. -/
theorem theNetIsAFaceOfTheLedger (L L' : List Crossing) (h : hands L = hands L') :
    net L = net L' := by
  unfold net
  rw [h]

/-- **And the face is strictly coarser.**  Two ledgers with the same hands and different sites have
the same net, exhibited: the passage moved on the boundary and the net did not notice. -/
theorem theNetIsBlindToWhereTheCrossingSits :
    net [⟨0, (1, -1), (1, 1), .withTurn⟩] = net [⟨7, (5, -3), (5, 2), .withTurn⟩] ∧
      ([⟨0, (1, -1), (1, 1), .withTurn⟩] : List Crossing) ≠ [⟨7, (5, -3), (5, 2), .withTurn⟩] := by
  refine ⟨rfl, ?_⟩
  decide

/-! ## 4. Five polygons, and their complete ledgers

Each ledger below is *computed* from the vertex list by the incidence condition; the right-hand side
is what the kernel returns, exhibited entry by entry so a reader can see the addresses.  Every one
of these five was re-verified independently in exact integer arithmetic before it was written. -/

/-- A square around the origin, counterclockwise from the lower right. -/
def enclosingLoop : List Pt := [(1, -1), (1, 1), (-1, 1), (-1, -1)]

/-- A square to the right of the origin straddling the axis: it meets the ray twice and encloses
nothing. -/
def straddlingLoop : List Pt := [(2, 1), (2, -1), (3, -1), (3, 1)]

/-- A square entirely above the axis: it never approaches the ray. -/
def separatedLoop : List Pt := [(1, 1), (3, 1), (3, 2), (1, 2)]

/-- A loop around the origin with a notch, crossing the ray three times: `+ − +`. -/
def notchedLoop : List Pt :=
  [(1, -1), (1, 1), (2, 1), (2, -1), (3, -1), (3, 2), (-1, 2), (-1, -1)]

/-- A doubled loop: twice around the origin, at two different radii, so the two upward passages sit
at two distinct abscissae rather than one retraced site. -/
def doubledLoop : List Pt :=
  [(1, -1), (1, 1), (-1, 1), (-1, -1), (2, -2), (2, 2), (-2, 2), (-2, -2)]

/-- **The enclosing square's ledger is one upward passage, at boundary segment `0`.**  `rfl`. -/
theorem theEnclosingLoopLedgerIsOneUpwardCrossing :
    ledger enclosingLoop = [⟨0, (1, -1), (1, 1), .withTurn⟩] := rfl

/-- **The straddling square's ledger is two opposed passages, at segments `0` and `2`.**  `rfl`. -/
theorem theStraddlingLoopLedgerIsTwoOpposedCrossings :
    ledger straddlingLoop =
      [⟨0, (2, 1), (2, -1), .againstTurn⟩, ⟨2, (3, -1), (3, 1), .withTurn⟩] := rfl

/-- **The separated square's ledger is empty.**  `rfl`. -/
theorem theSeparatedLoopLedgerIsEmpty : ledger separatedLoop = [] := rfl

/-- **The notched loop's ledger is three passages, `+ − +`, at segments `0`, `2` and `4`.**
`rfl`. -/
theorem theNotchedLoopLedgerIsThreeCrossings :
    ledger notchedLoop =
      [⟨0, (1, -1), (1, 1), .withTurn⟩, ⟨2, (2, 1), (2, -1), .againstTurn⟩,
        ⟨4, (3, -1), (3, 2), .withTurn⟩] := rfl

/-- **The doubled loop's ledger is two upward passages at two distinct sites.**  `rfl`. -/
theorem theDoubledLoopLedgerIsTwoUpwardCrossings :
    ledger doubledLoop =
      [⟨0, (1, -1), (1, 1), .withTurn⟩, ⟨4, (2, -2), (2, 2), .withTurn⟩] := rfl

/-! ## 5. The falsifier, made a theorem

*Two different crossing populations producing the same net* — the standing falsifier recorded
against `polygon_winding`.  It is exhibited twice: once at net `+1` with populations of size `1` and
`3`, and once at net `0` with populations of size `0` and `2`. -/

/-- **TWO POPULATIONS, ONE NET.**  The square around the origin crosses the ray once; the notched
loop crosses it three times, `+ − +`.  Their ledgers differ in length, in hand column and entry by
entry — and their nets are both `+1`.  Kernel computation throughout. -/
theorem theTwoPopulationsShareOneNet :
    net (ledger enclosingLoop) = 1 ∧
      net (ledger notchedLoop) = 1 ∧
      total (ledger enclosingLoop) = 1 ∧
      total (ledger notchedLoop) = 3 ∧
      hands (ledger enclosingLoop) ≠ hands (ledger notchedLoop) ∧
      ledger enclosingLoop ≠ ledger notchedLoop := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide

/-- **The cancelling pair: the same net `0`, and one of them met the ray twice.**  This is the case
a net cannot report — `winding = 0` is doing two jobs, *never approached the ray* and *crossed it and
came back*, and only the ledger separates them. -/
theorem theCancellingLoopAndTheSeparatedLoopShareOneNet :
    net (ledger straddlingLoop) = 0 ∧
      net (ledger separatedLoop) = 0 ∧
      total (ledger straddlingLoop) = 2 ∧
      total (ledger separatedLoop) = 0 ∧
      ledger straddlingLoop ≠ ledger separatedLoop := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- **The control: the net does separate other pairs.**  Without this the blindness above would be a
receipt that could not have come out otherwise — a family that separates nothing carries no
evidence when it fails to separate. -/
theorem theNetSeparatesTheEnclosingLoopFromTheStraddlingOne :
    net (ledger enclosingLoop) ≠ net (ledger straddlingLoop) := by decide

/-- **A second control.**  Reversing a loop is visible to the net. -/
theorem theNetSeparatesALoopFromItsReversal :
    net (ledger enclosingLoop) ≠ net (ledger enclosingLoop.reverse) := by decide

/-! ## 6. Winding about a declared point, and reversal -/

/-- A square of side four with a corner at the origin, counterclockwise. -/
def squareLoop : List Pt := [(0, 0), (4, 0), (4, 4), (0, 4)]

/-- **The square winds once about an interior point, and the ledger says where.**  The single
passage is the segment from `(4,0)` to `(4,4)`, read in the frame of the declared point.  `rfl`. -/
theorem theSquareWindsOnceAboutItsInterior :
    ledgerAbout (2, 2) squareLoop = [⟨1, (2, -2), (2, 2), .withTurn⟩] ∧
      windingAbout (2, 2) squareLoop = 1 := ⟨rfl, rfl⟩

/-- **And not at all about an exterior point, with an empty ledger rather than a cancelling
one.**  `rfl`. -/
theorem theSquareWindsNotAtAllAboutAnExteriorPoint :
    ledgerAbout (10, 10) squareLoop = [] ∧ windingAbout (10, 10) squareLoop = 0 := ⟨rfl, rfl⟩

/-- **The doubled loop winds twice, and the two passages are at two distinct sites.**  The net `2`
is a sum over an exhibited population of two, not one passage counted twice.  `rfl`. -/
theorem theDoubledLoopWindsTwiceOverTwoDistinctSites :
    windingAbout (0, 0) doubledLoop = 2 ∧
      ledgerAbout (0, 0) doubledLoop =
        [⟨0, (1, -1), (1, 1), .withTurn⟩, ⟨4, (2, -2), (2, 2), .withTurn⟩] := ⟨rfl, rfl⟩

/-- **Reversal swaps the hand and negates the net while the population size stands.**  The same
passage, the other way: one crossing before and one after, hand `withTurn` before and
`againstTurn` after, net `+1` and `−1`.  This is the port of the Rust control
`the_two_hands_swap_under_reversal_while_the_crossing_population_does_not`.  `rfl`. -/
theorem theReversedLoopSwapsTheHandAndNegatesTheNet :
    ledger enclosingLoop.reverse = [⟨2, (1, 1), (1, -1), .againstTurn⟩] ∧
      net (ledger enclosingLoop.reverse) = -1 ∧
      total (ledger enclosingLoop.reverse) = total (ledger enclosingLoop) := ⟨rfl, rfl, rfl⟩

/-! ## 7. The declared ray is an aperture

The Rust does not move the ray; it rotates the polygon by `p ↦ (p₁ + k p₂, p₂ − k p₁)` — that is,
multiplies by `1 − k i` — searching `k = 0 … 32` for a parameter putting no vertex on the axis, and
refuses if none exists.  The parameter is an apparatus aperture.  It cannot reverse a hand, and it
can move the whole population. -/

/-- The aperture rotation: multiplication by `1 − k i`. -/
def rotate (k : ℤ) (p : Pt) : Pt := (p.1 + k * p.2, p.2 - k * p.1)

/-- Transversality: no vertex sits on the axis the ray lies in. -/
def admissible (vs : List Pt) : Bool := vs.all fun p => decide (p.2 ≠ 0)

/-- Transversality at a declared aperture parameter. -/
def admissibleAt (k : ℕ) (vs : List Pt) : Bool := admissible (vs.map (rotate (k : ℤ)))

/-- The first admissible aperture parameter, searched over `0 … 32` exactly as the Rust does.
`none` is the refusal, not a fallback. -/
def rayParameter (vs : List Pt) : Option ℕ := (List.range 33).find? fun k => admissibleAt k vs

/-- **The aperture scales every pairing by `1 + k²`.**  Exact identity over `ℤ`, by `ring`. -/
theorem theApertureRotationScalesTheCrossByAPositiveFactor (k : ℤ) (a b : Pt) :
    cross (rotate k a) (rotate k b) = (1 + k ^ 2) * cross a b := by
  simp only [cross, rotate]
  ring

/-- **So the aperture can never reverse a hand.**  The factor is strictly positive for every
parameter, so the sign of every pairing survives the rotation. -/
theorem theApertureRotationNeverReversesAHand (k : ℤ) (a b : Pt) :
    0 < cross (rotate k a) (rotate k b) ↔ 0 < cross a b := by
  rw [theApertureRotationScalesTheCrossByAPositiveFactor, mul_pos_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · nlinarith [sq_nonneg k]
  · intro h
    exact Or.inl ⟨by positivity, h⟩

/-- A diamond around the origin: two of its vertices sit on the axis, so the ray is not transversal
at parameter `0`. -/
def diamondLoop : List Pt := [(1, 0), (0, 1), (-1, 0), (0, -1)]

/-- **The diamond refuses the first aperture and takes the second, and the rotation carries it onto
the square.**  Parameter `0` is inadmissible, the search returns `1`, and the rotated diamond is
exactly `enclosingLoop` — so its ledger is that one upward passage and its net is `1`.  Kernel
computation. -/
theorem theDiamondNeedsTheSecondApertureAndBecomesTheSquare :
    admissibleAt 0 diamondLoop = false ∧
      rayParameter diamondLoop = some 1 ∧
      diamondLoop.map (rotate 1) = enclosingLoop ∧
      ledger (diamondLoop.map (rotate 1)) = [⟨0, (1, -1), (1, 1), .withTurn⟩] ∧
      net (ledger (diamondLoop.map (rotate 1))) = 1 := by
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  decide

/-- **The aperture moves the population and not the net.**  One polygon, two admissible parameters:
at `0` it meets the ray twice, at `1` it meets it not at all, and the net is `0` in both frames.  A
crossing count reported without its aperture is a receiver face presented as the object; the net is
the part that crossed the frame boundary. -/
theorem theApertureMovesThePopulationAndNotTheNet :
    admissibleAt 0 straddlingLoop = true ∧
      admissibleAt 1 straddlingLoop = true ∧
      total (ledger (straddlingLoop.map (rotate 0))) = 2 ∧
      total (ledger (straddlingLoop.map (rotate 1))) = 0 ∧
      net (ledger (straddlingLoop.map (rotate 0))) = 0 ∧
      net (ledger (straddlingLoop.map (rotate 1))) = 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 8. The jump law — named open, with two proved instances

Crossing the boundary changes the winding by the hand of the edge crossed.  Stated here for the
general polygon over the exact carrier, and **not proved**. -/

/-- Difference of two points. -/
def sub (a b : Pt) : Pt := (a.1 - b.1, a.2 - b.2)

/-- Which side of the directed line `x → y` the point `z` falls on; zero exactly on the line. -/
def side (x y z : Pt) : ℤ := cross (sub y x) (sub z x)

/-- The two segments cross properly: each separates the other's endpoints strictly. -/
def properlyCrosses (p q a b : Pt) : Bool :=
  decide (side p q a * side p q b < 0) && decide (side a b p * side a b q < 0)

/-- Every boundary segment the move `a → b` properly crosses, by site. -/
def meetingSites (vs : List Pt) (a b : Pt) : List ℕ :=
  (closedSegments vs).filterMap fun t => if properlyCrosses t.2.1 t.2.2 a b then some t.1 else none

/-- The hand of a meeting between the directed edge `p → q` and the directed move `a → b`. -/
def meetingHand (p q a b : Pt) : Hand :=
  if 0 < cross (sub q p) (sub b a) then .withTurn else .againstTurn

/-- The move clears every vertex: no vertex of the polygon lies on the line of the move, so no
boundary passage can hide in a degeneracy. -/
def clearOfEveryVertex (vs : List Pt) (a b : Pt) : Bool :=
  vs.all fun p => decide (side a b p ≠ 0)

/-- The boundary edge at a declared site. -/
def edgeAt (vs : List Pt) (i : ℕ) : Option (Pt × Pt) :=
  ((closedSegments vs).find? fun t => decide (t.1 = i)).map fun t => t.2

/-- **NAMED OPEN — the jump law across one edge.**

If a straight move from `a` to `b` leaves both endpoints transversal to the ray, clears every vertex
of the polygon, and properly crosses **exactly one** boundary edge, then the winding about the
moving point changes by exactly the hand of that meeting.

This is not proved here for general polygons and general moves.  It is not vacuous: the hypotheses
are satisfiable and the conclusion is not constant, both discharged by the two instances below,
which realize the two hands and the two jumps `+1` and `−1`. -/
def TheJumpLawAcrossOneEdge : Prop :=
  ∀ (vs : List Pt) (a b p q : Pt) (i : ℕ),
    admissible (vs.map (shift a)) = true →
    admissible (vs.map (shift b)) = true →
    clearOfEveryVertex vs a b = true →
    meetingSites vs a b = [i] →
    edgeAt vs i = some (p, q) →
    windingAbout b vs - windingAbout a vs = handSign (meetingHand p q a b)

/-- **The jump law holds where the move enters the square.**  Every hypothesis of
`TheJumpLawAcrossOneEdge` is verified for this move, and the conclusion holds: the move `(2,−2) →
(2,2)` crosses only the bottom edge, its hand is `withTurn`, and the winding goes `0 → 1`.  Kernel
computation. -/
theorem theJumpLawHoldsWhereTheMoveEntersTheSquare :
    admissible (squareLoop.map (shift (2, -2))) = true ∧
      admissible (squareLoop.map (shift (2, 2))) = true ∧
      clearOfEveryVertex squareLoop (2, -2) (2, 2) = true ∧
      meetingSites squareLoop (2, -2) (2, 2) = [0] ∧
      edgeAt squareLoop 0 = some ((0, 0), (4, 0)) ∧
      meetingHand (0, 0) (4, 0) (2, -2) (2, 2) = .withTurn ∧
      windingAbout (2, 2) squareLoop - windingAbout (2, -2) squareLoop =
        handSign (meetingHand (0, 0) (4, 0) (2, -2) (2, 2)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **And where the move leaves it, with the other hand.**  The move `(2,2) → (2,6)` crosses only
the top edge, its hand is `againstTurn`, and the winding goes `1 → 0`.  Together with the previous
theorem this shows the right-hand side of the jump law genuinely varies — the statement is not a
constant in disguise.  Kernel computation. -/
theorem theJumpLawHoldsWhereTheMoveLeavesTheSquare :
    admissible (squareLoop.map (shift (2, 2))) = true ∧
      admissible (squareLoop.map (shift (2, 6))) = true ∧
      clearOfEveryVertex squareLoop (2, 2) (2, 6) = true ∧
      meetingSites squareLoop (2, 2) (2, 6) = [2] ∧
      edgeAt squareLoop 2 = some ((4, 4), (0, 4)) ∧
      meetingHand (4, 4) (0, 4) (2, 2) (2, 6) = .againstTurn ∧
      windingAbout (2, 6) squareLoop - windingAbout (2, 2) squareLoop =
        handSign (meetingHand (4, 4) (0, 4) (2, 2) (2, 6)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The two instances carry different hands.**  The control on the pair above: if both meetings had
the same hand, the two instances would be one instance and the jump law would be untested in its
sign. -/
theorem theTwoJumpInstancesCarryDifferentHands :
    meetingHand (0, 0) (4, 0) (2, -2) (2, 2) ≠ meetingHand (4, 4) (0, 4) (2, 2) (2, 6) := by
  decide

end Soma.Holonics.Millennium.WindingLedger
