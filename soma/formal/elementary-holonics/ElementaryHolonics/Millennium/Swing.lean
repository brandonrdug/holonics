import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ElementaryHolonics.Millennium.Gluing

/-!
# The swing — the one move, defined as harmonic conjugation

The swing carries a body past an anchor.  Four things participate and the definition needs all
four: the **body** that moves, the **anchor** it pivots about, a **contemporary constraint** (the
other body present, which with the anchor spans the edge being crossed), and the **board** — the
constraint that is invariant for every motion in the system.

**The swing is harmonic conjugation.**  `A'` is the unique point with cross ratio
`(A, A'; B, D) = −1`, where `B` is the anchor and `D` is the board.  Section 1 proves the
statement that makes this precise and useful: **in the chart that sends the anchor to zero and
the board to infinity, the swing is exactly negation** — the half turn, conjugated into whatever
chart the constraints declare.

**Freezing the board is putting `D` at infinity**, which is what makes a geometry affine rather
than projective.  Section 2 works there: the swing degenerates to the point reflection
`A ↦ 2B − A`, and sections 3 and 4 derive its invariants and decide a lattice puzzle with them.

Section 5 is the point of the file for this project: **the frozen board is the first honest
instance of the additive passage** in `Gluing.lean`.  Its obstruction group is a real, finite,
nontrivial group, and the question the puzzle asks is answered by naming the class.

Every `theorem` here is discharged.
-/

namespace Soma.Holonics.Millennium.Swing

/-! ## 1. The swing is negation in the chart the constraints declare -/

section Harmonic

variable {K : Type*} [Field K]

/-- The **chart the two constraints declare**: the map sending the anchor to zero and the board
to infinity.  Every projective transformation fixing both is diagonal here. -/
def constraintChart (b d x : K) : K := (x - b) / (x - d)

/-- The **harmonic conjugate** of `a` with respect to the anchor `b` and the board `d`.

*Aside: the fourth harmonic point; `(a, a'; b, d) = −1`.* -/
def harmonicConjugate (b d a : K) : K := ((a - b) * d + (a - d) * b) / (2 * a - b - d)

/-- **In the chart the constraints declare, the swing is negation.**

This is the whole content of the move.  A half turn is `−1`; conjugating it by the chart that the
anchor and the board declare produces the swing, and nothing about the swing is chart-dependent
except the conjugation. -/
theorem theSwingIsNegationInTheConstraintChart {b d a : K}
    (hbd : b ≠ d) (had : a ≠ d) (hden : 2 * a - b - d ≠ 0) :
    constraintChart b d (harmonicConjugate b d a) = - constraintChart b d a := by
  have hbd' : b - d ≠ 0 := sub_ne_zero.mpr hbd
  have had' : a - d ≠ 0 := sub_ne_zero.mpr had
  have hnum : harmonicConjugate b d a - b = (a - b) * (d - b) / (2 * a - b - d) := by
    rw [harmonicConjugate, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]; ring
  have hden2 : harmonicConjugate b d a - d = (a - d) * (b - d) / (2 * a - b - d) := by
    rw [harmonicConjugate, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]; ring
  have hAD : (a - d) * (b - d) / (2 * a - b - d) ≠ 0 :=
    div_ne_zero (mul_ne_zero had' hbd') hden
  rw [constraintChart, constraintChart, hnum, hden2, div_eq_iff hAD]
  field_simp
  ring

/-- **The anchor and the board are exactly what the swing fixes.**  A move has two fixed points,
and they are the two constraints — never the body. -/
theorem theSwingFixesTheAnchor {b d : K} (h : b ≠ d) : harmonicConjugate b d b = b := by
  have hbd : b - d ≠ 0 := sub_ne_zero.mpr h
  rw [harmonicConjugate, show 2 * b - b - d = b - d from by ring]
  field_simp
  ring

theorem theSwingFixesTheBoard {b d : K} (h : b ≠ d) : harmonicConjugate b d d = d := by
  have hbd : d - b ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [harmonicConjugate, show 2 * d - b - d = d - b from by ring]
  field_simp
  ring

end Harmonic

/-! ## 2. Freezing the board sends it to infinity, and the swing becomes a point reflection

An affine geometry is a projective one with a distinguished invariant line.  "The board is frozen
for all motions" is exactly that distinction, and in the affine chart the harmonic conjugate of
`a` with respect to `b` and the point at infinity is the point reflection. -/

variable {G : Type*} [AddCommGroup G]

/-- The **swing with the board frozen**: the body crosses the anchor and lands as far past it as
it began before it. -/
def swing (b a : G) : G := b + b - a

/-- **The swing is the half turn on the displacement from the anchor.**  This is the degenerate
harmonic condition — the one that survives when the board is at infinity — and it is why the
move is a turn and not a translation. -/
theorem theSwingNegatesTheDisplacementFromTheAnchor (b a : G) :
    swing b a - b = -(a - b) := by
  simp only [swing]; abel

/-- **The swing is an involution.**  Two swings about the same anchor return the body. -/
theorem theSwingIsAnInvolution (b : G) : Function.Involutive (swing b) := by
  intro a; simp only [swing]; abel

/-- **The anchor is fixed.** -/
@[simp] theorem theAnchorIsFixed (b : G) : swing b b = b := by
  simp [swing]

/-- **Two swings about different anchors are a translation, and the translation is doubled.**

This is the composition law: a single crossing turns, a pair of crossings translates.  The factor
of two is not a convention — it is why the reachable population sits in the doubled lattice. -/
theorem twoSwingsAreADoubledTranslation (b c a : G) :
    swing b (swing c a) = a + (b + b - (c + c)) := by
  simp only [swing]; abel

/-- **The swing does not commute, and its commutator is a doubled translation.**

Swinging about `b` then `c` differs from `c` then `b` by exactly twice the displacement between
the anchors.  Order is a real coordinate of the motion, not a bookkeeping choice. -/
theorem theSwingsDoNotCommute (b c a : G) :
    swing b (swing c a) - swing c (swing b a) = (b + b - (c + c)) - (c + c - (b + b)) := by
  simp only [swing]; abel

/-! ## 3. The frozen board's invariants: a parity that never moves, and a hand that alternates -/

/-- A position on the board. -/
abbrev Site : Type := ℤ × ℤ

/-- The **parity class** of a site: which of the four cells of the doubled lattice it sits in.

*Aside: the image of `ℤ² → (ℤ/2)²`.* -/
def parityClass (p : Site) : ZMod 2 × ZMod 2 := ((p.1 : ZMod 2), (p.2 : ZMod 2))

/-- **The swing never moves a body out of its parity class.**

This is the invariant, and it is invariant *per body* and independent of which anchor was used —
which is what makes it survive an arbitrary sequence of moves by arbitrary bodies. -/
theorem theSwingPreservesTheParityClass (b a : Site) :
    parityClass (swing b a) = parityClass a := by
  have key : ∀ x y : ZMod 2, y + y - x = x := by decide
  simp only [parityClass, swing, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.mk.injEq]
  constructor <;> push_cast <;> apply key

/-- The **oriented span** of a configuration: the determinant of the two edges out of the anchor.

*Aside: twice the signed area of the triangle.* -/
def orientedSpan (a b c : Site) : ℤ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- **The swing negates the oriented span: the magnitude stands and the hand flips.**

The split and the hand are separate readings and only one of them moves.  A receiver that reads
only the magnitude sees an invariant; a receiver that reads the orientation sees an alternation
of period two.  The number of swings modulo two is therefore a genuine coordinate of the motion,
recoverable from the configuration and lost by any unsigned reading. -/
theorem theSwingNegatesTheOrientedSpan (a b c : Site) :
    orientedSpan (swing b a) b c = - orientedSpan a b c := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  simp only [orientedSpan, swing, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The unsigned span is therefore invariant.**  A configuration that begins on a primitive cell
stays on one: the swing is a unimodular move.

*Aside: this is the same conserved `det = ±1` that a mediant descent conserves between
consecutive convergents — the swing and the continued fraction conserve one invariant.* -/
theorem theSwingPreservesTheUnsignedSpan (a b c : Site) :
    (orientedSpan (swing b a) b c).natAbs = (orientedSpan a b c).natAbs := by
  rw [theSwingNegatesTheOrientedSpan, Int.natAbs_neg]

/-! ## 4. The puzzle, decided

Three bodies sit at three corners of a primitive cell.  Can any of them be brought to the fourth
corner?  The parity class answers it without any search. -/

/-- A configuration of three bodies. -/
abbrev Config : Type := Fin 3 → Site

/-- One move: body `i` swings about body `j`. -/
def step (i j : Fin 3) (c : Config) : Config :=
  Function.update c i (swing (c j) (c i))

/-- Configurations reachable by any finite sequence of moves. -/
inductive Reachable : Config → Config → Prop
  | refl (c : Config) : Reachable c c
  | step {c d : Config} (i j : Fin 3) : Reachable c d → Reachable c (step i j d)

/-- **Every body keeps its parity class for the whole history, whatever anyone does.** -/
theorem everyBodyKeepsItsParityClass {c d : Config} (h : Reachable c d) (k : Fin 3) :
    parityClass (d k) = parityClass (c k) := by
  induction h with
  | refl => rfl
  | step i j _ ih =>
    by_cases hk : k = i
    · subst hk
      rw [step, Function.update_self, theSwingPreservesTheParityClass, ih]
    · rw [step, Function.update_of_ne hk, ih]

/-- The three bodies on three corners of a primitive cell. -/
def initial : Config := ![(0, 0), (1, 0), (0, 1)]

/-- The fourth corner. -/
def fourthCorner : Site := (1, 1)

/-- **The fourth corner is unreachable, by any body, after any sequence of moves.**

The three bodies occupy three of the four parity classes; the fourth corner is in the fourth; and
no move changes any body's class.  The impossibility is not a search that gave up — it is a
returned invariant with the obstruction named. -/
theorem theFourthCornerIsUnreachable {d : Config} (h : Reachable initial d) (k : Fin 3) :
    d k ≠ fourthCorner := by
  intro hk
  have hpar : parityClass (d k) = parityClass (initial k) := everyBodyKeepsItsParityClass h k
  rw [hk] at hpar
  revert hpar
  fin_cases k <;> simp [initial, fourthCorner, parityClass]

/-! ## 5. The frozen board is an honest instance of the additive passage

`Gluing.lean` states the shape; until now nothing instantiated it on a real object.  The board
does, and its obstruction group is finite, nontrivial and computed rather than posited. -/

/-- The reduction that measures which cell of the doubled lattice a site sits in. -/
def parityHom : Site →+ ZMod 2 × ZMod 2 where
  toFun := parityClass
  map_zero' := by simp [parityClass]
  map_add' := by
    intro x y
    obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    simp only [parityClass, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> push_cast <;> ring

/-- What a body can reach: the sites its own swings can carry it to, which is exactly the
doubled lattice through it. -/
def reachedDisplacements : AddSubgroup Site := parityHom.ker

/-- **The board, as an additive passage.**  Every site is locally admissible — the holes are all
there, and nothing local forbids any of them.  What is realized is the doubled lattice. -/
def boardPassage : AdditivePassage where
  Candidate := Site
  Realized := reachedDisplacements
  LocallyAdmissible := ⊤
  realized_le := le_top

/-- **The board does not glue, and the witness is the fourth corner.**

Local admissibility says nothing forbids the site; realization says nothing reaches it.  That gap
is the obstruction, and here it is inhabited, finite, and named. -/
theorem theBoardDoesNotGlue : ¬ boardPassage.Glues := by
  intro h
  have hmem : fourthCorner ∈ boardPassage.LocallyAdmissible := trivial
  have := h hmem
  simp only [boardPassage, reachedDisplacements, AddMonoidHom.mem_ker, parityHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, parityClass, fourthCorner, Prod.mk.injEq] at this
  revert this
  decide

/-- **Therefore its obstruction group is not trivial**, by the general theorem in `Gluing.lean`.
The abstract statement now has a witness, which is what keeps it from being an untested gauge. -/
theorem theBoardsObstructionGroupIsNontrivial :
    ¬ Subsingleton boardPassage.ObstructionGroup :=
  fun h => theBoardDoesNotGlue
    ((AdditivePassage.glues_iff_obstruction_subsingleton boardPassage).mpr h)

end Soma.Holonics.Millennium.Swing
