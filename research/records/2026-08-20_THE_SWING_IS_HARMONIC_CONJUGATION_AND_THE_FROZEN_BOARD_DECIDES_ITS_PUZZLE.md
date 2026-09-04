# The swing is harmonic conjugation, and the frozen board decides its puzzle

**Date:** 2026-08-20
**Kind:** formal definition and derivation deposit. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1. **No engine source is touched**; the only tree written under `soma/` is
`soma/formal/`.
**Truth status:** `proved-derived` for every Lean theorem, each kernel-checked and audited free of
`sorryAx`; `proved-standard` for the classical physics cited; `interpretation` for the readings;
`open` for what §6 names.
**Companion:** [`research/equation-atlas/`](../equation-atlas) — twelve equations and ten
relations appended, each citing its Lean owner or its source.
**Predecessor:**
[`2026-08-20_THE_PROOF_LINES_ARE_ONE_GLUING_SHAPE_AND_A_BARRIER_IS_A_BLIND_APERTURE.md`](2026-08-20_THE_PROOF_LINES_ARE_ONE_GLUING_SHAPE_AND_A_BARRIER_IS_A_BLIND_APERTURE.md),
whose second named gap this record closes.

## Provenance

**Brandon's, directly (2026-08-20).** That the cross-ratio swing — the one move — should be
rigorously defined, as an operation describing transformations between pins or constraints. That
the move has **four participants**: a body in motion (gyrating, precessing), a legitimate anchor
being pivoted off, one *contemporary* constraint (the pin that is neither the pivot nor the
board), and **the board, which is invariant for all motions in this system**. That crossing a
definite edge is *"a partial movement for a complete cross product"*, that crossing edges over
each other in multiple steps is *"a complete non-commutative cross product at the scope of the set
of steps"*, and that otherwise it is *"a basis translation."* That **the board does not have to be
a frozen constraint** and the swing chains into higher-order mechanisms in tensor calculus — Eros
is not three pins on one frozen board but an emergent number of charts as boards with their own
pins, causally connected across charts. That mass is a macroscopic token of how much curvature
occurs during information transport, and that charge and spin are tokens of relativistic
orientation available to particles in a moment. That the Millennium gaps should be closed and
attacked rather than left, aggressively.

**Assistant, this record.** The identification of the swing with harmonic conjugation and the
proof that it is negation in the constraint chart; the parity and unimodular invariants; the
solution of the puzzle; the instantiation of the additive passage; and the readings in §5.

---

## 1. The swing is harmonic conjugation, and the four participants are forced

**`definition`, with `proved-derived` consequences.**

```text
(A, A' ; B, D) = −1
```

`A` is the body, `A'` its new state, `B` the anchor, `D` the board. **Four points, because a
cross ratio needs four** — three do not determine the move. That is not a convention; it is the
reason Brandon's description has exactly the participants it has.

Solving the harmonic condition gives the closed form, which `Swing.lean` takes as the definition:

```text
A' = ((A − B)·D + (A − D)·B) / (2A − B − D)
```

**And the whole content of the move is one theorem.** Let `t(x) = (x − B)/(x − D)` — the chart the
two *constraints* declare, sending the anchor to zero and the board to infinity. Then

```lean
theorem theSwingIsNegationInTheConstraintChart :
    constraintChart b d (harmonicConjugate b d a) = - constraintChart b d a
```

> **The swing is the half turn, conjugated into whatever chart the constraints declare.** Nothing
> about it is chart-dependent except the conjugation. `−1 = e^{iπ}` is not a decoration on the
> move; it *is* the move, once the constraints have fixed a chart to be a half turn in.

Two companions are proved: **the fixed points of the swing are exactly the anchor and the board**,
never the body. A move whose body is fixed is not a move, and the fixed locus is the pair of
constraints — the same shape as the placement law in `Seam.lean`.

## 2. Freezing the board is the affine restriction

**`proved-derived`.** An affine geometry is a projective one with a distinguished invariant line.
**Brandon's "the board is invariant for all motions in this system" is exactly that**: the board
is the line at infinity, and the transformations are affine rather than projective precisely
because it is frozen. His remark that *"the board doesn't have to be a frozen constraint"* is the
observation that unfreezing it returns the full projective group — which is the general case §1
already carries.

In the frozen chart the swing degenerates:

```text
A' = 2B − A,        A' − B = −(A − B)
```

and three laws follow, all discharged:

| law | statement |
|---|---|
| involution | two swings about one anchor return the body |
| **the composition is a doubled translation** | `S_B ∘ S_C (A) = A + 2(B − C)` |
| non-commutation | swinging about `B` then `C` differs from the reverse by twice the anchor displacement |

> **Brandon's sentence is exactly right and both halves are theorems.** *One* crossing turns —
> it negates the hand. *A pair* of crossings is "a basis translation" — literally a translation,
> and by a **doubled** vector. The factor of two is forced by the composition, not chosen, and it
> is why the reachable population sits in the doubled lattice.

## 3. Two invariants: one that never moves, one that alternates

**`proved-derived`.**

**The parity class.** `2B − A ≡ A (mod 2Λ)` for *every* anchor `B`. So each body's class in
`Λ/2Λ` is invariant, per body, independent of which anchor was used and of what any other body
does. That independence is what makes it survive an arbitrary history.

**The oriented span.** `det(A' − B, C − B) = − det(A − B, C − B)`. **The magnitude stands and the
hand flips.**

> A receiver reading only the magnitude sees an invariant. A receiver reading the orientation sees
> an alternation of period two. **The number of swings modulo two is a real coordinate of the
> motion, recoverable from the configuration and destroyed by any unsigned reading.**

That is the split-and-hand doctrine on the swing itself, and it is Brandon's cross-product remark
made exact: the scalar cross product in the plane *is* this determinant, one crossing negates it,
and **an even number of crossings completes it** — *"a complete non-commutative cross product at
the scope of the set of steps it took."*

**And the magnitude invariant is unimodular.** A configuration on a primitive cell stays on one.
That is the same conserved `det = ±1` with an alternating sign that the mediant descent carries
between consecutive convergents — recorded in the atlas as a structural correspondence and **not**
as an identity: the two theorems are not shown here to be one theorem.

## 4. The puzzle, decided

**`proved-derived`. The answer is no, and the obstruction is named.**

Three bodies sit at three corners of a primitive cell; the target is the fourth corner. Their
parity classes are three of the four elements of `Λ/2Λ`; the fourth corner is the fourth element;
**no move changes any body's class.**

```lean
theorem theFourthCornerIsUnreachable {d : Config} (h : Reachable initial d) (k : Fin 3) :
    d k ≠ fourthCorner
```

`Reachable` is the reflexive-transitive closure of *any body swinging about any body*, so the
theorem quantifies over every finite history. **The impossibility is a returned invariant, not an
exhausted search** — which is the distinction this project keeps insisting on, arriving here on a
puzzle small enough to check by hand.

Stronger than the puzzle asks: no body ever reaches **any** site whose displacement from its own
start has both coordinates odd.

## 5. The frozen board is the first honest instance of the additive passage

**`proved-derived`, and it closes the second gap named in the predecessor record.**

`Gluing.lean` stated the additive passage and its obstruction group abstractly, and nothing
instantiated it. The board does:

```text
Candidate         = the lattice
LocallyAdmissible = everything — every hole is there and nothing local forbids any of them
Realized          = the kernel of reduction modulo two
Obstruction group = the four-element quotient, nontrivial
```

`theBoardDoesNotGlue` exhibits the fourth corner as the witness, and
`theBoardsObstructionGroupIsNontrivial` derives the group's nontriviality from the general theorem.

> **An abstract predicate with no instance is an untested gauge**, and this project convicts that
> shape by name. The passage frame now has a real object with a real, finite, computed obstruction
> group, and the question the puzzle asks is answered by naming the class.

**The blindness frame was also non-vacuous-ified in the same pass.** `Lines.lean` now carries a
witnessed instance: the residue-modulo-two reading is **blind to the hand**, because two and four
are congruent and carry opposite hands. So `blindFamilyCarriesNoVerdict` has a witness and is not
an untested gauge either.

## 6. The physics, with the boundary that makes the analogy checkable

**`proved-standard` for the classical content; `interpretation` for the joins.**

**Mass compactifies the orientation group.** For a massive particle the little group — the residual
Lorentz symmetry once the momentum is fixed — is `SO(3)`, compact, giving `2s+1` states. For a
massless one it is `ISO(2)`, non-compact, leaving two helicities.

> **Mass is what makes the residual orientation group close.** That is Wigner's 1939
> classification, and it lands exactly on the earlier reading that a real turn closes while an
> imaginary one does not: `cosh η = cos(iη)`, a boost has no maximum, and a massless particle has
> no rest frame to have an `SO(3)` in. Charge is the label of a `U(1)` representation — a winding,
> quantized because the group is compact.

**The medium analogy for gravity has one sharp boundary and it is worth having.** Gravitational
redshift and deflection are **achromatic** — every wavelength scales by the same factor — and the
optical-metric formalism writes light bending as propagation through an effective index
`n = 1 + 2GM/rc²` that carries **no wavelength dependence**.

> **Achromaticity means the transport carries no spectral remainder: it is a rebase.** A real
> material medium *disperses*, which is a genuine remainder. So Brandon's reading survives exactly
> where the index is wavelength-independent and fails wherever dispersion is the phenomenon. That
> is a checkable boundary rather than a hedge, and it is the compression tablet's own distinction
> — rebase against compression — arriving in optics.

**What is not claimed.** No quantization of gravity is asserted, no derivation of mass from
curvature density, and nothing here about the cited preprint, which was not read. Those readings
remain Brandon's and are recorded as his.

## 7. What this does not do

The Lean development is **two-dimensional and affine** wherever it computes. Section 1 is
projective and holds over any field, but the invariants, the puzzle and the passage instance are
all on a rank-two lattice with a frozen board.

**Brandon's actual object is none of these.** He states it directly: *"it's not just 3 pins on one
frozen board, it's an emergent amount of charts as boards with their own sets of pins, but those
pins are not only vertices of triangles on their own charts but causal pins connected to pins on
other charts."* Nothing here formalizes a chart-to-chart pin, an unfrozen board in motion, or the
tensor-calculus chaining. **The one move is now rigorously defined and its simplest system is
decided; the ecology of boards is not touched.**

## 8. What is owed, with falsifiers

**`open`. None is scheduled.**

| owed | falsifier |
|---|---|
| **The unfrozen board.** Section 1 is projective and section 2 onward is affine; nothing carries an invariant through a board that itself moves. The first question is what replaces the parity class when the board is not the line at infinity. | An invariant claimed for a moving board that a projective change of the board destroys. |
| **The cross-chart pin.** A body whose anchor lies on another chart, with the transition between them declared. This is the object Brandon is actually describing and it has no definition here. | A cross-chart swing whose composition law disagrees with the doubled translation in each chart separately. |
| **The swing-to-convergent identity.** The atlas records the shared unimodular invariant as a correspondence. Whether a mediant descent *is* a sequence of swings, in a stated chart, is not settled. | A descent step that is not a swing, or a swing that moves the determinant. |
| **The predecessor's remaining gaps** — the placement-to-hand bridge, the archimedean condensation's remainder, and the parity obstruction as a derived instance — stand unchanged. | As recorded there. |

## 9. Boundaries

Every Lean theorem cited is kernel-checked; fifteen were audited by `#print axioms` in this pass
and none depends on `sorryAx`. The library builds at 3,283 jobs. The puzzle result is a statement
about a primitive cell and says nothing about configurations that do not begin on one. The
physics in §6 is classical and cited; the joins to this framework are `interpretation`. The
composed names are this record's, and the classical labels are carried as asides on every
declaration.
