# The atlas is built: the method is recognised before it runs, and the coboundary keeps the residue

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `implemented-exact` and `measured` for everything returned; `proved-standard` for
the classical theorems composed. Two of the assistant's own expectations were **refuted by the
tests it wrote**, and both refutations are content rather than defects.
**Occasion:** the method-atlas deposit named three ranked builds. The first two are built, driven,
and measured. Brandon's stated ideal governs the shape, verbatim and contiguous:

> *the ideal here is that we're not only going to be able to utilize the output of the experiment as
> an atlas of mathematically correct transport functions, but we will be able to use this as a
> baseline measurement of truth for the machine's ability to recognize and employ transport
> mechanisms in local manifold regions appropriately.*

---

## 0. What was built

| owner | what it decides | driver |
|---|---|---|
| `crates/holonic-engine/src/elementary_chart.rs` | whether `∫R e^g` closes in the elementary chart, as the **consistency of one exact rational linear system** | `examples/the_integral_is_decided_by_rank_and_recognised_before_it_runs.rs` |
| `crates/holonic-engine/src/hermite_reduction.rs` | the **coboundary move**, with the residues returned as a Rothstein–Trager resultant and compared across a declared gauge | `examples/the_representative_moves_and_the_residue_does_not.rs` |

Two primitives the inventory found missing were added to
`crates/holonic-engine/src/rational_polynomial.rs`: `squarefree_decomposition` (Musser, with
multiplicities — `squarefree_part` returns only the radical and forgets the depth that every pole
descent needs) and `extended_monic_gcd`.

`cargo test --workspace` before the Hermite work: **2,239 passed, 0 failed** over 42 result lines.

---

## 1. The repair the builds forced, and it closes a standing defect

`crates/holonic-engine/src/inverse_transport.rs:128` `ExactAffineVersionFiber` already carried
incremental RREF over `Rat` **with the right-hand side**, and already refused an inconsistent system
by name with `AffineFiberObstructed`. But **the refusal named no material.** The row combination
producing the contradiction was computed at `:279` — it is the sequence of elimination factors — and
then discarded, so the fiber could prove an obstruction existed and never say what it was.

Repaired additively, breaking nothing: each `ExactAffineFiberRow` now carries a sparse
`lineage: BTreeMap<usize, Rat>` recording which admitted equations, in what exact combination,
produced it. When a row reduces to all-zero coefficients against a non-zero response, **the lineage
IS the left null combination**, and it is retained as `AffineObstruction`.

`AffineFiberObstructed` itself is unchanged — it is compared by equality at two sites and
constructed at a third — so the witness arrives through a new `obstruction()` accessor rather than
through a payload.

**Measured that the witness is a genuine combination and not always one row.** On
`∫(1 + x + x²)e^{x²}` neither equation is inconsistent alone: the constant monomial fixes `c₁ = 1`
and the quadratic fixes `2c₁ = 1`. The returned witness is

```text
(-2)·eq[x^0] + (1)·eq[x^2]     annihilates every unknown, returns -1
```

which is exactly the hand derivation. A witness that could not span two rows would have nothing to
report on this material.

---

## 2. Non-elementarity is a rank deficiency with an exhibited row

Liouville's criterion for `∫R e^g` is that a rational `a` exists with `a' + a·g' = R`. Two structures
decide it and they **refuse for different reasons** — which is the part a textbook table hides.

**The pole structure decides first, and decides before any arithmetic.** If `a` has a pole of order
`m ≥ 1`, then `a'` has order `m+1` there while `a g'` has order `m`; `g` is a polynomial so `g'`
contributes no pole, the orders cannot cancel, and `a' + a g'` has a pole of order exactly `m+1 ≥ 2`.
**So a simple pole in `R` requires a pole of `a` of order zero, which produces no pole at all.** A
simple pole is an absolute obstruction carrying no linear system. That is why `∫e^x/x` is `Ei(x)`,
and the driver returns it with `0` equations and `0` unknowns.

**Then the degree bound, and it is a single value rather than a search space:**

```text
deg a = deg R − deg g + 1
```

**This is the a priori bound that makes the candidate population finite and exhaustible** — the
property the method-atlas deposit named as the sound instance of a localized search, as against a
table of integrals, which is not one.

Measured over 16 declared integrands: **8 elementary with the realizer returned and all 8
differentiating back exactly**, 5 refused with an exhibited witness, 2 refused structurally on a
simple pole, 1 outside the declared aperture. Every realizer is classically correct —
`∫x e^x = (x−1)e^x`, `∫x²e^x = (x²−2x+2)e^x`, `∫x e^{x²} = ½e^{x²}`, `∫(2x²+1)e^{x²} = x e^{x²}`,
`∫(x²−x)e^x/x = (x−2)e^x`.

**The control that isolates the transport.** `∫1·e^x` and `∫1·e^{x²}` have the **identical**
coefficient `R = 1`. The first admits with realizer `1`; the second is refused. Nothing about the
numerator separates them — only `g'`, and `g'` is the transport. A reading about the integrand's
size or shape rather than about its transport could not produce that split.

---

## 3. The recognition instrument, and the asymmetry is the finding

Brandon's ask was for a baseline measuring the machine's ability to *recognise* which transport
applies. So the signature is committed **before** the system is built, and graded against what
returned. A recognition that reported the solver's answer would be a check whose material cannot
vary the property under test.

Measured over the declared 16:

```text
recognition settled it alone             5
recognition opened it, system found      8
recognition opened it, system refused    2
recognition contradicted                 0
```

**The asymmetry is the content, and it is a theorem rather than a limitation.** The two structural
refusals — a simple pole, and a negative realizer degree — are read off the object and **no linear
system can overturn them**. A satisfied degree bound is **necessary and not sufficient**: it says
where the only candidate lives, never that the candidate exists.

`∫(1+x)e^{x²}` is the separating case. Its degree bound is satisfied, so the signature cannot refuse
it, and the system refuses it anyway. Without such material in the family the recognition would look
decisive everywhere, and *"decisive everywhere"* would mean the signature and the solver are one
frame rather than two — the vacuous-gauge defect wearing a passing result.

---

## 4. The coboundary move, and a gauge whose orbit is measured

Hermite reduction writes `f = h' + g` with `h` rational. Because a rational function's derivative has
**zero residue at every pole**, `Res_α(f) = Res_α(g)` for every `α`: **the representative moves and
the residues do not.** That is why the move is lawful at all — the integral depends only on the class
— and it is the exact distinction between a coboundary move and a chart transition.

The class is returned with **no root extracted**, as the Rothstein–Trager resultant
`R(z) = Res_x(B − z·D*', D*)`, a `ℚ`-polynomial whose roots are the residues, compared by exact
equality and never by magnitude.

**Two reduction schedules are declared as a gauge, and the orbit is measured before agreement is read
as evidence.** On `f = (3x² + 2x + 1)/((x−1)²(x+1)³)` the schedules visit genuinely different
intermediate states and **do not even take the same number of steps** — two against three.

The mechanism is worth keeping, because a test asserting equal step counts failed and found it:
**descending `(x+1)³` to `(x+1)²` brings it level with `(x−1)²`, so the squarefree decomposition then
returns their PRODUCT at multiplicity two and one step descends both.** Descending `(x−1)²` first
never creates that coincidence. A gauge whose members take different step counts on the same material
is a stronger orbit than one that merely reorders.

Both return the identical `h`, the identical `g = −¼/(x²−1)`, and the identical
`Res(z) = z² − 1/64`. Residues `±1/8`, confirmed by hand: `−¼/2` at `x = 1` and `−¼/(−2)` at
`x = −1`.

**And the step bound is read off the material rather than authored.** With
`N = Σᵢ (i−1)·deg Vᵢ` — the total excess pole order counted at every root — one step on `V` drops
every root of `V` by one order, so `N` falls by `deg V ≥ 1` per step and the reduction terminates in
at most `N`. Here `N = 3`, and the schedules take 2 and 3. The first version of this module pinned
`STATE_APERTURE = 4096` instead; the authored-levels gate caught it, and **the level was derivable
from the material all along**, which is the disposition the contaminant protocol demands rather than
a label.

**And the control that keeps the invariant honest:** `2/(x−1)` returns `Res(z) = z − 2` against
`1/(x−1)`'s `z − 1`. A change that is not a coboundary **does** move the class. An invariant nothing
can move is not measuring anything.

---

## 5. Three expectations the tests refuted, kept because they are the content

**A coboundary can create a pole; it can never create a residue.** The test asserting that adding
`d/dx(1/x²)` to `1/(x−1)` leaves the residue polynomial unchanged **failed**, taking `z − 1` to
`z² − z`. The code was right. The coboundary introduces a pole at `x = 0` that the original integrand
did not have — at residue **zero**, because that is all a derivative can contribute. So the residue
polynomial gains a factor of `z` and **every other root stays exactly where it was**.

The sharper law, now stated and built as `nonzero_residue_polynomial()`:

> `residue_polynomial` is invariant when the pole set is fixed. The residue polynomial **with every
> factor of `z` divided out** is invariant unconditionally.

Both are now tested, with the pole-creating case required to move the first and required not to move
the second.

**The step count is schedule-dependent, and `Σ(mᵢ−1)` is an upper bound rather than a count.**
Stated in section 4: a test asserting the schedules take equal steps failed at 2 against 3, and the
merge it exposed is a real fact about Hermite reduction.

**The Sylvester route has an aperture, and calling it past that aperture is the convicted defect.**
`rothstein_trager` on a single-pole function leaves `B − z·D*'` constant in `x`, and
`resultant_in_eliminated_variable` declares degree ≥ 1 in the eliminated variable. Three tests failed
there. The repair is not to widen the carrier: `Res_x(c, g) = c^{deg g}` is elementary, so the
degenerate case is computed directly and the carrier is used only inside the aperture it declares.

---

## 6. What this does not claim

Not integration, and not Risch. `elementary_chart`'s aperture is `R = P/Q` with `Q` **squarefree**
and `g` a non-constant polynomial; a repeated denominator factor admits poles in the realizer and is
**refused by name** rather than answered. `hermite_reduction` works over `ℚ(x)` with no algebraic or
logarithmic extension, no field tower, and no logarithm emitted — the log part is returned as its
resultant. **Measured and still true: this tree has no derivation on any field, and the only
derivation-like operator in it remains the formal polynomial derivative.**

No Millennium movement, and no deed here may be graded by one. The third ranked build —
hypergeometric finiteness by Beukers–Heckman interlacing against Schwarz's fifteen rows — is not
begun. This record schedules nothing.

---

## 7. The third build, added the same day: closure decided by sorting integers

`crates/holonic-engine/src/hypergeometric_closure.rs`, driven by
`examples/the_solution_closes_when_the_marks_take_turns.rs`.

**The object in composable terms**, which is the form Brandon ratified this day and which this
section is written in: a second-order transport law well behaved everywhere except at **three
sites** — `0`, `1`, infinity. At each site a solution carried once round a small loop comes back
**turned**; those three amounts are the **local turn numbers**. Composing loops generates the
**return group**. *If the return group is finite the solution takes finitely many values and closes;
if infinite it never closes.* (Classical labels, carried alongside so they remain lookupable: the
*hypergeometric equation*, its *exponent differences*, its *monodromy group*.)

**What decides it.** Put the dials on a circle. Two families of marks: the **numerator** marks for
`a` and `b`, and the **denominator** marks for `c` and for `1`, which sits at position zero because
a whole turn is no turn. **The group is finite exactly when the families take turns round the
circle** — and must keep taking turns under **every restretching**, meaning every multiplication of
all marks by a whole number sharing no factor with the circle. (Classically the *Beukers–Heckman
interlacing criterion*, Invent. Math. 95, 1989; the restretchings are its *Galois conjugates*.)

**Over a common denominator every mark is an integer, so the entire decision is sorting integers and
checking labels alternate.** No root extracted, no angle taken, no matrix built, no float anywhere.

### What returned

- **Fifteen of fifteen** classically closing turn-number rows recovered **by the alternation test
  alone**. The classical table (*Schwarz's list*) is present as a `BTreeMap` **control** and is
  consulted by nothing that decides — a table used to classify its own rows returns the preimage of
  its own declaration.
- **Four of four** declared non-closing triples refused, each with the **adjacent pair exhibited**:
  the elliptic case returns denominator marks `0` and `0` adjacent on a circle of two; all-quarters
  returns numerator marks `1` and `3` adjacent on a circle of eight.
- **The restretching loop is load-bearing, measured: 336** dial pairs in one swept family alternate
  **as drawn** and fail only once spun — `a = 1/30, b = 17/30` alternates as `[1,17]` against
  `[0,15]` and dies at the eleven-fold spin. Without such material the loop could be deleted with
  every test still green, and its agreement would prove nothing.

### Two findings the build produced, the second by the driver refuting

**The geometry reading was not symmetric, and that was a defect rather than a convention.** The
equation is symmetric in `a` and `b`, but the turn at infinity is `a − b`, which flips sign under the
exchange. A signed sum therefore gave one equation two different geometries depending on which dial
was written first. **The sum must be taken on absolute turn numbers** — a turn measured the other way
round is the same turn — and a test now exchanges the dials and requires the reading not to move.

**The flat locus IS the splitting locus.** The driver refuted on a fixture listing a flat triple
among the refusals. The code was right. Identically,

```text
λ + μ + ν = 1 − 2b
```

so a flat sum forces a dial to zero, and a dial at zero lands **on** the denominator family's mark at
zero — which is exactly the coincidence that splits the equation into simpler pieces. **A flat triple
is therefore never merely infinite; it is outside the criterion altogether**, and reporting it as a
refusal reports the wrong species. Confirmed on four flat triples, each splitting at mark zero.

That also sharpens the joint to standing terrain. The flat row is exactly the rotation orders a
lattice admits, which `winding_inertia::lattice_admits_order` already derives on rational grounds —
and it is precisely the row where this criterion does not apply, so the two organs meet at a boundary
rather than overlapping.

### The third outcome is a species, not a fallback

`Splits` is returned by name beside `Closes` and `DoesNotClose`, and a test requires all three to
occur on the declared material. A reading whose third arm never fires is a two-valued test wearing a
third label.

### What this does not claim

It decides **finiteness** of the return group. It does not build the group, does not produce the
algebraic solution, and does not integrate anything. Second order only, rational dials only — the
alternation machinery is written for `n` marks against `n` so the order can rise later, and nothing
here drives it above two.
