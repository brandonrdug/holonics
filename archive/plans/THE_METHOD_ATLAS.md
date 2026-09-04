# The method atlas

**Date:** 2026-08-15
**Status:** a construction plan under `docs/plans/THE_ROADMAP.md`, the single active roadmap.
This one covers the atlas itself. It supersedes
`THE_TYPED_TRANSPORT_ATLAS.md` as the *object*; that document remains in force as the plan for one
**instrument**, and §3 says exactly what it is and is not.

---

## 0. The object, in Brandon's words, and the drift that is being corrected

> *"an atlas of computational structures physically required for algorithms that enable mathematics
> proofs, so they'd be like invariant transport patterns… characteristic properties of group
> structures and transport dynamics between them, like chemistry. A good example in mathematics is
> integration, there are many varying techniques and many specifically applied tables of patterns to
> particular problems, where those 'tables of methods' are not mystical heuristics but rather founded
> transport mechanisms that apply to the relevant charts."*

And the warning attached to the material:

> *"if you keep referring to 'Lean/mathlib' you're going to confuse yourself into thinking that we
> care specifically about Lean & mathlib, when they are just the encoded mediums that contain the
> information in which we want to decompose."*

**The assistant did exactly that.** `THE_TYPED_TRANSPORT_ATLAS.md` ran six movements, and every one
of them was about the **codec**: a Lean reader, a Lean conclusion relation, a Lean binder domain, a
Lean emission, Lean tactic edges. `rw` is substitution *in a proof language*, not substitution in
the mathematics. **An atlas of tactic applications is an atlas of the medium.**

The cause is legible: the method-atlas record's own ranked list of what was owed had **three items,
all three were built on 2026-08-14**, and instead of extending the atlas the assistant went sideways
into the pipeline that reads the medium.

---

## 1. What an atlas row is, and the three that stand

**A row is a recognition condition computed exactly on a mathematical object, which decides which
transport applies — and decides equally when none does.** That shape is the whole content, and the
three standing rows all have it:

| row | object | recognition | failure returns as |
|---|---|---|---|
| `elementary_chart` | `∫ R e^g` | consistency of one exact rational linear system; `deg a = deg R − deg g + 1` forces a finite candidate population | a **rank deficiency with an exhibited annihilating combination**, plus a separate structural refusal for a simple pole |
| `hermite_reduction` | a rational integrand | the **coboundary move**: change the representative by an exact term, leave the residues | the class as a Rothstein–Trager resultant, **no root extracted** |
| `hypergeometric_closure` | a three-site turning equation | do the two families of marks **alternate**, under every restretching | infinite return group; flat triples land **outside** the criterion, meeting `winding_inertia::lattice_admits_order` at a boundary |

None consults a table of answers. Each computes a signature and the signature decides.

---

## 2. The rows the material argues for next

Both are named in the method-atlas record and neither is built. Genus appears nowhere in the tree as
a curve invariant; Chebyshev's criterion appears nowhere at all.

### THE SUBSTITUTION ROW IS RECOGNISED BY GENUS

**One invariant decides the entire substitution row.** `t = tan(x/2)` is stereographic projection
from `(0,−1)`: it exhibits `s² + c² = 1` as **genus 0**, hence rationally parametrisable, and *the
parametrisation is the substitution*. Euler's three substitutions for `√(ax²+bx+c)` are the three
ways to project a conic from a rational point — from infinity when `a > 0`, from a rational root when
the discriminant is square, from `(0,√c)` when `c > 0`.

**The failure boundary is the same invariant.** `√(x³+ax+b)` is genus 1; genus is a birational
invariant, so no rational parametrisation exists and the integral is elliptic. *A signature read off
the object decides which chart applies, and the same signature decides when none does.*

**Complete when** genus is computed exactly for the declared curve family, a genus-0 curve with a
rational point returns its parametrisation **and the Jacobian that makes it a chart transition**
(`H.0207`), and a genus-1 curve returns the refusal with genus as its reason.

**Falsifier:** a curve called genus 0 for which no parametrisation is produced, or genus 1 for which
one is. Both arms must be exercised; a fixture that can only fail one way proves nothing.

### THE BINOMIAL DIFFERENTIAL IS THREE CASES AND THEY ARE ALL OF THEM

`∫ x^m (a + b x^n)^p dx` is elementary **iff one of `p`, `(m+1)/n`, `(m+1)/n + p` is an integer**
(Chebyshev, 1853). Three cases, forced, decidable in `ℚ`.

**This row is aperture-complete**, and the standing rule says an aperture-complete instrument must
say so rather than looking extensible.

**Complete when** the three cases are computed over `ℚ` with no float, each case returns its
substitution, and a fourth-case input returns non-elementary **with the three tests exhibited as
having failed**.

**Falsifier:** an input outside the three cases returning elementary.

---

## 3. What the Lean work is, named correctly

It is an **instrument**, not a row. The kernel is an exterior returning port: it adjudicates a
construction the body emits, and this session made that adjudication trustworthy —

- a reader whose four measured defects fell by two orders of magnitude, and whose arrival graph
  nearly doubled;
- `v` verified against the kernel **7 of 7** and `D` against Lean **17 of 17**;
- a typed emission whose structural refusals went **147 → 0**;
- a proved edge deposited into `derivation_atlas`, moving `{Cells, BoundaryRank, FillingRank}`.

**Those are floors for the instrument.** What they are not is a transport pattern in mathematics.
The instrument's honest use in this plan is narrow and real: **a row's recognition condition can be
posed to the kernel as a theorem**, so a row is not graded only by its own arithmetic.

**And its own bound stands unchanged:** the typed arm admits zero paths the untyped one did not.

---

## 4. The edges, which are what "phases between each other" means

A row is a node. The edges are the typed moves between them, and the record already fixes the
species:

```text
  chart transition   substitution, and it CARRIES A JACOBIAN            H.0207
  coboundary move    Hermite, integration by parts — changes the
                     representative by an exact term, changes no class
  local-global       partial fractions, because H¹(P¹, O) = 0
```

**Merging the first two destroys the invariant**, which is the correction the record calls the one
that matters most. And every complete algorithm here is **two-phase: reduce, then extract the
class** — which is why an evaluation composes a coboundary move with a class extraction rather than
searching.

**Complete when** one integrand is carried end to end through *recognise → chart transition →
coboundary reduction → class extraction*, with each step's species named and its invariant stated.

---

## 5. The stratification, which says where a table exists at all

Kolchin: solvable in Liouvillian terms iff the **identity component** `G°` is solvable. Finite
tables exist and are forced in four named places — Kovacic's four cases, Schwarz's fifteen rows,
Chebyshev's three, Klein's five finite subgroups of `PSL₂(ℂ)`. **Generically `G = SL_n`,
positive-dimensional, and there is no table.**

So the atlas is stratified by the group, the finite strata are enumerable, and **the generic stratum
is not a table** — which is a stronger statement than a complete table would be, because it says
where to look.

**The joint to standing terrain, and `5` is what separates the cuts:** `1/p+1/q+1/r > 1` is
spherical and finite; `= 1` is Euclidean and **exactly** the crystallographic orders
`winding_inertia::lattice_admits_order` already derives from `niven_value`; `< 1` is hyperbolic.
`(2,3,5)` is finite but not crystallographic. One `Rat` comparison joins Schwarz's list to terrain
this tree already computes, and it is not built.

**Re-measured 2026-08-15 and it is PARTIAL — the comparison is built and the JOINT is not.**
`cargo test -p holonic-engine --lib hypergeometric_closure` passes 12, and `curvature_sign` is
exactly that one `Rat` comparison — `at_zero.abs() + at_one.abs() + at_infinity.abs()` against
`Rat::one()`, returning `Spherical`/`Flat`/`Saddle`. **What is genuinely absent is the composition:**
no site calls both `curvature_sign` and `winding_inertia::lattice_admits_order`. The joint is stated
in a doc comment rather than computed, which is the shape this file exists to catch.

---

## 6. Standing bars

**No Millennium row grades a deed here.** The atlas's relation to those problems is that it is where
the framework's primitives land, not a claim on any of them.

**A table of integrals is not an instance of localized P=NP.** Verification means zero-testing, which
is the undecidable half; a finite table is the advice model; and a table is incomplete by
construction. The sound instances are Liouville/Risch and Kovacic — an a priori bound making the
candidate population finite and exhaustible — and certificate-producing algorithms.

**Do not name a computed object by a group it was not computed as.** The alternation criterion is not
monodromy: computing a representation needs `ℤ[ζ_h]`, which this workspace does not have.

## What this plan does not claim

It schedules no capability beyond the two rows and the composition in §4, grades nothing by an
external epistemology, and asserts no result in mathematics. The Lean instrument's floors stand and
are cited as floors. Whether the atlas's rows recur across the library is the centrifuge's question
and is not assumed here.
