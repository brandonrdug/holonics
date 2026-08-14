# The method is a chart transition or a coboundary move, and only the finite strata are tables

**Date:** 2026-08-14
**Truth status:** `proved-standard` for every named classical result in §§1–6 (Liouville–Rosenlicht,
Risch, Richardson, Kolchin, Kovacic, Schwarz, Klein, Beukers–Heckman, Levelt, Katz, Chebyshev,
Cauchy–Hadamard, Berry, Schlesinger and Ramis density, Gross–Zagier–Kolyvagin, Voisin);
`conjecture` for Kontsevich–Zagier, Grothendieck–Katz and Grothendieck's period conjecture, each
marked in place; `established-bounded [measured]` for every statement about this tree;
`interpretation` for the stratification reading in §7 and for the correspondences in §8.
**Evidence:** `measured` on this tree at `2aaf2eb`; every tree claim taken by opening the file, with
the grep or `file:line` given. Two delegated sweeps supplied the literature and the inventory; their
load-bearing claims were re-measured here before being carried.
**Provenance:** Brandon, direct conversation 2026-08-14, setting the object — *"an atlas of
computational structures physically required for algorithms that enable mathematics proofs, so
they'd be like invariant transport patterns"*, *"characteristic properties of group structures and
transport dynamics between them, like chemistry"*, and the integration instance: *"those 'tables of
methods' are not mystical heuristics but rather founded transport mechanisms that apply to the
relevant charts"*. The corrections in §7, the stratification form, and the assistant's own refuted
claims in §9 are the assistant's and are graded as such.
**Band:** TWO SPECIES OF MOVE, NOT ONE / THE GROUP STRATIFIES AND ONLY FINITE STRATA ARE TABLES /
GENUS IS THE RECOGNITION CONDITION / STOKES MATRICES ARE GALOIS GENERATORS / THE CLOSURE IS
DECLARED AND THE THEOREM FOLLOWS THE DECLARATION

---

## Present question

A table of integration methods, a list of series-expansion techniques, a classification of
hypergeometric transformations: are these heuristics, or are they founded transport mechanisms with
recognition conditions? And if they are founded, what founds them?

## 0. What this repository already owns, so nothing below re-derives it

Two objects carry most of the general form already, and a deposit that restates them is churn.

**`H.0362` *Transcendental formulation atlas*** (`definition`,
`papers/source/holonics/transcendence-special-functions.typ:329`) already **is** the atlas object. A
formulation node is `(D, E, ℋ, v, ρ)` — parameter domain, exact expression or algorithm, hypotheses
and branch data, denoted invariant, receiver — and *"an atlas edge is a proved transformation
carrying one node to another while preserving `v`."* Its transformation field already enumerates the
edge species: **substitution with Jacobian, analytic continuation, functional equation, recurrence,
hypergeometric transformation, modular action, and exact algorithm conjugacy.** Its boundary already
bars the obvious error: *"Shared output does not supply an edge."*

**The instrument ladder** already states the general law and drives it. From
`research/records/2026-08-10_THE_INSTRUMENT_DECLARES_THE_APERTURE_AND_THE_REFUSAL_IS_THE_RETURN.md`:

> **An instrument is a declared receiver family. Its aperture is an index condition on a group. What
> the instrument cannot reach it must refuse by name, and adjoining a further instrument is
> purchasing a channel.**

`crates/holonic-engine/src/quintic_chart.rs` (2,875 lines) is that law computed: four charts, each
with a recognition condition, eight named obstruction species carrying evidence, and a **cost law
derived rather than asserted** — killing `k` coefficients leaves `k−1` homogeneous conditions of
degrees `2..k`, so Bezout gives `k!` points, which is exactly why the classical Bring reduction
costs a square root and a cube root. Re-run 2026-08-14, all three Greek problems crossing the
compass wall at neusis, computed:

```text
x^3 - 2      the doubled cube    compass REFUSES  neusis NECESSARY-ONLY  radical RETURNS
x^3+x^2-2x-1 the heptagon        compass REFUSES  neusis NECESSARY-ONLY  radical RETURNS
x^3 - 3x - 1 a trisection cubic  compass REFUSES  neusis NECESSARY-ONLY  radical RETURNS
x^5 - x - 1                      compass REFUSES  neusis REFUSES         radical REFUSES
```

`x⁵−x−1` is refused by neusis and by radicals **for different reasons** — 5 is not 3-smooth; `S₅` is
not solvable — and the driver says both, because two instruments agreeing is not two instruments
being one instrument.

**So the algebraic case is settled, built and driven.** Everything below is about whether it
generalizes, and the answer is: in a precise stratified sense, and not otherwise.

## 1. THE CORRECTION THAT MATTERS MOST — a table has two species of move, not one

The reading *"a method is a chart transition"* is **half right, and merging the halves destroys the
invariant the entire theory runs on.**

| classical "method" | what it is | species | invariant |
|---|---|---|---|
| `u = g(x)` | pullback along a differential-field morphism | **chart transition** | the integral (`H.0207`) |
| Weierstrass `t = tan(x/2)`, Euler, trig substitution | rational parametrisation of a genus-0 curve with a rational point | **chart transition** | the genus |
| contour deformation, residues | enlarge the domain, move the cycle | **chart transition + homology** | `[γ] ∈ H₁(U∖S)` |
| **integration by parts** | modify the representative by an exact term | **coboundary move** | the de Rham class |
| **Hermite reduction** | the algorithmic form of by-parts | **coboundary move** | the de Rham class |
| **partial fractions** | global form → local principal parts | **local–global decomposition** | `H¹(P¹, O) = 0` |
| Feynman's trick, `∂_t ∫` | the connection on a family | **Gauss–Manin connection** | the local system |
| creative telescoping | produce `L` and `G` with `Lf = ∂_x G` | **certificate for the connection** | holonomic rank |

**Integration by parts is not a chart transition.** It changes the representative and changes nothing
in cohomology — which is precisely why it is the right tool, because the integral depends only on the
class. Every complete algorithm in this area has the same two-phase shape: **reduce (kill the exact
part), then extract the class (residues, periods).** That is not a reading imposed here; it is how
reduction-based creative telescoping and `p`-adic cohomology computation are organised.

**Measured in this tree:** `H.0207` *Change of variables carries the Jacobian* is registered
`proved-standard` at `geometry-calculus.typ:263`, with the boundary *"Rebase is not measure-preserving
unless the Jacobian says so."* **Integration by parts is not a registry entry at all** — it appears
only as a hypothesis inside a heat-semigroup entry — and **partial fractions has zero occurrences.**
Given that by-parts is one of the three generators of the period conjecture (§5), that is the
sharpest registry gap this survey found.

## 2. Genus is the recognition condition, and it is computable

The whole substitution row of the table has **one** recognition condition. `t = tan(x/2)` is
stereographic projection from `(0,−1)`; it exhibits that the curve `s² + c² = 1` is **genus 0**,
hence rationally parametrisable. Euler's three substitutions for `√(ax²+bx+c)` are exactly the three
ways to project a conic from a rational point — from infinity when `a > 0`, from a rational root
when the discriminant is square, from `(0,√c)` when `c > 0`.

**And the failure boundary is the same invariant.** `√(x³+ax+b)` is genus 1; genus is a birational
invariant, so no rational parametrisation exists and the integral is elliptic, not elementary.

This is the strongest support the reading has: **a signature read off the object decides which chart
applies, and the same signature decides when none does.**

One further row is completely classified by a rational test — **Chebyshev, 1853**:
`∫x^m(a+bx^n)^p dx` is elementary **iff** one of `p`, `(m+1)/n`, `(m+1)/n + p` is an integer. Three
cases, forced, decidable in `ℚ`.

## 3. The closure is declared, and the theorem follows the declaration

**Liouville's structure theorem** (Crelle 13, 1835; modern proof Rosenlicht 1968) constrains the
*answer*, not the existence: if `f` has an elementary antiderivative then
`f = v' + Σᵢ cᵢ uᵢ'/uᵢ` with `v, uᵢ` in the field. **That collapse is why an algorithm is possible** —
the search space falls from all elementary extensions to the field plus logarithms of its elements,
with a priori degree bounds.

**`∫e^{−x²}dx` is a rank obstruction, not a difficulty.** Liouville's criterion for `∫f e^g` requires
`a` with `f = a' + ag'`; here `a' − 2xa = 1`. A pole of order `m` forces a pole of order `m+1` on the
left and none on the right, so `a` is a polynomial; and `deg(a' − 2xa) = deg a + 1 ≥ 1 ≠ 0`. **Two
degree contradictions on an exact rational linear system.**

**And the declaration can be enlarged, with the theorem following.** Singer–Saunders–Caviness
(*SIAM J. Comput.* 14, 1985) proves the Liouville-type structure theorem for elementary functions
**plus a declared finite set of new transcendentals**; Cherry (1985, 1986) gives the decision
procedures for the error function and the logarithmic integral. **Declare more charts, get a new
structure theorem and a new decision procedure.** That is the aperture doctrine arriving from
analysis with citations attached, and it is the sharpest confirmation of the reading in this record.

**Risch (1969)** decides elementary integrability over a purely transcendental elementary tower, by
induction on tower height: Hermite reduction (a coboundary move), Rothstein–Trager (residues are the
roots of `Res_t(p − zq', q)`), then descent. **Its limits are two distinct things and must not be
merged**: the *constant-field problem* — Risch is a decision procedure **relative to constant
arithmetic** — and **Richardson's theorem** (1968), whose undecidability requires the **absolute
value** in the expression class and is routinely misquoted without it. For exp-log without `|·|`,
zero-testing is decidable *conditional on Schanuel's conjecture*.

## 4. The group stratifies, and only the finite strata are tables

**Kolchin's theorem, stated exactly:** a linear ODE is solvable in Liouvillian terms **iff the
identity component `G°` of the differential Galois group is solvable.** It is `G°`, and the
distinction is not pedantic — if `G` is finite and non-solvable, `G° = {e}` is trivially solvable,
and correctly so, because all solutions are then algebraic hence Liouvillian. **Stating it with `G`
gets Schwarz's list exactly wrong.**

**Kovacic (1986)** makes it a literal finite table at order two. Normalise to `y'' = ry`; then
`G ⊆ SL₂(ℂ)` and **exactly one of four cases holds**, the four being the classification of algebraic
subgroups of `SL₂(ℂ)`:

```text
1  reducible          a solution e^{∫ω} with ω rational           degree 1
2  imprimitive        ω algebraic                                 degree 2
3  finite primitive   tetrahedral, octahedral, icosahedral        degree 4, 6, 12
4  G = SL2(C)         NO Liouvillian solution
```

**Schwarz (1873)** is the periodic table by name: all solutions of the hypergeometric equation are
algebraic iff the exponent-difference triple lies in **fifteen** rows — one infinite dihedral family
and fourteen sporadic triples, 2 tetrahedral, 2 octahedral, 10 icosahedral. **And it is forced:**
finiteness is the spherical condition `1/p + 1/q + 1/r > 1`, which admits exactly `(2,2,n)`,
`(2,3,3)`, `(2,3,4)`, `(2,3,5)`, because a finite subgroup of `PSL₂(ℂ)` is `Cₙ`, `Dₙ`, `A₄`, `S₄` or
`A₅` (Klein). Beukers–Heckman (1989) generalise it to all ranks with an **interlacing criterion**.

### The joint to what this tree already computes, and 5 is the number that separates the cuts

```text
1/p + 1/q + 1/r  >  1   spherical    FINITE     (2,2,n) (2,3,3) (2,3,4) (2,3,5)   <- Schwarz
                 =  1   Euclidean    infinite   (3,3,3) (2,4,4) (2,3,6)           <- crystallographic
                 <  1   hyperbolic   infinite
```

The Euclidean row is **exactly** the crystallographic orders, and
`crates/holonic-engine/src/winding_inertia.rs:2788` already computes that cut —
`lattice_admits_order = niven_value(1, order).is_some()`, **derived from Niven's theorem rather than
hardcoded**, with 5 excluded. **`(2,3,5)` is finite but not crystallographic.** Finiteness of
monodromy and lattice-compatibility are two cuts of one rational inequality, and **5 is the number
that separates them.** One `Rat` comparison joins Schwarz's list to an organ this body already owns,
and nothing in the tree says so — measured: no owner for the finite subgroups of `SO(3)`, and
`Schwarz` occurs once in the corpus meaning Ramond–Neveu–Schwarz.

### Where the group stops being a table — and this is the correct general form

**Generic linear ODEs have `G = SL_n` or `GL_n`: positive-dimensional, a continuum of conjugacy
classes, no table.** The finite tables are the **degenerate stratum**. So the reading's honest form
is not *"the atlas is closed because a group decides it"* but:

> **The atlas is stratified by the group. The finite strata are enumerable and forced; the generic
> stratum is not a table.**

That is stronger, because it says exactly where to look for tables. Two further bounds: the nonlinear
analogue (Morales-Ruiz–Ramis) is a **necessary condition only** — an obstruction, not a
classification — and the arithmetic recognition condition, **Grothendieck–Katz `p`-curvature**, is
**open**.

## 5. Connection is transport, monodromy is holonomy, and this one is literal

For the hypergeometric equation the singular points are exactly `{0, 1, ∞}`, and **Riemann's
theorem** says any rank-2 Fuchsian equation on `P¹` with three regular singular points is carried to
it — *there is essentially one such equation.*

The equation is a **flat connection**, and parallel transport of a flat connection depends only on
the homotopy class of the path. **Therefore holonomy and monodromy are identical, not analogous.**
Connection formulae are the **transition functions** of the local system in the three-disc atlas.
And the division of labour is exact: **local monodromy is free** — diagonal in its own basis, read
straight off the exponents — while **global monodromy costs exactly the connection matrices.** That
is the precise sense in which connection formulae are transport.

The connection matrices' entries are Gamma ratios, i.e. Beta values, i.e. **periods**; and the Euler
integral makes `₂F₁` **a period of an algebraic family** whose monodromy **is** that family's
Gauss–Manin connection. Connection matrix, monodromy and period are three faces of one local system.

**Rigidity is the strongest form of "the recognition condition determines the transport":** Levelt
(1961) — local exponent data determines global monodromy up to conjugacy; Katz (1996) — every
irreducible rigid local system is built from a rank-1 one by middle convolutions, made algorithmic by
Dettweiler–Reiter (2000). **An algorithmic atlas of transport patterns with a finite generating set
of moves, proved.**

## 6. Divergence is not a defect — it carries Galois generators

**The invisibility claim is correct and elementary.** `e^{−z} ∼ 0` in `Re z > 0`: every Poincaré
asymptotic coefficient vanishes, so `f` and `f + e^{−z}` have the *same* expansion. **The asymptotic
series is a quotient, and what it deletes is exactly the exponentially small term.** That is
`CLAUDE.md` §0j's phase-object theorem in analysis, needing no physical model.

**The Stokes jump sits where the term is maximally subdominant** — where it is most invisible to a
magnitude comparison. **And the discontinuity is the reading, not the object:** Berry (1989) showed
that with optimal truncation the Stokes multiplier varies *smoothly*, as `½(1 + erf σ)` over angular
width `O(|z|^{−1/2})`. **A receiver's coarse face presented as the object, with a citation and an
explicit smoothing profile.**

**And the deleted datum is recoverable, which is the resurgence theorem:** factorial divergence ⟺ a
finite singularity of the Borel transform ⟺ an exponentially small nonperturbative term. The
large-order growth reads the Stokes constant off the coefficients.

### The headline, and it is `proved-standard`

**Ramis density theorem:** the differential Galois group at an irregular singular point is the
smallest algebraic group containing the exponential torus, the formal monodromy, **and all the Stokes
matrices.** (Regular case: Schlesinger — monodromy is Zariski-dense in the Galois group.)

> **So the divergence of the series is not a defect of the method. It is the carrier of Galois-group
> generators that the convergent case does not have. "Divergence is phase" and "the group is the
> valence" are the same statement at an irregular singular point.**

## 7. The completeness question already exists and is exactly the right shape

**Kontsevich–Zagier (2001).** A period is a value of an absolutely convergent integral of a rational
function with rational coefficients over a domain cut out by polynomial inequalities with rational
coefficients — equivalently, an entry of the period matrix pairing algebraic de Rham cohomology
against singular homology. **The conjecture:** any two integral representations of one period are
related using only

```text
1. additivity            (in integrand and domain)
2. change of variables   (pullback)          <- the chart transition of section 1
3. Stokes' formula       (by parts)          <- the coboundary move of section 1
```

**Status: open.** Ayoub proved a relative version (Annals 2015); it is equivalent to injectivity of
the motivic period map, where it meets Grothendieck's period conjecture.

**That is the completeness claim for exactly the atlas being asked for** — three generators, one of
each species of §1 — and it is narrower in three named ways: the class is restricted to rational
integrands over `Q̄`, so `∫e^{−x²}` is an *exponential* period in the strictly larger ring; it is about
relations between numbers, not decidability, and yields no algorithm even if true; and it is disjoint
from the Liouville/Risch atlas, which is about *functions* — the bridge between them is Gauss–Manin,
and it is a bridge rather than an identity.

`H.0361` *Period number* is registered `definition`; **the conjecture is not registered.**

## 8. The Millennium rows as statements about the atlas

Nothing here is a claim, and `canon/THE_MILLENNIUM_FRAME.md` forbids grading a deed by a row.

| | as a transport statement |
|---|---|
| **RH** | the functional equation `Λ(s) = Λ(1−s)` **is** a chart transition and RH places the zeros on its fixed locus. `Γ(s/2)` is the archimedean local factor — the chart at infinity — which is why the *completed* function is the object. |
| **Hodge** | is the period pairing surjective onto Hodge classes from the cycle side? The obstruction is the **cokernel** of the cycle class map. Voisin (IMRN 2002) is the theorem behind *realization pays*: drop the ample realizer and the conclusion dies. |
| **Navier–Stokes** | does the solution stay in the chart? Scaling `u ↦ λu(λx, λ²t)` is a chart transition; **3D supercriticality of the energy norm is the atlas failure** — the conserved quantity sits below the critical scaling. |
| **Yang–Mills** | non-abelian holonomy generates a genuine group; a mass gap is a forbidden band in the transfer operator's spectrum. **Reflection positivity is measured absent here**, and the module's own bar on the phrase is correct and kept. |
| **BSD** | two charts — arithmetic rank with `Reg` the determinant of a positive form on a realizer population, and analytic order of vanishing — with the leading coefficient a **period × regulator**. `H.0357` computes the real period. |
| **P vs NP** | §9 below, because the obvious mapping is wrong. |

### `H.0357` is the one live bridge, and nothing in the tree says so

`H.0357` (`proved-standard`, `transcendence-special-functions.typ:201`) carries

```text
K(k) = ∫₀^{π/2} dθ/√(1 − k² sin²θ) = (π/2)·₂F₁(1/2,1/2;1;k²) = π/(2·AGM(1,√(1−k²)))
```

That single entry is the **BSD real period**, a **`₂F₁`**, and a **quadratically convergent mean
iteration** — and its exponent differences `(0,0,0)` are all unipotent, monodromy `Γ(2)`, **infinite**,
decisively off Schwarz's list. `λ = k²` is the modular lambda whose `S₃` orbit is the six anharmonic
values. **One `proved-standard` entry sits on the join of every section of this record.**

## 9. Where the assistant's reading was wrong, kept because the corrections are the content

1. **"A method is a chart transition."** Half of them are **coboundary moves** (§1). Merging them
   destroys the de Rham class, which is the invariant that makes both Risch and the period conjecture
   work.
2. **"Where the group is finite the atlas is closed, so a table of methods is a periodic table."**
   True in four named places — Kovacic's four cases, Schwarz's fifteen rows, Chebyshev's three,
   Klein's five finite subgroups — and **false generically**, because the generic differential Galois
   group is positive-dimensional. The stratified form in §4 is the correct one.
3. **"A table of integrals is an instance of localized P=NP."** **Facile as stated, on three counts.**
   The verification polarity is inverted — verification means zero-testing, which is the undecidable
   half. A finite table is the **advice model**, `NP ⊆ P/poly`, which Karp–Lipton would collapse `PH`
   for, so invoking it assumes the hypothesis. And a table is incomplete by construction while the
   value of the reading lives in completeness. **The sound instances are Liouville/Risch and
   Kovacic** — an a priori bound making the candidate population finite and exhaustible, which is
   `TABLET_THE_CHART.md`'s own stated mechanism verbatim — **and certificate-producing algorithms**
   (Zeilberger/WZ, Kovacic's `ω`, PSLQ), which are honestly witness-shaped.
4. **"This tree already relates the six trigonometric ratios to the six anharmonic transforms."**
   **False as measured: `anharmonic` occurs ONCE in the entire live tree**, unenumerated, inside
   `H.0201` at `geometry-calculus.typ:64`. And the correspondence is with the **squares**:
   `λ = sin²θ` gives `{sin², cos², csc², sec², −tan², −cot²}`. **Two of the six carry a minus sign,
   and they are exactly the two that CROSS the pair `{λ, 1−λ}`** rather than fixing or inverting it —
   the half turn appearing on the crossing, which is `CLAUDE.md` §2b's *a sign is a passage, never a
   state*, instantiated. None of it is deposited.
5. **"Convergence is decided by geometry rather than by coefficients."** Cauchy–Hadamard is an
   *identity*, so the "rather than" is wrong. The defensible claim: **the cause is a singularity, and
   it lives in a chart the problem was not posed in** — `1/(1+x²)` is bounded and real-analytic on all
   of `ℝ` and has radius 1 because of poles at `±i`. Singularity analysis makes it a two-way
   dictionary, not a preference.

## 10. What is owed, ranked by how little new machinery each needs

1. **`∫R(x)e^{g(x)}dx` decided as the consistency of an exact rational linear system.** Liouville's
   criterion is one linear system over `ℚ`; the return is its rank and its inconsistent row. Makes
   *"`∫e^{−x²}` is not elementary"* a rank deficiency with an exhibited obstruction. Two frames —
   consistency, then differentiate the produced `a·e^g` back. Controls both ways: `2xe^{x²}` admits
   with `a = 1`, `e^{−x²}` and `e^x/x` refuse for two different reasons.
2. **Hermite reduction plus Rothstein–Trager, with the period vector as the invariant.** The cheapest
   high-value build: `euclidean_resultant`, `resultant_in_eliminated_variable`, the complete
   `rational_root_census` and Sturm isolation all exist. **And the gauge has a non-trivial orbit by
   construction** — Hermite genuinely moves the representative while the residues must not move —
   which is exactly what `PivotRule::ALL` failed to have.
3. **Hypergeometric finiteness by the Beukers–Heckman interlacing criterion, cross-checked against
   Schwarz's fifteen rows.** *Do not call it monodromy* — computing a representation needs `ℤ[ζ_h]`,
   which this workspace does not have, and naming it so would repeat a convicted defect. Interlacing
   is `Rat` fractional parts over `(ℤ/h)*`: no roots, no floats, no matrices. **Honest only if the
   computed criterion runs** — consulting the table alone returns the preimage of an authored field
   and carries zero evidence. Negative control: `₂F₁(1/2,1/2;1;·)`, already `proved-standard` here,
   must return infinite.

## What this record does not claim

No new mathematics: every classical result is cited to be composed with, not rederived. No Millennium
movement, and no deed anywhere may be graded by §8. It does not claim the machine performs
integration, computes a monodromy representation, or owns a differential field — **measured, this
tree has no derivation on any field, and the only derivation-like operator in it is the formal
polynomial derivative.** It schedules nothing.
