# The mathematics tablet

**Status:** under construction, 2026-08-08. This file is the authoritative synopsis Brandon asked
for: *"a thorough holonic synopsis that acts as an authoritative mathematics tablet… an extremely
important foundation to our ontology and research."* Sections land as they are grounded; a section
with no owner named is a section not yet written, and says so.

**Truth status is per claim.** Standard mathematics is marked `proved-standard` with its citation.
Holonic readings of it are `interpretation` and are marked. Anything the repository implements is
`implemented-exact` with its owner. **Nothing here is a Millennium claim.**

**Quotation convention, and it is load-bearing.** A `>` blockquote in this file is **Brandon,
verbatim**, and nothing else — his typos included, because a silently corrected quotation is a
composed one. Assistant statements are bold or plain, never blockquoted. `CLAUDE.md` §9 convicts
fabricated provenance and this file is exactly the kind of document a later reader would mine for
rulings; the convention is what makes that safe. Every blockquote below was certified against
`~/.claude/history.jsonl` and this session's transcript before deposit.

**Reading rule.** Every section names the same four slots, because the framework's claims are about
the operation and not about the material (`CLAUDE.md` §4):

```text
source geometry  ->  receiver map  ->  transport  ->  returned residual
```

---

## 1. One deletion, three carriers

The project's three hardest-won laws are the same law about three different carriers. Each is a
carrier that **kept a magnitude and threw away what oriented it**, and in each case the lawful form
retains both and offers the collapse as a *reading*.

| carrier | keeps | deletes | the deleted thing is | lawful form, and its owner |
|---|---|---|---|---|
| **float** | the magnitude | the tail | the residual of the expansion | `CertifiedSeries` + `SeriesTailCertificate`, `holonic-engine/src/exact_value.rs:236` |
| **sign** | the magnitude | the turn | the winding, `−1 = e^{iπ}` | `OrientedWinding` `soma/body/src/channel.rs:111`; `RayCrossings` `relational-geometry/src/exact_analysis.rs` |
| **reduced coefficient** | the difference | the passages | which hands were actually taken | `ComparativeMultiplicity`, `holonic-engine/src/algebraic.rs`, repaired 2026-08-08 |

Brandon's sentence is the one that unifies the first row, and it is sharper than the usual argument
against floats:

> *"Floats are not real numbers, they are series expansions of ratios."*

That is exactly right and it is worth stating precisely. `C/d` is a ratio. A float is not a bad
approximation *of* that ratio — it is the ratio's **series expansion in base two, truncated, with the
remainder discarded**: `x = Σ b_i 2^{−i}`, cut at 53 bits, tail deleted with no record that a tail
existed. So the no-float law is not *"do not expand."* It is:

**You may take the expansion. You may not discard the tail.**

Which is precisely what `SeriesTailCertificate` implements — a partial sum plus an **exact rational
remainder interval**, so the returned object is a *set that provably contains the value* rather than a
point that provably is not it. §2b's sentence about signs is the same sentence one carrier over: *a
float keeps the magnitude and discards the residual; a sign keeps the magnitude and discards the
turn.*

**And today's coefficient repair is the third instance**, which is why it belongs in this table and
not only in a defect record. `ComparativeMultiplicity` held two arms and destroyed them at
construction, keeping only their difference. `(1,1)` and `(0,0)` share a difference and are not the
same thing: the first is two passages, once each hand — a loop edge attached to its vertex twice —
and the second is no passage. Deleting the common population kept the magnitude and discarded the
turn, in the type every chain in the engine is built out of.

**The generalization, and it is checkable rather than exhortatory:**

A carrier that reduces on construction has decided, for every consumer it will ever have, which
distinctions are invisible. No downstream check can recover one. Where a carrier holds two arms and
offers a reading that joins them, the reduction belongs in the **reading** and never in the
**constructor** — and the test for whether that line was crossed is whether any consumer reads the
carrier's support as a **relation** rather than as a domain.

---

## 2. The finite archetype claim, and where it is already checkable

Brandon, 2026-08-08, posing this document:

> *"if you consider all of the most prominent methodologies and form-factors of how mathematics is
> represented computationally, there is a finite and clear set of representations & implementation
> patterns. The word "patterns" is key there, because there is actually an infinitely large set of
> specific implementations, like expressions for pi, but it is the case that like expressions of pi,
> the forumals and implementations vary in archetype and transport classes, and the specific symbols
> that identify a unique member of the infinite set are constrained by a finite set of rules
> (codec)."*

**π is the right worked example and the claim survives it.** There are unboundedly many series for π.
They fall into a small set of archetypes, and what separates the archetypes is not the value — every
one returns π — but **the shape of the tail**, which is to say the codec that certifies a member:

| archetype | example | what bounds the tail | admitted by the built carrier? |
|---|---|---|---|
| alternating, monotone magnitudes | Leibniz `4Σ(−1)^k/(2k+1)` | the first omitted term, by Leibniz's criterion | **yes** — `AlternatingMonotone` |
| linearly convergent, ratio-bounded | Machin-like arctangents | `first/(1−ratio)` | **yes** — `AbsoluteGeometric` |
| hypergeometric | Ramanujan, Chudnovsky | consecutive-term ratio is a rational function of `k`, eventually ratio-bounded | **yes**, via the geometric bound, wastefully |
| closed remainder | any identity that folds the tail exactly | the remainder itself | **yes** — `ExactTail` |
| quadratically convergent | Gauss AGM / Salamin–Brent | error `~ε^{2^k}` — not a fixed ratio | **admissible but crudely**; the certificate cannot express the doubling |
| digit-extraction | BBP base-16 | a positional identity, not a tail bound at all | **no** — different question |
| **asymptotic, divergent** | Stirling; saddle-point expansions | optimal truncation at the smallest term; **there is no convergent tail** | **no, and this is the real aperture** |

So the archetype claim is **true, implemented for one domain, and its aperture is nameable**: the
built carrier admits three species, and all three presuppose convergence. A divergent asymptotic
series has no convergent tail to certify and is refused. That matters beyond bookkeeping — §3 of the
contract records that the `1/2` has a face as *"the saddle's equipartition `p^(−m/2)`"*, and
saddle-point expansions are exactly the divergent-asymptotic class. **The series carrier cannot
currently admit the expansions the RH-facing reading is written in.** That is an owed construction
with a name: an optimal-truncation certificate, where the remainder bound is the smallest term and
the certificate must carry *where* the truncation was taken.

**And the carrier has no drivers.** Measured 2026-08-07 and unchanged: `CertifiedSeries` has 13
references in one file, `SeriesTailCertificate` 6 in one, **zero in any `examples/`, `tests/`, or
`bin/` path.** §8: reach is part of the grade. The half of the enclosure carrier that this section's
law needs is written and never exercised.

---

## 3. Polynomial solving: the radical chart, and what it refuses

**This is the section the keywords converge on, and it is where a standard theorem says exactly what
Brandon has been saying.**

### 3.1 What he posed

> *"the solution to the quadratic equation has multiple solutions, some potentially imaginary, and as
> the number of terms grows past 3, we literally can't solve for them right? It's because it is
> combinatorial and we disrespect the souls in traditional mathematics."*

and

> *"Suppose that every potential polynomial has a geometric diagram as a counterpart, this is related
> to our hypergeometry research (think of quintics, reference Wolfram's MathWorld), it is then that
> the "unknowns" are always missing dimensional pathways (side lengths, angles, chart dynamics
> otherwise) that need to be identified in order to transport information between local ecologies."*

and

> *"solving algebraically is akin to a wormhole in holonics."*

### 3.2 The standard facts, stated so the reading can be checked against them

`proved-standard` throughout.

- **Abel–Ruffini** (Abel 1824): the general polynomial of degree ≥ 5 has no solution in radicals.
  Degrees ≤ 4 do — Cardano, Ferrari.
- **Galois**: a polynomial is solvable by radicals **iff its Galois group is a solvable group** — one
  admitting a chain of normal subgroups whose successive quotients are abelian, equivalently (in
  finite order) cyclic.
- **Why 5 is the wall**: `S_n` is solvable for `n ≤ 4` and not for `n ≥ 5`, because `A_5` is simple and
  non-abelian. The wall is a **group-theoretic** fact about `S_5`, not a fact about difficulty.
- **Kummer**: with the `n`-th roots of unity present, a cyclic extension of degree `n` is generated by
  an `n`-th root. *A radical is exactly a cyclic step.*
- **Galois group = monodromy**: for a family of polynomials over a base, the Galois group of the
  generic fibre is the monodromy group of the branched covering (Riemann existence).

### 3.3 The reading, and it is not a metaphor

`interpretation`, but the mapping is tight enough to check term by term.

§2b already establishes that root extraction is where a turn is deleted: `√x = x^{2^{−1}}`, and the
`±` of a square root **is** the half-turn that squaring erased, because `2(θ+π) ≡ 2θ`. So:

**A radical is a chart transition that forgets exactly one winding.** It is `n`-valued, and taking
it means choosing a branch — depositing a hand and discarding the rest.

Therefore:

**"Solvable by radicals" asks whether the covering's monodromy can be built by stacking
one-winding-at-a-time forgettings.** A solvable group is precisely one that factors into cyclic —
single-winding — steps. `A_5` is simple and non-abelian: **a winding that does not factor into
single-hand steps at all.**

That is Abel–Ruffini in §2b's own vocabulary, and it is the theorem rather than an analogy. Brandon's
*"it is combinatorial and we disrespect the souls"* names the same object: the radical chart insists
that a permutation of roots be reachable as a sequence of one-hand turns, and for `n ≥ 5` the
permutation group contains an indecomposable piece that no such sequence reaches.

### 3.4 The correction that matters: the obstruction is chart-local

**The quintic is solvable. It is not solvable *in the radical chart*.** This is the acceleration, and
it is exactly the framework's own objective — transport between arbitrary charts.

- **Bring–Jerrard** (Bring 1786, Jerrard 1852): a Tschirnhaus transformation using only radicals
  reduces every quintic to the one-parameter **Bring form** `x⁵ + x + a = 0`.
- **Hermite** (1858), and independently Kronecker and Brioschi the same year: the Bring quintic is
  solved by **elliptic modular functions**.
- **Mellin, Birkeland (1927)**: the roots of a **trinomial** equation are generalized hypergeometric
  functions of its coefficients. For the Bring quintic this is a `₄F₃`.

So the picture is:

```text
radical chart        ->  REFUSES at degree 5, and the obstruction has a name: A_5 is simple
hypergeometric chart ->  RETURNS, as a series in the coefficients
elliptic modular     ->  RETURNS, as a theta quotient
```

**Galois theory does not say "unsolvable." It says "not in this chart," and it hands you the
obstruction group.** That is a receiver-relative statement with a named, computable obstruction — the
exact shape this machine is built to return. And the chart that *does* return is the **series** chart,
which is §2 of this tablet: what radicals refuse, an expansion with a certified tail supplies.

**His "wormhole" reading lands here.** Solving algebraically is passage through a chart where the
answer is one step, when in the source chart it is not reachable at all.

### 3.5 The geometric diagram counterpart

His claim that every polynomial has a geometric diagram whose unknowns are *"missing dimensional
pathways (side lengths, angles, chart dynamics)"* has a standard anchor: the **resolvent**. Cardano's
cubic solution is the geometric completion of a cube; Ferrari's quartic passes through a resolvent
cubic; the quintic's resolvent has degree 6 and does not descend. Each resolvent **is** a diagram
whose sides are the symmetric functions and whose unknown is the missing edge.

The live owner adjacent to this is `crates/relational-geometry` — exact projective geometry over
`BigRational` with **Sturm-certified roots** — and `exact_value.rs:189` `AlgebraicRoot`, which refuses
construction unless its isolating interval provably contains exactly one root. *Root isolation is
already exact here; root solving by chart transport is not built.*

**Owed, and it is a well-posed construction rather than a research question:** a Tschirnhaus organ.
Take a degree-5 input, transport it to Bring form by an exact rational chart change, return the
transported form **and the transport**, and refuse — with the obstruction named — when the target
chart cannot represent the answer. That is `FOUND`/`RIDE`/`OPEN` on a polynomial, and every piece of
the exact substrate it needs already exists.

### 3.6 Fermat's Last Theorem, and why it is the same species as integral Hodge

His intuitions, verbatim:

> *"solving algebraically is akin to a wormhole in holonics"*

> *"Dark matter is purely like the wormhole, explicitly a curved path. Is the fractal dimension like
> pi's C/d? This has something to do with FLT still."*

Two standard facts make the curvature intuition exact:

- The Fermat curve `xⁿ + yⁿ = zⁿ` is a smooth plane curve of degree `n` and therefore has **genus
  `(n−1)(n−2)/2`**. For `n = 3` the genus is 1 — an elliptic curve, flat. For `n ≥ 4` the genus is
  `≥ 3`, so `χ = 2 − 2g < 0`: **hyperbolic**.
- **Faltings (1983, the Mordell conjecture)**: a curve of genus > 1 over a number field has only
  **finitely many** rational points.

So *"a curved path"* is not loose talk: the difficulty of FLT switches on exactly when the curve's
Euler characteristic goes negative, and the first general theorem about it is a theorem about that
curvature. Faltings gives finiteness, not emptiness; Wiles closes the gap by a different route
entirely — modularity of semistable elliptic curves, via Frey's curve and Ribet's theorem.

**And the deeper alignment, which this project should carry:**

`xⁿ + yⁿ = zⁿ` has abundant **real** solutions and abundant **rational** ones on the projective
curve's complex points. What fails is the **integral** section. FLT is not "no solutions" — it is
*the solutions exist over the larger ring and not over `ℤ`*.

That is the **same species** as the failure of the *integral* Hodge conjecture, which `CLAUDE.md` §3
records: a class supported over `ℚ` and unsupported over `ℤ`, with the obstruction living in the
**cokernel of the cycle class map**. And this repository already models that species by name:
`ObstructionSpecies::ReachableOnlyInMultiple { factor }`, `supported_realizers.rs:108` — and the
grown circuit produced an instance of it, `factor: 2`, with the generator exhibited.

**Stated carefully, because it is easy to overclaim:** FLT and integral Hodge are not the same
theorem and neither is claimed. They are the same *question shape* — **does a solution that exists
over a larger ring descend to the integers** — and this machine's obstruction vocabulary was built
for exactly that shape. That is a construction-selection principle, in the sense of §2, and nothing
more.

### 3.7 Localized P=NP

> *"It is P=NP locally, where the chain walks everything locally!"*

> *"uses "is this solvable, and at what cost" in order to infer about the *combinatorics*."*

The precise reading in the machine's own vocabulary, and it is already half-written in `CLAUDE.md` §2:

P vs NP is the gap between **verifying** and **finding**. RIDE is verification against standing;
FOUND is search that pays curvature. `CLAUDE.md` §2, assistant prose: *"FOUND pays curvature; RIDE is
cheap because the terrain already paid."* **Localized P=NP is the statement that on standing terrain,
finding costs what verifying costs — because the terrain already did the finding.**

Prime founding is the worked instance the contract already names: verifying a factorization is one
multiplication; finding it is the hard direction. But *below the square-root frontier the transport
population is finite and exhaustible*, so locally the two costs meet, and exhaustion — not a
certificate — is what FOUNDs a new axis.

**Owed:** the machine currently has no organ that returns *"is this solvable, and at what cost"* as a
typed answer. §8's cost discipline and today's Smith-reduction finding are the same demand arriving
from the other side: a cost that is measured in **work** and not in elapsed time. `PivotSchedule`
returns the pivot count and it is provably **not** the dominating quantity; the dominating quantity
is intermediate entry bit-length and nothing counts it. Until a work vector exists, no cost question
in this repository has a lawful answer.

---

## 4. Sections not yet written

Named here so their absence is legible rather than silent, per §7 and §8.

- **Coordinate systems as receiver declarations** — Cartesian, polar, complex, cylindrical,
  spherical, projective, homogeneous, **barycentric**, **trilinear**, affine, phase, configuration,
  latent/embedding, tangent bundles, UV. The claim to make: a coordinate system is a *receiver*, not
  a property of the space, and the Jacobian is the transport.
- **Curvature as the link between discrete linearity and wave dynamics** — the deficit angle, the
  cycle spectrum's star-polygon windings (§2b, and `winding_inertia.rs`), and the refusal deposited
  2026-08-08: the lineage torsion is **not** a deficit angle, and the two organs read disjoint data.
- **Polygons, n-grams, capacitance** — Brandon: *"you cannot have a polygon without its implicit
  n-grams."* The measured anchor exists: `C_n`'s eigenvalues `2cos(2πk/n)` are one per star polygon
  `{n/k}`, and the sign of each is the winding past the quarter turn.
- **Knot / String / M** — point → line → loop → string → sheet → volume. The skein relation is
  already an owner (`skein.rs`), and `derivation_skein.rs` returns 18/58 classes at `2·c`.
- **Hodge and holomorphic spaces** — flagged by Brandon as neglected. Partly discharged 2026-08-08 by
  `matroid_chow.rs` (Hodge–Riemann on a matroid representable over no field) and by §2/§3 of the
  contract; the holomorphic half is not written.
- **Weave: warp and weft** — *"Which axes are warp vs weft relative to what?"* Collection in progress.
- **Illicium** — *"the illicium is itself the frame… the arrow of time, the arrow of entropy, in the
  active system."* Collection in progress.
- **Friction** — *"'Good' intuition feels smooth; brains can objectively feel when patterns are not
  quite clicking together."* Collection in progress. The candidate identification is friction = the
  retained residual of a gluing that did not close, which already has an owner in
  `running_integral::ChordObstruction`.
- **Ant integration** — *"parallel sense I/O streams."* Collection in progress.
- **MorphoHDL and grown circuitry** — partly discharged: `grown_cell.rs` grows by exhaustion of
  material with no counter, and §3 of this tablet's cost finding came out of it.
- **Rendering coupled to perspective receivers.**
