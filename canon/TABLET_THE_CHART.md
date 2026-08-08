# The chart: coordinates, transport, and what a chart refuses

> **Part of the mathematics tablet.** The spine, the quotation convention, the reading
> rule, and the law this file's sections instance are in `canon/THE_MATHEMATICS_TABLET.md`.
> Read that first; this file is one mechanism of it and is governed by it.

A coordinate system is a receiver and the Jacobian is the transport; a radical is a chart that forgets a winding; warp and weft are a reading in a frame.

---

## 10. A coordinate system is a receiver, and the Jacobian is the transport

**Truth status:** `implemented-exact` for every owner named, each opened before being cited;
`proved-standard` for the classical identities; `interpretation` for the governing claim, which is
this project's and is stated so it can be refused.

**The claim.** A coordinate system is not a property of a space. It is a declaration made by
something that *reads* the space, and a chart change is the pullback of that reading — the Jacobian
— and nothing else. The repository asserts this in its type layout rather than in prose, which is
what makes it checkable. `crates/relational-geometry/src/model.rs:38`, at the definition of
`LocalChart`:

> The chart is not an ambient coordinate system. Its origin and ordered basis vectors state how
> local components are embodied inside this frame. A receiver can compare it with another chart only
> through declared frame relations.

### 10.1 The two halves are two types, and the separation is the content

What a **frame** carries is `LocalChart { origin, basis: [RatVec3; 3], labels }`
(`model.rs:45`) — an origin and an ordered basis, exact over `BigRational`, with `gram()` and
`orientation()` derived rather than stored. What a **reader** carries is
`Receiver { frame, orientation, projection, gauge, route_overrides }`
(`crates/relational-geometry/src/projection.rs:380`). Nothing in a `Construction` is written in a
coordinate system; a coordinate exists only once a receiver has been applied. Two charts become
comparable exactly when a `FrameRelation` (`model.rs:143`) declares an exact `AffineMap3` between
them, and a comparison is refused when the relation graph admits more than one route and the caller
supplied no `route_overrides`. **A chart with no declared relation to another chart is not wrong; it
is incomparable, and the type says so.**

### 10.2 The Jacobian, exactly, and the one arm it drops

`projection_pullback_gram` (`projection.rs:853`) is the load-bearing function and it computes the
Jacobian by hand. For `PerspectiveRay { focal_distance: f }` — the map
`(x, y, z) ↦ (fx/(f+z), fy/(f+z))` — it builds

```text
row_x = ( f/(f+z) ,   0     , −f·x/(f+z)² )
row_y = (   0     , f/(f+z) , −f·y/(f+z)² )
```

which are exactly `∂/∂(x,y,z)` of the two output components, and for `StereographicNorth` —
`(x,y,z) ↦ (x/(1−z), y/(1−z))` — the rows are exactly that map's partials. `gram_from_rows` then
returns `JᵀJ`. `receiver_metric` (`projection.rs:827`) conjugates it by the receiver's orientation
and divides by the gauge's own reference length, so **the receiver measures its own declared
reference as one and no universal ruler exists anywhere in the path**. `Orthographic` and
`Isometric` are constant Grams — rank two and the `(2/3, −1/3)` Gram whose fiber is `span{(1,1,1)}`,
which is the exact statement of what an isometric projection deletes.

**What escapes is `JᵀJ` and not `J`.** `ReceiverMetric` (`projection.rs:469`) carries `pullback`,
`reference_squared` and `normalized`; the Jacobian itself is a local in `projection_pullback_gram`
and is dropped at return. `J` and `RJ` for any `R` in `O(2)` share a Gram, so the metric arm keeps
the magnitude and discards the hand — §1's shape exactly. The hand is not lost from the *body*: it
is retained in a different return, as `sign(det(basis))` in `LocalChart::orientation()` and as
`TriangleFaceSignature::parity` (`projection.rs:483`). But **the two arms of one transport live in
two returns rather than in one carrier**, and §1's test — does any consumer read the carrier's
support as a relation rather than as a domain — is the one to apply if a future consumer needs both
at once.

### 10.3 The named systems, and who owns each

| system | owner, or the absence | note |
|---|---|---|
| Cartesian / affine | `LocalChart`, `AffineMap3` (`exact.rs`), `FrameRelation.forward` | affine is the *only* frame-to-frame law; there is no linear-only path |
| polar | `rational_circle` (`exact.rs:540`), `ProjectiveRatio` (`projection.rs:60`) | §10.4 |
| complex | `ExactComplexAxisPair` (`dimensional_receiver.rs:84`), `ExactTurn` (`decorated_path.rs:102`) | §10.5 |
| projective / homogeneous | `ProjectivePoint2`, `HomogeneousConic`, `primitive_projective` (`projection.rs:33`) | every homogeneous carrier is reduced to a primitive integer tuple at construction |
| barycentric | `SurfaceCrossing::barycentric: [Rat; 3]` (`holonic-engine/src/receiver.rs:658`) | §10.6 |
| tangent | `AnalyticGeometry::tangent` (`analytic_field.rs:239`) and `tangent_dimension_at_homogeneous_origin` (`algebraic.rs:1032`) | two owners and two different objects — a curve's tangent vector and a cone's Zariski tangent dimension; there is no tangent **bundle** anywhere |
| phase | `arithmetic_phase.rs`, `receiver_phase_atlas.rs`, and the physical phase triple in `examples/desktop_receiver.rs:49` | three unrelated senses of "phase", none of them a symplectic phase space |
| configuration | `basin.rs:28` `ConfigurationCellId` | a bounded exact **complex**, and the module refuses the continuous case by name |
| **cylindrical, spherical** | **no owner.** `git grep -i cylindrical` over `crates/` and `soma/` returns zero; every `spherical` hit is `AtmosphericAltitude*` or a test string | neither is needed by anything built, and inventing one would be cabinet-filling (§9) |
| **trilinear** | **no owner, and zero occurrences in the entire repository** | the natural next chart after barycentric, and genuinely absent |
| **UV / texture** | **no owner.** `uv_` returns zero; `texture` occurs only in the test helper `textured_section` | nothing here parameterizes a surface for sampling, because nothing samples |
| **latent / embedding** | **no owner, and the absence is a declaration.** `latent` names a reconstructed *divisor generator* (`divisor_reconstruction.rs:40`), not a learned vector; the ML sense is refused in source at `soma/life/src/agentic_language.rs:201` and `:436` | the honest replacement is the Nerode quotient of `receiver_exact_compression.rs`, which is a partition with an exhibitable separating word rather than a space with a distance |

### 10.4 The polar chart, and where the half-turn went

`rational_circle(t)` returns `((1−t²)/(1+t²), 2t/(1+t²))` — the Weierstrass tangent half-angle
substitution, `t = tan(θ/2)` — so `cayley_rotation_{x,y,z}` are exact rational rotations with no
transcendental anywhere (`proved-standard`; this is the rational parametrization of the conic
`x²+y²=1`). `ProjectiveRatio::compose_same_axis` computes
`(n₁d₂ + d₁n₂) / (d₁d₂ − n₁n₂)`, which is the tangent addition formula: **angle addition is exact
rational arithmetic on the half-angle parameter.**

The affine half-angle chart misses exactly one point of the circle, `t = ∞`. That point is the
half-turn. And the carrier **restores exactly it**: `ProjectiveRatio::infinity()` is `1/0`, so
`ExactSpin::axis(X, 1/0)` is the quaternion `[0,1,0,0]`, and `ExactSpin::matrix` returns
`diag(1, −1, −1)` — rotation by `π` about `x`. `proved-derived`, two lines, checkable against
`ExactSpin::matrix` at `projection.rs:237`. **So the one point the rational chart cannot see in its
affine form is `−1 = e^{iπ}`, and the projective completion is exactly the repair.** That is §2b's
sentence arriving as a
property of a chart rather than as a reading: the half-turn is not a value the chart forgot, it is
the chart's own point at infinity.

### 10.5 The complex chart is a quarter turn, declared

`dimensional_receiver.rs:19`, at the module head: *"Exact complex coordinate pairs are represented as
two real receiver coordinates with the local quarter-turn `J(a,b)=(−b,a)`. Consequently `J²=−I` is
an exact chart relation rather than an 'imaginary' source object."* The control is named
`complex_pair_is_one_dimension_and_its_square_turn_is_negative_identity` (`:1621`), and a germ
carrying only one half of a declared pair is refused as `IncompleteComplexPair`.

`ExactTurn { parallel, transverse }` (`decorated_path.rs:102`) is the same object in the geometry
crate: `between(incoming, outgoing)` returns `(u·v, u×v)/|u|²` and `multiply` is
`(p₁p₂ − t₁t₂, p₁t₂ + t₁p₂)` — complex multiplication, exactly, with no modulus taken. A turn is
composed by multiplying, never by adding angles, so no `atan2` is ever needed and none exists in the
tree.

### 10.6 Barycentric is the chart with no origin, and that is why it survives projection

`ray_triangle_crossing` (`receiver.rs:2361`) is Möller–Trumbore over `Rat`: the determinant decides
degeneracy by exact zero rather than by tolerance, and the return carries
`barycentric: [1−u−v, u, v]` together with `orientation: sign(determinant)` — **both arms, in one
carrier**, which is the shape §10.2 found missing on the metric path. A barycentric coordinate names
a point by its relation to a simplex and to nothing else; it is the one chart in this table that
declares no origin, and it is the one the display path can consume without importing a frame
(`crates/holonic-engine/README.md:626`: color is derived by exact barycentric ratios of the
receiver's own phase triple into the monitor's RGB basis, *"RGB remains a display quotient, not a
universal physical spectrum"*).

```text
source geometry  ->  receiver map        ->  transport       ->  returned residual
a Construction       a Receiver's frame,     the exact Jacobian  the pullback Gram, the parity, and
of exact points      orientation, gauge      of ProjectionLaw    the horizon fibers of directions
and frame relations  and ProjectionLaw                           the finite chart cannot hold
```

---

## 3. Polynomial solving: the radical chart, and what it refuses

**This is the section the keywords converge on, and it is where a standard theorem says exactly what
Brandon has been saying.**

**Read the prior deposits before this section.** `research/records/2026-08-06_THE_CONSTRAINT_IS_THE_CHI_THE_UNKNOWN_IS_THE_MISSING_CHART.md`
already carries the Galois reading at `proved-standard`, names Klein's icosahedron, and states the
resolution shape as *"found a chart whose symmetry matches the obstruction, and the unknown becomes
determined."* `2026-07-17_THE_ARC_IS_THE_CONSTRUCTION...` carries Doyle–McMullen. This section
restates and extends them; it does not discover them, and I wrote a first draft as though it did.

**And the frame-relativity is Brandon's ruling, already persisted**, 2026-07-03:

> *"The FLT sense in particular is very important and I need solvability being frame-relative to be a
> persisted fact, I don't want to bother with winning that argument again."*

together with the harder one, 2026-07-08:

> *"you are not recognizing that the RH and FLT are plagued by absolute frames, they are malformed
> like absolute P vs NP or AGI as notions."*

So §3.4 below is not an acceleration offered to him. It is his ruling, with the citations attached.

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

- **Doyle–McMullen**: a *generally convergent purely iterative* solution. A degree-11 rational map
  is canonically associated with the icosahedron's 12 vertices, its symmetry realises `A_5` as Möbius
  transformations, and a full-measure population of initial points converges to the 20 dual
  dodecahedral vertices, from which a root is recovered. Already carried at
  `research/records/2026-07-17_THE_ARC_IS_THE_CONSTRUCTION_THE_SPECTRUM_IS_ITS_RECEIVER_FACE.md:195-226`.

```text
radical chart        ->  REFUSES at degree 5, and the obstruction has a name: A_5 is simple
hypergeometric chart ->  RETURNS, as a series in the coefficients
elliptic modular     ->  RETURNS, as a theta quotient
icosahedral dynamics ->  RETURNS, as the limit of an exactly-constructed iteration
```

**And `A_5` being the obstruction is not decoration — it is the icosahedron's rotation group.** The
chart that resolves the quintic is the chart whose symmetry *is* the obstruction. That is the
sentence the 2026-08-06 record already deposited, and it is the cleanest instance in the whole tablet
of *"the unknown is a missing dimensional pathway."*

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

**The obstruction organ is BUILT and driven, and this section's first draft missed it.**
`crates/holonic-engine/src/arithmetic_monodromy.rs` (1,748 lines) carries
`QuinticTransitiveGroup::{Cyclic5, Dihedral5, Frobenius20, Alternating5, Symmetric5}` — the five
transitive subgroups of `S_5` — with the predicate in code:

```rust
pub fn solvable_by_radicals(self) -> bool {
    matches!(self, Self::Cyclic5 | Self::Dihedral5 | Self::Frobenius20)
}
```

plus exact monic normalisation preserving the splitting field, discriminants by Sylvester resultant
through a **fraction-free Bareiss determinant** over `BigInt`, and a declared refusal: *"absence of an
unobserved cycle type never excludes a group."* Driven by
`examples/arithmetic_monodromy_ecology.rs`. So the machine already **computes the obstruction**; what
it does not do is **transport to the chart the obstruction names**.

Root isolation is likewise exact — `exact_value.rs:189` `AlgebraicRoot` refuses construction unless
its Sturm certificate proves exactly one root in the interval, and `implicit.rs:719` returns a full
certified real-root population at a declared **quartic** aperture. *Root isolation and obstruction
detection are built; root solving by chart transport is not.*

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

## 4. The weave: warp and weft are a reading in a frame

**Truth status:** `established-bounded` for the laboratory's statement of the law; `measured` for the
implementation gap. The governing sentence is a laboratory deposit, not this session's invention.

Brandon's question, which is the whole content:

> *"Can you make sure that your probing adheres to the Frame usage? Which axes are warp vs weft
> relative to *what*?"*

The laboratory answered it, and the answer is the same shape as §2b:

> Warp/weft is not a label a fibre carries; it is a **reading in a frame.** From a frame below it,
> lineage `X` is a **warp**. From a frame at `X`'s own level or above, the same `X` is a **weft**. So
> **every fibre is simultaneously warp-for-some and weft-for-others.** *"Is `X` warp or weft?"* is
> malformed; only *"warp or weft **from which frame**"* is well-posed.
> — `THE_FABRIC.md:19-25` at laboratory `a07ff376`

and the rule is explicit and quantitative: **a thread is warp iff its rank is above the frame's own
`ref_rank`, weft iff at or below** (`THEORY_AND_EQUATIONS.md:3957-3963`). The frame carries a turn
*and* a rank-level; shift the rank-level and the partition re-cuts.

**This is §2b's sentence for a different carrier.** There, the *split* is invariant and the *hand* is
a convention. Here, the *cloth* is invariant and the *partition into warp and weft* is a receiver
declaration. Same law, different material — which is §4 of the contract exactly.

### The defect, and it is today's defect again

**`ref_rank` has no implementation anywhere** — not at `a07ff376`, not at its parent, not here. The
only axis-tagging owner that ever existed, `pub enum Thread { Warp, Weft }` in a laboratory
encoder module deleted before `a07ff376`, **tagged each axis statically at construction**. Nothing re-partitions
under a frame change.

That is the same defect this session repaired in `ComparativeMultiplicity` and convicted in `§8`:

> **A receiver-relative reading, frozen into the carrier at construction time.** The law says the
> partition is a function of `(fibre, frame)`; the carrier stored it as a function of `fibre` alone.
> No downstream consumer can recover the frame-dependence, because the constructor discarded it.

The live canon states warp/weft (`canon/04_GEOMETRY_NAVIGATION_AND_WEAVE.md:67-73`) and **drops the
frame-relativity clause entirely** — the load-bearing half. That is a documentation regression to
repair, and the construction it implies is small: a warp/weft *reading* that takes a frame, rather
than a `Thread` field.

---
