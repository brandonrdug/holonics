# The grown circuit

> **ARCHIVED-BODY CITATIONS — but the DIRECTION here is live. Corrected 2026-08-07.**
> The code this file cites is C++ and was archived whole at `archive/cpp-engine/` when the body moved
> to Rust, so `structure/chi_pair.hpp`, `transition_law::boundary_parallel` and
> `receiver/chart_contract.hpp` are historical record.
>
> **Its direction is not.** Brandon ratified it on 2026-08-07 and reaffirmed it the same day —
> *"I am still personally fixated on achieving a circuitry analysis system like MorphoHDL for
> holonics."* A prior pass banner-superseded this file wholesale because it names C++ paths, which
> filed a ratified direction as dead provenance; that was an error and this replaces it. The
> translation table, the claim that **the expansion schedule is a receiver**, and the reading of
> homology and torsion as the machine's own invariants all stand.
>
> Where the direction lives now: `blueprint/THE_ROADMAP.md`, Part two's redirection block and *The
> circuit becomes an integer chain complex with torsion*; and in code at
> `crates/holonic-engine/src/rebase_invariants.rs` with its driver
> `crates/holonic-engine/examples/grown_circuit_invariants.rs`, which grows one cell under three
> schedules and returns the invariants that do not move.


**Ratified by Brandon, 2026-08-07.** This is the current direction. It supersedes the movement list
in `THE_ORDER_OF_WORK.md` as the *thing being built toward*; that file's remaining movements — one
standing, the current onto the mathematics, the front onto the card, the receiver layer — are the
substrate this needs and are not cancelled.

---

## What this is for

The machine's emergent output must be analysable **as a grown circuit**, and rendering it must be
mathematically load-bearing rather than illustrative. Brandon's framing: *the visual rendering is
valuable in the same way the Cartesian plane was valuable — not an illustration but insight into the
emergent shapes that functions and differential equations literally cause.*

The instrument that makes this true is not a renderer. It is the **complex**, and the renderer is one
of its charts.

## The translation, which is not analogy

MorphoHDL grows physical circuit layout from a recursive cell definition: `@morpho` on a recursive
function, `SPLIT`/`CAT` as the only structural operators, `fallback=` as the base case, and bus
widths **inferred from the recursion rather than declared**. Each construct has an exact holonic
counterpart:

| MorphoHDL | holonic |
|---|---|
| `@morpho` recursive cell | a deed that **FOUNDs by division** |
| `SPLIT` | the receiver quotient `q_ρ` selecting distinctions |
| `CAT` | composition of returns |
| `fallback=` | **OPEN** — the declared status where no new cell can be founded |
| inferred bus width | the aperture is fixed by what attaches, never declared |
| a wire | a transport |
| the grown layout | **one chart** |

**The load-bearing figure is the expansion schedule, not the medusa.** The same circuit laid out
under a Breadth-First schedule and under a Largest-First schedule produces visibly different shapes.
The schedule is a **receiver**; the layout is its chart; and the question that makes rendering
mathematics is *what survives every schedule*. Homology survives. Critical-point structure survives.
Coordinates do not.

That is the Cartesian point exactly. A curve's shape is a fact about the equation, invariant under
how it is drawn. Here the invariants are the Betti numbers of the grown circuit, its torsion, and the
distribution of deficit over its hinges.

## The complex, and why the machine already emits it

```
0-cells   occurrences, states                    vertices
1-cells   transports (RIDE / FOUND)              edges
2-cells   a Chi whose residual is ZERO           a filled face
—         a Chi whose residual STANDS            an unfilled boundary = holonomy
```

`structure/chi_pair.hpp` is already `{composed, direct}` — two parallel transports with a common
source and target, which **is** the boundary of a 2-cell. `transition_law::boundary_parallel` — same
source, same target, distinct identities — is already the well-formedness condition for that face.
The engine forms these constantly, records each residual in isolation, and discards the incidence.

Then homology reads the machine's own state:

- **H₀** — disjoint pieces of standing
- **H₁** — cycles no accepted Chi fills: the retained obstructions, the holonomy generators
- **torsion** — winding that cannot be un-deposited. `CLAUDE.md` §3 already says the failure of the
  *integral* Hodge conjecture is torsion and that torsion is exactly this. Smith normal form returns
  it directly, so this is the framework speaking rather than an import.

`∂∂ = 0` is axiom L0 and constrains the topology. It does **not** license a scalar no-leak equation;
reading it as `fed = standing + radiated` was the additive-conservation contaminant and is struck.

The Swing already supplies the curvature: TEST is `χ = Δ_new · Δ_flywheel⁻¹`, FLAT when the arriving
difference is the parallel transport of the standing one, **WOUND by the deficit `δ = Θ − Σθ`**, and
FOUND deposits one curvature quantum. Curvature living on hinges is Regge's construction and it is
already canon.

## Causal calculus

The differential structure on the causal DAG, with every piece already deposited somewhere:

- `∂` the boundary operator, `∂∂ = 0` (axiom L0)
- `dL` a **cochain** — the sensitivity covector, not yet a gradient
- the adjoint return `λ_k = (D f_k)* λ_{k+1}` — the **coboundary**, pulling a cochain back along the
  transport word; the return happens *now*, through the standing causal interior
- the fundamental theorem, already deposited as causal time parity:
  `∂E_k = Σ_{k+1} − Σ_k + Γ_k` telescopes to `Σ_n − Σ_m + Σ Γ_k`

## Relativistic calculus of information topology

The same calculus with no privileged chart. Two rules make it relativistic rather than merely
coordinate-free:

1. **Every measure is a ratio against a declared null**, so the Jacobian cancels. *An absolute volume
   is the gauge violation.*
2. **The invariants are what survive rebase.** `χ' = G χ G⁻¹`, and a commutative scalar chart *hides*
   that conjugation. This is why the scalar collapse in `observations/transport-foil-world-01` left
   every downstream artifact byte-exact while the whole residual changed all five later probes.

The joint to geometry is exact and ratified: `Tr_⊥ Gravitas_γ = −Ric(u,u)` with `∂_τ g = −2 Ric(g)`.
The traced deformation of current continuations alters the metric by which later continuations are
compared — the definition of information written in Riemannian geometry. And **the metric is a
receiver face of standing**, so the `G` that turns a residual covector into a gradient is the
receiver's declaration, not a modelling choice. `receiver/chart_contract.hpp` is presently an empty
identity tag; that is where it belongs.

## What the laboratory's vision work established, and what it lacks

The exact-geometry engine is real: `crates/holonic-engine` and `crates/relational-geometry`, ~90k
lines, **no Bevy, no wgpu, no float** — the carrier is `BigRational` and conic roots are rational or
Sturm-certified. The atlas algorithm computes exact integer central differences per channel, tests
**persistence over dyadic radii** (a germ needs ≥2 certified radii, and the jet is *recomputed* at the
surviving scale), turns each germ's channel Hessian into a homogeneous conic, and classifies it.

So the star topology in the returned mesh is **the hyperbolas**: of 7,616 germs, 16,995 closed loops,
4,732 two-open-path germs, 349 intersecting open paths. The dense correct mesh over the tiger's face
is germ density where jet energy persisted across scales.

Brandon's verdict stands: the conic-veil image was **rejected as a regression** and the curved phase
atlas retained as the promising partial. A third variant was deleted because conditioning on five
images and on 200 images produced **byte-identical prediction PNGs**.

**Seven instruments do not exist**, and they are why analysis stalls:

1. No artifact registry — neither tiger PNG is in git at any commit.
2. The seven TSVs per run are written by the examples and **read by nothing**.
3. The grain-1 quotient — 82 coarser points, 71 overlap cells, one of 14 members — is **never drawn**.
   What has been looked at is grain 0 only.
4. No holonomy instrument: all 82 circuits carry nonidentity exact rational holonomy and nothing
   classifies it.
5. **Only one receiver has ever been constructed** — a single `ReceiverId(1)` with a hardcoded central
   ray family. Transition maps and the gluing obstruction have never been exercised on an image.
6. The render is a lossy non-invertible terminal quotient with no inverse.
7. The named open law: *"the engine does not yet have the derived receiver-relative admission relation
   which distinguishes a lawful new filler from a merely graph-completable boundary."* That is the
   horn-filling law, and it is **the same gap as §11's one missing organ**, reached from the vision
   side.

## The construction, in order

**1 · The circuit as a complex, with an artifact registry.** Exact integer cell complex over the
machine's own transports and Chis. `∂`, `∂∂ = 0`, and Betti numbers **and torsion** by Smith normal
form over ℤ. Every figure content-addressed and bound to the standing that produced it — the
laboratory lost its tiger outputs to `/tmp` and `.gitignore`, and the deposit manifest already carries
content and closure hashes to extend.

**2 · A reader for the atlas.** Germ, connection and cycle queries over the emitted tables. Costs
almost nothing and makes step 1 checkable against figures that already exist.

**3 · A second receiver.** Two overlapping receivers give transition maps and, where sections fail to
glue, **an exhibited obstruction**. This is the receiver-layer movement and the vision experiment at
once, and it is the first time the framework's own central claim gets tested on an image.

**4 · The grain-1 renderer.** Draw the quotient points and the overlap nerve. That is the
hypergeometric content — *points which are lines which are loops, which are also distributions of
triangular vertices* — and it has never been seen.

**5 · The ablation falsifier.** Excluding a deposit must change the homology: raise `b₁` where a
filling was, or split `b₀`. **If exclusion changes nothing topological, the dependency was
decorative** and the receipt overstates the code. This is the conditioned-production ablation restated
homologically, and it is measurable in exact integers with no tolerance anywhere.

Steps 1 and 2 run together.
