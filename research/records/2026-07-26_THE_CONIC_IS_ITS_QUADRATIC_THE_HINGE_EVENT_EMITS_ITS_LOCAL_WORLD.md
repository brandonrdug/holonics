# THE CONIC IS ITS QUADRATIC; THE HINGE EVENT EMITS ITS LOCAL WORLD

**2026-07-26 · RATIFIED GRAPHICS/PHYSICS PLAN CONSTRUCTION / NATIVE EXACT
CONICS / ORIENTED SIMPLICIAL HINGES / CAUSED CONIC FAMILIES / FIRST DISCRETE
PHYSICAL LAW / DETERMINISTIC MULTICORE CONIC RECEIVER / 32 TESTS PASS /
SCOPED CLIPPY CLEAN / NO FLOAT / NO VULKAN / NO SOMA INTEGRATION**

## 1. Exact question and stopping condition

This construction asked whether the Round A categorical and exact-value
carrier could support one actual caused geometric world:

1. a conic is authoritative as an exact quadratic rather than a sampled or
   manually classified picture;
2. a receiver returns its complete exact root fiber;
3. one hinge change propagates only through declared local incidence;
4. the propagated change causes the conic rather than placing it beside the
   dynamics;
5. incompatible transport leaves an explicit seam;
6. one declared physical law accounts for carried and returned action; and
7. physical CPU parallelism cannot alter any logical result.

That stopping condition is now met at the bounded CPU reference grain.

## 2. Native conic law

`HomogeneousConic` carries

\[
a x^2+bxy+c y^2+d xw+e yw+f w^2=0
\]

as six exact rational coefficients. Its doubled symmetric matrix retains the
same zero locus and exposes exact determinant and discriminant.

The conic class is derived in the contemporary affine chart:

- nondegenerate negative discriminant gives a circle or ellipse face;
- zero gives a parabola face;
- positive gives a hyperbola face;
- zero matrix determinant with positive discriminant gives an intersecting
  real line pair; and
- the supported separated-axis factorization identifies a parallel real line
  pair.

Circle, ellipse, parabola, and hyperbola are chart-relative names.
Degeneracy is the stronger projective invariant. No `ConicSpecies` input is
accepted by this carrier.

Restricting the conic to an exact local line gives

\[
\alpha t^2+\beta t+\gamma=0.
\]

The returned `ConicLineRelation` is:

- no finite root;
- one rational linear root;
- one exact repeated tangent root;
- two rational quadratic roots;
- two Sturm-certified algebraic roots; or
- one typed coincident line fiber.

No decimal, tolerance, sampled polyline, or tessellation enters this solve.

## 3. Receiver-relative conic fibers

A `NativeConic` carries:

- its cell identity;
- founding source event;
- most recent changing event;
- local frame;
- two-dimensional chart inside that frame; and
- exact homogeneous form.

The receiver transports the chart and quadratic through the declared frame
path. A coplanar receiver ray returns its exact polynomial roots. A transverse
ray first closes its unique plane meeting and returns a conic contact only
when that point satisfies the quadratic exactly.

Each `ConicContact` retains:

- source and latest event;
- exact ray parameter;
- multiplicity;
- oriented hand;
- forward/behind/origin/OPEN relation to the ray;
- and the exact affine local line which converts that root into the source
  conic point.

Contacts remain in canonical cell/root order. Pairwise depth order is recorded
separately because exact algebraic or series values need not yet form a total
order. `OPEN` is retained rather than replaced by an executor ordering.

## 4. Oriented simplicial complex

`SimplicialComplex` now owns caused vertices, oriented triangular faces,
derived oriented edges, cofaces, and hinges. A hinge may be founded only when
one edge has exactly two oppositely oriented cofaces.

A `HingeTransportNetwork` admits the exact projective re-base

\[
q_{\mathrm{target}}
=
\frac{a q_{\mathrm{source}}+b}
     {c q_{\mathrm{source}}+d},
\qquad ad-bc\ne0.
\]

The source and target hinges must share an incident face. Juxtaposed hinges do
not transport. The currently admitted dynamic network is a directed acyclic
local relation; a cycle is refused rather than being silently interpreted as
chronology.

One `HingeEvent`:

1. selects the reachable local relation from its pivot;
2. derives every candidate against the same predecessor;
3. closes agreeing candidates;
4. leaves disagreeing candidates as `ConflictingCandidates`;
5. leaves a projective pole as `UndefinedTransport`;
6. changes only closed hinges and their incident faces;
7. evaluates every dependent conic family from the resulting exact standing;
   and
8. commits the complete successor atomically.

Repeated incompatible paths therefore do not choose a winner or synthesize an
average.

## 5. The conic is an emitted consequence

`ConicFamilyLaw` assigns each of the quadratic's six coefficients an exact
affine form over selected hinge parameters. This is not a detached observer
calculation. It is part of the `HingeWorldLaw` successor.

The bounded cell carries

\[
x^2+y^2-(1+q_2)w^2=0
\]

where a declared identity turn carries \(q_1\) across their common middle
face to \(q_2\). The event

\[
q_1:0\longmapsto3
\]

therefore changes the conic from

\[
x^2+y^2=w^2
\]

to

\[
x^2+y^2=4w^2.
\]

Exactly the two reachable hinges and three incident faces change. A separate
hinge remains exact at zero.

## 6. First physical realization

`VariationalHingeLaw` supplies one narrow physical doctrine, not universal
physics. The source declares coordinate, event-step, action, momentum, and
impulse units together with exact inertia \(I\), stiffness \(K\), and boundary
impulse \(J_k\).

Its discrete action is

\[
L_d(q_{k-1},q_k)
=
\frac I2(q_k-q_{k-1})^2
-\frac K2q_k^2
+J_kq_k.
\]

The transition is carried as

\[
\begin{aligned}
p_k &= I(q_k-q_{k-1}),\\
p_{k+1} &= p_k-Kq_k+J_k,\\
q_{k+1} &= q_k+\frac{p_{k+1}}I.
\end{aligned}
\]

The returned receipt keeps internal impulse, external impulse, momentum
before, momentum after, declared units, and

\[
p_{k+1}-p_k-(-Kq_k)-J_k=0
\]

as an exact residual. In a free completed event, momentum returns exactly as
the invariant. At an unfinished boundary it remains the stored current
carried into the next event. An external impulse changes that current without
being mislabeled as loss.

This establishes temporal action balance for the declared law. It does not yet
establish a general closed spatial-cycle theorem, Kirchhoff law, field
equation, collision law, or continuum mechanics.

## 7. Deterministic CPU realization

`CpuExecutor` now has serial and explicitly bounded multicore realizations.
Multicore work is divided into local contiguous batches. Every returned member
is restored to canonical input-address order before becoming visible.

The execution receipt names:

- exact task count;
- requested worker limit;
- workers actually used;
- physical batches; and
- joins.

The same 51-member conic receiver aperture was realized serially and through
four CPU workers. The complete `NativeConicVisibilityReceipt` is exactly
equal. Only the CPU execution receipt differs.

This establishes deterministic multicore receiver-fiber realization. Hinge
event propagation itself remains serial and atomic at this cut.

## 8. Exact bounded observable

Command:

```text
cargo run -p holonic-engine --example native_conic_hinge
```

Observed complete relation:

```text
changed hinges: 1,2
changed faces: 1,2,3
changed conic: 1
left receiver before depths: 2,4
opposed receiver before depths: 2,4
left receiver after depths: 1,5
opposed receiver after depths: 1,5
source points before: (-1,0),(1,0)
source points after: (-2,0),(2,0)
```

The receivers use opposed ray directions. They therefore carry distinct local
traversal while closing the same intrinsic source-point sets.

## 9. Verification

```text
cargo test -p holonic-engine --all-targets --no-fail-fast
```

Result: 32 passed, 0 failed.

```text
cargo clippy -p holonic-engine --all-targets --no-deps -- -D warnings
```

Result: clean.

A source scan finds no `f32`, `f64`, or `Math.PI` carrier in
`crates/holonic-engine`.

Workspace-wide dependency clippy remains blocked by pre-existing warnings in
`relational-geometry`; those files were not changed by this construction.

## 10. Honest boundary

This construction does not yet provide:

- exact finite-area pixel-aperture classification for conic curves;
- receiver-derived coordinate-grid fields;
- a conic display transducer or interactive presentation;
- material, occlusion, lighting, or plural-fiber presentation doctrines;
- cyclic hinge holonomy dynamics;
- a general closed-cycle conservation theorem;
- multicore hinge-event solving;
- a backend-neutral device ABI;
- a Vulkan feasibility cell; or
- a direct GPU backend.

The old sampled `ProjectiveConic` in `relational-geometry` remains historical
support. It was not promoted into the new native conic authority.

Nothing in this completion schedules the presentation or GPU work by itself.
