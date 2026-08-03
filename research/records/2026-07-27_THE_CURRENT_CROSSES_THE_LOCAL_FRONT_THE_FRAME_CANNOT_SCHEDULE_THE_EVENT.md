# THE CURRENT CROSSES THE LOCAL FRONT; THE FRAME CANNOT SCHEDULE THE EVENT

**Date:** 2026-07-27  
**Status:** BUILT / COMPLETE EVENT-LOCAL PROPAGATION / LOCALLY PARALLEL
ANTICHAINS / EXACT AFFINE SOURCE REBASE / PRE-PROJECTION FACE CARRY /
TERMINAL TRACE CARRY / EXACT HOST ACCEPTED / NO GUI LAUNCH / NO CUDA RUN /
SOMA INTERIOR UNCHANGED

## Present question

The desktop physics path still exposed two coupled defects.

First, one local incidence was being mistaken for one physical event. Emitted
current entered `LocalStarStanding`, the outer display loop fabricated a
continuation event, and the complete construction, receiver faces, terminal
restriction, and display were rebuilt after that one incidence. A display
refresh had therefore become a false physical clock.

Second, a receiver tube could carry a literally identical source section but
could not carry the same section through a different exact inscription. A
source and its receiver rays could move together without changing the
receiver-relative face, yet the implementation still paid to project and
restrict it again.

The construction question was:

> Can one supplied world event propagate its exact current through every
> causally subsequent local incidence without display ticks, can co-present
> local solves execute concurrently without executor order becoming
> chronology, and can a proved geometric rebase carry a previously formed
> receiver face before projection?

The stopping condition was a production-path correction, exact rest/return/
open-cycle boundaries, serial/multicore equality, positive and negative rebase
acceptance, and headless verification. No desktop window or CUDA passage was
authorized.

## 1. The sparse current population is a causal frontier

Let \(B_j\) be the complete local-star standing at causal layer \(j\), and let

\[
I_j:H\longrightarrow\mathbb Q
\]

be the finite exact current vector over the contemporary hinge population.
Its active support is

\[
A_j=\{h\in H:I_j(h)\ne 0\}.
\]

The ordered map used to represent \(I_j\) is neither a frame buffer nor a
queue. It is one sparse exact vector at one causal cut. Contributions which
arrive at the same hinge in the same cut add before that hinge is solved.

For every \(h\in A_j\), the local law evaluates

\[
\lambda_h(B_j,I_j(h))
=
\left(
\Delta B_{j,h},
J_{j,h},
\varepsilon_{j,h}
\right).
\]

Every member of \(A_j\) reads the same predecessor \(B_j\). The members may
therefore be physically realized in parallel. Their canonically ordered merge
forms

\[
\left(B_{j+1},I_{j+1}\right)
=
\bigoplus_{h\in A_j}\lambda_h(B_j,I_j(h)).
\]

Only after that merge may \(I_{j+1}\) advance. Parallelism and causality are
therefore distinct:

- one antichain is co-present and physically parallelizable;
- successive antichains are causally ordered because the latter consumes the
  former's successor; and
- thread completion order cannot alter either order.

`CpuExecutionReceipt::ordered_antichains` records total work across the event
while retaining the greatest simultaneous worker population. The
`LocalCausalLayerReceipt` population preserves every individual antichain,
its active hinges, emitted frontier, and physical execution testimony.

## 2. One event closes its own local front

`LocalStarLaw::enact_frontier` now owns the complete propagation opened by one
external `LocalStarEvent`. Only the first layer receives that world deed.
Subsequent layers are internal factors of the same event; they are not
externally visible continuation events.

The front stops at one of three exact boundaries.

### Rest

\[
I_{j+1}=0.
\]

Nothing remains to conduct.

### Exact return

\[
B_{j+1}=B_m
\qquad\text{for some }m\le j.
\]

This is equality of the complete exact standing, not equality of a scalar
coordinate, hash, support set, or rendered face.

### Open cyclic support

Let \(N=|H|\). Every emitted current crosses one declared local incidence. If
nonzero current survives through \(N+1\) causal layers, an ancestry walk has
visited more hinge supports than exist, so at least one hinge support repeats.
This proves recurrent support by the pigeonhole principle; it does not pretend
that the complete physical state has returned.

The surviving current is committed as `open_frontier` under
`CyclicSupportOpen`. It remains an exact boundary for a genuinely later world
deed. A display clock may not manufacture that deed.

The former `pending_currents` name is removed. Intermediate fronts never
enter standing at all. Only a front which survives the complete event enters
the successor as `open_frontier`.

## 3. The display no longer drives physics

The rejected outer path performed:

\[
\text{one incidence}
\to
\text{fabricated continuation event}
\to
\text{full source sync}
\to
\text{receiver projection}
\to
\text{terminal restriction}
\to
\text{display}.
\]

That loop was the reason physical change appeared one frame at a time. It also
paid the most expensive observation work after every internal incidence.

The desktop now performs:

\[
\text{supplied world deed}
\to
\text{complete causal front}
\to
\text{one contemporary receiver assembly}
\to
\text{one changed tube restriction}
\to
\text{presentation}.
\]

A redraw presents the already-current outer quotient. It does not advance the
physical world. A resize changes the terminal boundary only. Neither operation
creates a `LocalStarEvent`.

This does not make local physics sequential. All active hinges in one layer
still execute through the multicore executor. It prevents an unsafe shared
mutation race: a hinge may respond to its co-present predecessor, but it may
not read another hinge's half-committed successor from the same antichain.

## 4. The exact affine folding boundary

Let a source ray family have center \(c\) and ordered exact basis

\[
B=[u\;v\;d],
\]

where \(d\) is the parallel direction or central forward carrier. Let the
candidate target ray family carry \(c'\) and

\[
B'=[u'\;v'\;d'].
\]

For matching ray species and nonsingular \(B\), the unique affine candidate is

\[
A=B'B^{-1},
\qquad
t=c'-Ac,
\qquad
\phi(x)=Ax+t.
\]

`RayFamily::exact_affine_rebase_to` derives this map with exact rational
arithmetic. `ReceiverSourceSection::exact_rebase_to` then verifies every
carrier against the same \(\phi\):

- frame and frame-relation populations remain exact;
- entity and conic identities remain exact;
- every triangle vertex and thread vertex maps through \(\phi\);
- conic centers translate and conic axes transform through \(A\);
- native conic event, frame, and constitutive form remain exact while its
  chart origin and axes co-transport; and
- the determinant hand records whether local orientation is preserved or
  reversed.

One failed constituent rejects the rebase. Visual resemblance, a hash, a
floating tolerance, or agreement at selected terminal addresses cannot admit
it.

When the proof succeeds, `TerminalTubeAtlas::carried_receiver_face` returns
the already-formed exact arrangement with the new ray family before source
projection. `ReceiverTubeChange::Rebased` then carries the existing terminal
trace as well. The receiver-relative face is invariant under the proved
co-transport; rebuilding it would add cost without adding information.

This closes the precise affine folding boundary named in
`THE SOURCE IS THE STAR; THE TUBE PRECEDES REPROJECTION`. A general
non-affine or kernel-specific far-field fold is not silently identified with
this theorem. It still owes its own exact transport law and, where a finite
series is used, an exact consequence certificate.

## 5. Acceptance

Headless acceptance after the correction:

- `cargo test -p holonic-engine --all-targets`:
  69 library tests pass; 4 desktop tests pass; 2 physical tests remain
  explicitly ignored;
- `cargo clippy -p holonic-engine --all-targets --no-deps -- -D warnings`:
  clean; and
- changed-path `git diff --check`: clean.

The new witnesses establish:

1. one source current crosses more than one local incidence and reaches exact
   rest in one supplied event;
2. a two-hinge recurrent transport returns one exact open cyclic boundary
   after the combinatorially derived horizon without a display tick or
   numerical tolerance;
3. serial and four-worker execution produce the identical complete standing
   and radiation across all causal layers;
4. a complete affine co-transport carries the receiver face and terminal
   trace without reprojection or retracing; and
5. perturbing one triangle vertex outside the common affine map refuses the
   carry.

No float, approximation, tolerance, frame-owned physics, GUI launch, or CUDA
run entered this construction.

## Result

The physical unit is now the caused event, not the rendered frame. Its current
is a sparse exact vector which branches across locally incident stars,
executes co-present members in parallel, and advances causally ordered
frontiers until it reaches an exact boundary. Presentation observes the
resulting contemporary cut; it does not schedule it.

The first nonliteral folding law is also closed. An exact affine transport
which carries the receiver rays and every admitted source constituent carries
the already-formed receiver face and its terminal restriction. Any
non-coherent constituent forces a fresh factorization.
