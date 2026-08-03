# THE ARRANGEMENT PRECEDES THE ADDRESS; THE RETURN CHANGES THE NEXT RECEIVER

**Date:** 2026-07-26  
**Status:** BRANDON-RATIFIED PLAN / COMPLETED CONSTRUCTION / LEGACY
RESOLUTION-FIRST OWNER REMOVED / CONTINUOUS HETEROGENEOUS RECEIVER /
NATIVE CONICS MIGRATED / EXACT AREA QUOTIENT / COMPRESSED RETURN GENERATORS /
RETURNED CONTROL ENACTED / EXACT CURRENT + ACTION LAW / DETERMINISTIC
MULTICORE / DEVICE PARITY GATE / PLATFORM MEMBRANE / NO FLOATS / NO BEVY

## 1. Completed causal path

The one compiled path in `crates/holonic-engine` is now

\[
K_t
\xrightarrow{\Pi_{\rho_i,\Lambda_t}}
\mathcal A_i(t)
\xrightarrow{\{R_i(e_i)\}}
\mathcal A_B(t)
\xrightarrow{Q_{W,H,B}}
M_t
\xrightarrow{\tau_W}
D_t .
\]

- \(K_t\) is caused geometry in its local frames.
- \(\Pi_{\rho_i,\Lambda_t}\) is receiver \(i\)'s exact local ray law and
  transported frame relation.
- \(\mathcal A_i(t)\) is a continuous projective arrangement.
- \(R_i(e_i)\) is the caused standing relation founded by source event \(e_i\)
  from receiver face \(i\) into bounded presentation \(B\).
- \(\mathcal A_B(t)\) is the recomputed plural arrangement.
- \(Q_{W,H,B}\) is the terminal finite-area quotient.
- \(M_t\) retains every supported contribution per finite member.
- \(\tau_W\) is an explicit outer world transducer into a platform carrier.

Width and height first occur in \(Q_{W,H,B}\). They do not enter \(K_t\),
\(\Pi\), \(\mathcal A_i\), or \(\mathcal A_B\).

The following compiled public carriers were removed:

- `Aperture`;
- `ReceiverRasterSpec`;
- `PixelFiber`;
- `VisibilityReceipt`;
- `trace_receiver*`;
- resolution-first `trace_native_conics*`;
- pixel-atlas conversion helpers; and
- the receiver realization operations `EmitRay`, `TestTriangle`, and
  `AssembleCrossingFiber`.

The realization program now transports caused primitives and assembles one
continuous face.

## 2. Continuous heterogeneous arrangement

One `ReceiverFace` can carry together:

1. projective triangular sheets;
2. open or closed threads;
3. construction conics;
4. native hinge-caused conics; and
5. transported local coordinate foliations.

Each triangle or thread vertex retains its exact receiver-ray depth. Each
conic retains:

\[
X^\mathsf T Q X=0,
\qquad
d_\rho(X)
=
\frac{\ell_{\rm numerator}(X)}
     {\ell_{\rm denominator}(X)}.
\]

Under exact projective transport \(X'=MX\),

\[
Q'=M^{-\mathsf T}QM^{-1},
\qquad
\ell'=M^{-\mathsf T}\ell .
\]

Coordinate grids are not collections of drawn lines. A transported axis is
the complete family

\[
L(t)=L_0+tL_1.
\]

Arrangement relations retain exact line/line crossings, exact
line/conic roots and multiplicities, coincident relations, and the complete
implicit pencil for conic/conic intersections. A singular projection becomes
a typed seam, never a sample or epsilon.

## 3. Terminal finite-area quotient

For address \(a=(c,r)\), `TerminalMatrixSpec` derives one exact rectangle
\(C_a\). It never asks what the rectangle's center ray sees.

Linear and polygonal support is decided by exact incidence. For a conic
\(f(x,y)=0\), support on \(C_a\) is decided from the exact range of \(f\).
A quadratic reaches its extrema on a rectangle at:

- a corner;
- a stationary point on one of the four edges; or
- an interior stationary point.

Every candidate is rational when the quadratic and cell are rational.
Therefore

\[
C_a\cap\{f=0\}\ne\varnothing
\quad\Longleftrightarrow\quad
\min_{C_a}f\le 0\le\max_{C_a}f
\]

is decided without floating point, center sampling, tessellation, or
tolerance.

## 4. Returned control is later causality

Pointer devices return ordered integer counts. For a current presentation
point \(p\) and its integer-count successor \(p'\), receiver \(i\) receives:

\[
u=R_i^{-1}(p),
\qquad
u'=R_i^{-1}(p').
\]

This is a projective pullback, not a globally linear screen displacement.
Basis motion, Cayley precession, selection, and degree shifts are typed
consequences.

`ReceiverControlLaw` commits them into carried standing.
`apply_receiver_control` changes the next `ReceiverFaceSpec` before its
arrangement is formed. The older mistake—moving a ray law while retaining a
stale already-projected face—is therefore impossible on this path.

`CoupledControlLaw` admits a source-declared joint receiver/hinge event:

\[
(\rho_t,H_t)
\xmapsto{e}
(\rho_{t+1},H_{t+1}).
\]

Both deeds are solved from the same predecessor and become visible together.
No hard-coded input policy decides that pointer motion is a hinge event.

## 5. Return topology is compressed at the event root

Enumerating every simple branch through a cyclic hinge graph was rejected.
For event root \(r\), the live law now forms one rooted transport tree \(T_r\).
Every non-tree relation \(e:u\to v\) emits one fundamental return generator:

\[
\gamma_e
=
T(r,u)\,e\,T(r,v)^{-1}.
\]

Its exact projective holonomy is

\[
P_{\gamma_e}
=
P_{T(r,v)}^{-1}
\circ P_e
\circ P_{T(r,u)}.
\]

The generator retains the two tree words, chord, entered/returned parameter,
holonomy class, and target gluing residual. Work is proportional to reached
vertices and relations; the law does not enumerate all simple paths.

Parallel incompatible arrivals refuse the affected target and expose a seam.
A chord returning to the event root remains a higher return constituent and
does not erase the root deed.

## 6. Physical laws

The bounded variational hinge law remains one declared physical realization:

\[
p_k=I(q_k-q_{k-1}),
\qquad
p_{k+1}=p_k-Kq_k+J_k,
\qquad
q_{k+1}=q_k+\frac{p_{k+1}}I .
\]

The generalized discrete current carrier now implements

\[
\partial J=S
\]

as exact incoming-minus-outgoing incidence at every node with declared units.
For a potential word \(v_0,\ldots,v_n\),

\[
\sum_{k=0}^{n-1}
\left(V(v_{k+1})-V(v_k)\right)
=V(v_n)-V(v_0).
\]

A closed word has zero sum. An open interval retains its endpoint difference
and `StoredCurrentInterval` carries unreturned current rather than pretending
instantaneous conservation. `DiscreteActionStress` carries

\[
\Sigma=\frac{A_{\rm after}-A_{\rm before}}{\Delta q}
\]

with exact deformation, units, and orientation.

## 7. Parallel and device execution

`CpuExecutor` realizes indexed antichains and restores canonical order.
Cross-receiver arrangement pairs and terminal area classifications use this
executor. Serial and four-worker logical outputs are exact.

`ExactDeviceExecutor` is the only device admission boundary. A candidate
Vulkan, CUDA, or other backend must return the exact same task cardinality and
exact values as `HostExactDevice`. `admit_device` refuses any mismatch.
No Vulkan implementation is silently admitted merely because Vulkan is
available; CPU remains authoritative until a real candidate closes parity.

`PlatformMembrane` carries raw integer events and completed `DisplayFace`
values. `MemoryPlatform` is the deterministic reference. A native window
adapter may be supplied later without gaining ownership of geometry,
physics, chronology, or exact standing.

## 8. Verification

The completed acceptance cell is:

- `cargo test -p holonic-engine --all-targets`: **36 passed / 0 failed**;
- `cargo clippy -p holonic-engine --all-targets --no-deps -- -D warnings`:
  **clean**;
- `exact_receiver`: **2 continuous primitives / 10 exact arrangement
  relations / 3,600 terminal members**;
- `native_conic_hinge`: **1 native conic / 3 exact arrangement relations**;
- `plural_receiver_presentation`: **2 continuous primitives / 800 terminal
  members / 1 returned control**;
- serial and four-worker arrangement and terminal outputs: **exact**;
- compiled legacy resolution-first symbols in `crates/holonic-engine`:
  **absent**; and
- `f32`, `f64`, floating-point literals, and circular-constant evaluation:
  **absent**.

This record completes the ratified engine plan. It does not schedule a native
window or a Vulkan implementation. Those are physical adapters which may be
admitted only when the present question requires them and exact parity is
actually demonstrated.
