# THE FACE PRECEDES THE MATRIX; THE FIRST RETURN CARRIES ITS HOLONOMY

**Date:** 2026-07-26  
**Status:** BRANDON-RATIFIED CONSTRUCTION / BUILT / EXACT CPU REFERENCE /
CYCLIC HINGE RETURN / PLURAL RECEIVER ASSEMBLY / FINITE PRESENTATION QUOTIENT /
EXACT INPUT RETURN / NO FLOATS / NO VULKAN / NO WINDOW

**Supersession:** This bounded intermediate record is retained as construction
history. Its compiled resolution-first compatibility paths, branch-enumerated
cycle law, center-sampled quotient, and open-work list are superseded by
`2026-07-26_THE_ARRANGEMENT_PRECEDES_THE_ADDRESS_THE_RETURN_CHANGES_THE_NEXT_RECEIVER.md`.
They are not current architecture or a scheduled queue.

## 1. The correction

“Finite-area pixel aperture” was the wrong causal order. It allowed an outer
display carrier to become the thing the receiver supposedly observed.

A receiver instead has one continuous exact local face. Its caused surfaces
are transported into its own chart. Multiple receivers may have different
face extents and aspect ratios. A bounded presentation relates those
independent faces. Only after that relation exists may a finite output matrix
ask what is present at its addresses:

\[
K_t
\xrightarrow{\Pi_{\rho_i,\Lambda_t}}
S_i(t),
\qquad
\mathcal P_t
=
\operatorname{Assemble}_{B,\Lambda_t}
\left\{(\psi_i)_*S_i(t)\right\}_{i\in I_B},
\qquad
Q_{W,H}(\mathcal P_t).
\]

Here:

- \(K_t\) is the caused contemporary construction;
- \(S_i(t)\) is receiver \(i\)'s exact local face;
- \(\psi_i\) is a declared invertible exact relation from that face into the
  bounded presentation;
- \(I_B\) is only the active receiver population inside boundary \(B\); and
- \(Q_{W,H}\) is the finite presentation quotient imposed by the output
  carrier.

The matrix addresses are not world cells. A member of \(Q_{W,H}\) may receive
zero, one, or many independent receiver contributions. Those contributions
remain plural until an explicit outer world law interprets them.

## 2. The cyclic correction

The preceding hinge network rejected any relation which completed a directed
cycle. That removed the very return required to carry winding and holonomy.

The corrected network admits a directed local cycle. During one event, each
causally distinct branch is followed only until its **first return** to a hinge
already present in that branch. This makes the passage finite without
serializing false instants or erasing the return.

For one first-return word

\[
\gamma=(r_1,\ldots,r_n),
\qquad
T_\gamma=T_{r_n}\circ\cdots\circ T_{r_1},
\qquad
q_i \xmapsto{T_{r_i}} q_{i+1},
\]

the successor carries:

1. the ordered relation word \(\gamma\);
2. the entered and returned hinge parameters;
3. the exact composed projective turn \(T_\gamma\);
4. one of three typed faces:
   - **projective gauge:** \(T_\gamma\) is a nonzero scalar multiple of the
     identity;
   - **fixed-point holonomy:** \(T_\gamma\) is nonidentity while
     \(T_\gamma(q_0)=q_0\);
   - **displaced holonomy:** \(T_\gamma(q_0)\ne q_0\);
5. the directed differences
   \(\Delta q_i=q_{i+1}-q_i\); and
6. the exact telescoping balance

\[
\sum_i \Delta q_i
=q_{\mathrm{return}}-q_{\mathrm{entered}},
\qquad
\varepsilon_\gamma
=\sum_i\Delta q_i
 -(q_{\mathrm{return}}-q_{\mathrm{entered}})
=0.
\]

This balance is an exact transport identity. It is **not** installed as a
universal physical voltage law. A physical realization must still supply
units, constitutive current, sources, sinks, and its selected conservation
doctrine. Nontrivial projective holonomy can survive even when the scalar
coordinate closes and the telescoping boundary sum is zero.

## 3. Construction

### 3.1 Continuous receiver face

`crates/holonic-engine/src/receiver.rs` now contains:

- `ReceiverFaceExtent`, with exact rational horizontal and vertical spans and
  no resolution;
- `ReceiverFaceSpec`, containing the participating receiver and its exact ray
  family;
- `ReceiverSurface`, a caused triangle transported completely into that
  receiver's chart;
- `ReceiverFace`, the contemporary surface population and receiver-local ray
  law before presentation; and
- `FaceFiber`, produced only when an exact local coordinate is actually
  received.

`receive_face` and `receive_face_entities` are the face-first entry points.
The older `Aperture`/`trace_receiver` API remains only as a bounded
single-receiver instrument used by earlier exact conic and realization
evidence. It is not the owner of plural presentation.

### 3.2 Plural bounded assembly

`crates/holonic-engine/src/presentation.rs` contains:

- `ExactFaceMap`, an invertible rational affine relation with exact push and
  pull;
- `ReceiverFacePlacement`;
- `PluralReceiverAssembly`, which requires the receiver-face population and
  placement population to agree exactly;
- `PresentationResolution`, the outer \(W\times H\) constraint;
- `PresentationMember`, retaining all receiver contributions at one address;
- `PresentationMatrix`; and
- `quotient_presentation`, which may realize independent matrix addresses
  serially or on a bounded CPU worker population without changing canonical
  result order.

No receiver contribution is selected, blended, occluded, or colored by this
path. `display.rs` now accepts only the completed plural
`PresentationMatrix`; its transducer is explicitly an outer world doctrine.

### 3.3 Exact return through the same relation

`return_presentation_input` carries four typed deeds:

- a receiver-local basis step with source-supplied exact step size;
- raw integer pointer displacement;
- selection of one finite presentation address; and
- an integer degree shift over a named scale target.

For display resolution \(W\times H\), raw pointer counts
\((\Delta x,\Delta y)\) first become the exact presentation displacement

\[
\delta_D
=
\left(
\frac{\Delta x}{W},
-\frac{\Delta y}{H}
\right).
\]

If \(M_i\) is the linear part of receiver \(i\)'s placement, the returned
receiver-local deed is

\[
\delta_i=M_i^{-1}\delta_D.
\]

No floating-point device coordinate enters the geometry. A selection returns
every receiver contribution present at the selected address. A degree shift
does not pretend to be geometric zoom; its selected world may interpret it as
grain, degree horizon, lineage depth, neighborhood, or constituent scale.

## 4. Exact bounded witness

`examples/plural_receiver_presentation.rs` constructs one caused triangle and
receives it through:

- a square central receiver face; and
- an independently wide parallel receiver face.

Exact maps place both faces in one bounded presentation. A \(5\times3\)
finite quotient returns:

- 15 finite addresses;
- 30 receiver-membership tests;
- 30 received local rays;
- 30 exact triangle-incidence tests;
- 14 exact crossings; and
- two independent contributions at the center address.

With four CPU workers, the returned matrix is exactly the same as the serial
matrix. A raw integer mouse displacement of \((1,-1)\) returns to the wide
receiver as the exact local displacement

\[
\left(\frac35,\frac13\right).
\]

The cycle witness uses three locally adjacent tetrahedral hinges with the
translation \(q\mapsto q+1\). One event enters at \(q=2\), transports
\(2\to3\to4\to5\), and returns:

\[
\gamma=(r_1,r_2,r_3),\qquad
T_\gamma(q)=q+3,\qquad
\sum\Delta q=3,\qquad
q_{\rm return}-q_{\rm entered}=3,\qquad
\varepsilon_\gamma=0.
\]

It is typed as displaced holonomy. The event's local hinge assignments remain
\((2,3,4)\); the first return becomes one higher cycle constituent in the
successor standing and is also radiated outward, rather than being reapplied
indefinitely.

## 5. Verification

On the named source:

- `cargo test -p holonic-engine --all-targets` passes;
- `cargo clippy -p holonic-engine --all-targets --no-deps -- -D warnings`
  passes;
- the plural receiver example runs successfully on four CPU workers; and
- no `f32`, `f64`, `Math.PI`, or floating-point literal enters
  `crates/holonic-engine`.

## 6. Honest scope

This construction establishes the causal order:

\[
\text{caused world}
\longrightarrow
\text{independent receiver faces}
\longrightarrow
\text{bounded plural assembly}
\longrightarrow
\text{finite presentation quotient},
\]

and the exact return of bounded input through the same face relation.

It does **not** yet establish:

- one heterogeneous receiver face containing the native conic carrier beside
  transported triangle surfaces; native conics remain exact but their older
  visibility receipt is still resolution-first;
- clipping and exact finite-address classification of a continuous conic
  receiver face;
- a world law which turns returned receiver input into hinge, receiver, or
  source events;
- a general physical constitutive law for cyclic current, stored tension,
  sources, sinks, or energy;
- simultaneous solution of mutually coupled hinge events;
- a window, platform device membrane, or Vulkan executor; or
- any claim that finite presentation is the world itself.

Those statements delimit this build. They do not schedule a successor.
