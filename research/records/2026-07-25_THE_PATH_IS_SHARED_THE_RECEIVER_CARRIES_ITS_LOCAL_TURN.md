# THE PATH IS SHARED; THE RECEIVER CARRIES ITS LOCAL TURN

**Date:** 2026-07-25  
**Grade:** BRANDON-AUTHORIZED CONSTRUCTION / BUILT / EXACT JOINT DECORATED
PATH CARRIER / CO-PRESENT RECEIVER GRAIN / CLOSED TURN RETURN / NO FLOATING
POINT / NO BEVY CHANGE / NO SOMA INTERIOR CHANGE

## Scope

This construction is one continuation of the geometry-first programme, not a
new application or an isolated visualization feature. It asks how a causal
path can remain lawful while multiple internal perspectives present different
crossings and metrics.

The prior atlas separated source incidence from receiver planarization. It
left the useful carrier open. That carrier is now implemented without
guessing a scalar weight.

## The one carrier

The source supplies the ordered branches and actual junctions. The
co-present receiver family supplies a common exact subdivision: every source
parameter at which any receiver presents a regular crossing refines that
branch for the whole family. Each receiver evaluates every resulting
interval, while retaining only its own over/under and orientation marks.

Thus a path is neither the source graph alone nor a stack of unrelated
screens. It is one ordered source path decorated by the joint receiver face.
Apparent crossings never become causal switches.

The implementation is a free noncommutative path carrier:

\[
\operatorname{Path}(\mathcal T_{\mathcal J}),
\qquad
\mathcal T_{\mathcal J}
=
\{(d,d'):t(d)=o(d'),\ d'\ne\bar d\}.
\]

Its records retain source branch/order/frame/metric, common interval cuts,
receiver-local interval metrics and crossings, and exact local turn factors.
No determinant, norm, sum, probability, or loss scalar replaces those
fields.

## The first exact evaluation law

For two nonzero rational receiver chords \(v,w\), the local turn is

\[
\tau(v,w)
=
\left(
\frac{v\cdot w}{v\cdot v},
\frac{v\wedge w}{v\cdot v}
\right).
\]

Reading the pair in \(\mathbb Q(i)\), this is \(w/v\). Every closed lawful
path therefore has exact return

\[
\prod_j\tau(v_j,v_{j+1})=(1,0).
\]

That closure is conservation-like but deliberately insufficient: distinct
source geometries and receiver words share the same return. The ordered
interior is what preserves their difference.

## Bounded consequence

The initial precessed receiver presents \(AC\times BD\) at source parameters
\(21/47\) and \(36/47\). A direct receiver sees no crossing, but its \(AC\)
and \(BD\) chords are subdivided at those same parameters because both
receivers belong to one event grain.

After \(D_z:1\to1/4\), the crossing departs. The lawful source primitive
paths remain the same, while the source metric words, precessed turn words,
and common interval partitions change. Every closed turn return remains
\((1,0)\). The complete receipt is
`observations/joint-decorated-path-atlas-01/RESULTS.md`.

## Broader relation

This is the smallest implemented bridge presently shared by:

- receiver-relative mathematical graphics;
- knot diagrams, where crossings are presentation data over source strands;
- discrete transport, where local factors compose along actual incidence;
- algorithmic worlds, where source execution order cannot be replaced by a
  projected dependency picture; and
- a possible decorated zeta treatment, where primitive recurrence must carry
  arithmetic and Archimedean evaluation rather than remain an unweighted
  graph count.

It does not install a universal evaluation. A domain supplies the law which
reads the path decorations. For RH that law must still connect primitive
paths to Euler factors, the completed Archimedean carrier, and the required
positive form or spectral statement. The carrier now preserves enough
information for that question to be posed without conflating source loops
with receiver loops.

## Deposited objects

- `PAPERS/mathematics/definitions/joint-decorated-path-carrier.typ`
- `PAPERS/mathematics/theorems/exact-receiver-turn-return.typ`
- `crates/relational-geometry/src/decorated_path.rs`
- `crates/relational-geometry/examples/joint_decorated_path_atlas.rs`
- `observations/joint-decorated-path-atlas-01/RESULTS.md`
