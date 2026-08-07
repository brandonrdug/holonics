# RECEIVER TOPOLOGY ATLAS 01

**Date:** 2026-07-25  
**Grade:** EXACT HOST CONSTRUCTION / SOURCE INCIDENCE TYPED APART FROM
PROJECTED INCIDENCE / EXACT ROTATION SYSTEM / FACE BOUNDARIES RECOVERED /
IHARA RECURRENCE COMPARED / NO FLOATING POINT / NO BEVY CHANGE / NO SOMA
INTERIOR CHANGE

## Question and stop

The question was whether the joint receiver construction supplies enough
information to distinguish:

1. recurrence belonging to declared source incidence;
2. recurrence created by one receiver's planar projection; and
3. a later source geometry which happens to present the same planar topology.

The stop was one exact three-cut comparison containing source incidence,
regular apparent crossings, every oriented face boundary, source and
receiver-dual Ihara polynomials, and primitive loop counts.

## Construction

The source is the tetrahedral incidence graph \(K_4\) carried by six declared
thread branches \(AB,AC,AD,BC,BD,CD\). Its initial vertices are

\[
A=(0,0,0),\quad
B=(4,0,0),\quad
C=(0,4,0),\quad
D=(1,1,1).
\]

Three cuts are compared:

- **A:** initial source, direct orthographic receiver;
- **B:** identical initial source, orthographic receiver precessed by exact
  Cayley parameters \((-1/2,-1/2,0)\);
- **C:** same precessed receiver after the sole source change
  \(D_z:1\to1/4\).

Every projected coordinate, intersection parameter, depth order, cyclic ray
order, face area, graph coefficient, and loop count is exact.

## Source change

The source incidence remains \(K_4\), but its geometry does not remain equal:

```text
oriented volume witness: 16 -> 4

AB squared: 16 -> 16
AC squared: 16 -> 16
AD squared: 3 -> 33/16
BC squared: 32 -> 32
BD squared: 11 -> 161/16
CD squared: 11 -> 161/16
```

Thus the emanation retains orientation and incidence while changing one
volume and three metric relations.

## Cut A: direct receiver

The direct receiver presents no apparent crossing:

```text
source V/E = 4/6
diagram V/E/F = 4/6/4
apparent crossings = 0
```

The three bounded face areas are \(4,4,8\); the outer signed doubled area is
\(-16\). The source graph and face dual are both \(K_4\), with reciprocal
Ihara polynomial

\[
16u^{12}-24u^{10}-16u^9-3u^8+24u^7+16u^6-6u^4-8u^3+1.
\]

The nonzero oriented primitive counts through length eight are

```text
length 3: 8
length 4: 6
length 6: 12
length 7: 24
length 8: 18
```

## Cut B: same source, precessed receiver

The receiver change alone presents one regular apparent crossing:

```text
AC x BD at (1344/1175,252/235)
AC is over BD
crossing orientation = +1

source V/E = 4/6
diagram V/E/F = 5/8/5
```

The receiver-dual reciprocal becomes

\[
\begin{aligned}
&-48u^{16}+112u^{14}+32u^{13}-40u^{12}-64u^{11}
-68u^{10}+8u^9\\
&\qquad+41u^8+40u^7+12u^6-8u^5-10u^4-8u^3+1.
\end{aligned}
\]

Its nonzero primitive counts through length eight are

```text
length 3: 8
length 4: 10
length 5: 8
length 6: 16
length 7: 40
length 8: 68
```

The source reciprocal remains exactly the Cut A polynomial. The additional
receiver loops therefore do not testify to new source incidence.

## Cut C: emanated source, same precessed receiver

After \(D_z:1\to1/4\), the crossing leaves this receiver:

```text
source V/E = 4/6
diagram V/E/F = 4/6/4
apparent crossings = 0
```

The four face areas differ from Cut A:

\[
\frac{48}{25},\quad-\frac{144}{25},\quad
\frac{16}{25},\quad\frac{16}{5}.
\]

Nevertheless both the unweighted source and receiver-dual Ihara polynomials
equal Cut A exactly, as do the displayed primitive loop counts.

## Analysis

The three cuts close the required separation.

1. **Source incidence is receiver-invariant but geometry-blind.** Its
   unweighted loop function is identical in A, B, and C even though the
   source volume and metric relations change in C.
2. **Raw receiver topology is not receiver-covariant.** Its unweighted loop
   function changes from A to B although the source is identical.
3. **Topological recurrence is not causal identity.** A and C have the same
   unweighted source and receiver-dual functions, yet their source volume,
   edge metrics, receiver face areas, and chronology differ.
4. **An apparent crossing is useful testimony but not a source junction.**
   The construction splits it for planar face recovery while retaining the
   two source branches and their depth order.
5. **The missing carrier is transported decoration, not more graph
   enumeration.** A useful loop object must carry source occurrence,
   receiver transition, exact geometric swing or weight, and returned
   holonomy together.

This result prevents a raw graph zeta from being mistaken for the sought RH
object. A later RH-bearing carrier would still owe an exact trace identity
with the completed zeta amplitudes and a correspondence between its
primitive paths and prime Euler factors.

## Reproduction

```sh
cargo test -p relational-geometry
cargo run -p relational-geometry --example receiver_topology_atlas
```

Source:

- `crates/relational-geometry/src/receiver_topology.rs`
- `crates/relational-geometry/examples/receiver_topology_atlas.rs`
