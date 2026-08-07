# ENTANGLED RECEIVER ATLAS 01

**Date:** 2026-07-25  
**Grade:** BOUNDED EXACT HOST ANALYSIS / FOUR CO-PRESENT RECEIVERS /
NON-CARTESIAN JOINT FACE / VARIABLE GRAIN / TWO OVERLAPPING SWINGS /
SOURCE EMANATION CLOSED / NO FLOATING-POINT CAUSAL DATA / NO BEVY /
NO SOMA INTERIOR CHANGE

## Question

Can one actual marked occurrence population be received through several
independently centered, oriented, normalized, and grained faces while:

1. retaining only tuples which share one source occurrence;
2. carrying a projective invariant which no receiver owns alone;
3. allowing a difference to be invisible at one finite grain and visible at
   another; and
4. propagating one source emanation through every co-present face without
   serially mutating the receivers?

The stopping condition was one exact bounded receipt containing the source
marks, every receiver face, every four-member swing, receiver-local crossing
and triangle data, grain comparisons, and the successor difference.

## Construction

One rational source line carries five ordered occurrences

\[
A=-\frac34,\qquad
B=-\frac14,\qquad
C=0,\qquad
D=\frac14,\qquad
E=\frac34.
\]

The source embedding is

\[
p(t)=\left(t,\frac t2+\frac1{10},\frac t3+\frac15\right).
\]

An off-line pivot \(Q\), the faces \(ACQ\) and \(CDQ\), and one transverse
return thread are founded from this same cut. The two overlapping projective
cells are

\[
(A,B,C)\rightsquigarrow D,
\qquad
(B,C,D)\rightsquigarrow E.
\]

Four exact receiver faces participate:

| Receiver | Projection | Grain | Aspect |
|---|---|---:|---:|
| 1 | orthographic | \(3\times3\) | \(1\) |
| 2 | precessed perspective | \(73\times127\) | \(73/127\) |
| 3 | precessed stereographic | \(23\times7\) | \(23/7\) |
| 4 | precessed orthographic | \(17\times9\) | \(17/9\) |

Every orientation is an exact Cayley rotation. Every gauge, projection,
aperture boundary, crossing predicate, depth comparison, side ratio, and
cross-ratio is rational. A point on a pixel seam retains both neighboring
apertures instead of being rounded into one.

## Initial joint face

The coarse receiver identifies three distinct source occurrences at its
current grain:

```text
B -> aperture (1,1)
C -> aperture (1,1)
D -> aperture (1,1)
```

Receivers 2, 3, and 4 separate all three pairs. Therefore the pairs
\((B,C)\), \((B,D)\), and \((C,D)\) are grain-dark at receiver 1 but
distinguished by the joint face.

The triangle faces are genuinely receiver-relative. For example \(ACQ\)
has side-ratio faces

```text
receiver 1: 1 : 208/225 : 673/225
receiver 2: 1 : 32070977715370941/15399790166968708
              : 72342544858499245/15399790166968708
receiver 3: 1 : 21209945377743109/235846423609207200
              : 276503743858086349/235846423609207200
receiver 4: 1 : 5954/841 : 11029/841
```

The source triangle is one occurrence; these nonidentical ratios are its
four local faces.

The transverse return has:

- no regular crossing in receiver 1, where it reaches endpoint and
  collinearity discriminants;
- a crossing of source segment 2 in receiver 2;
- a crossing of source segment 1, with opposite crossing orientation, in
  receiver 3; and
- a crossing of source segment 2 in receiver 4.

No crossing population is promoted to the identity of the source relation.

## Shared swings

All four receivers return exactly

\[
\chi(A,B;C,D)=\frac32,
\qquad
\chi(B,C;D,E)=\frac32.
\]

The projected coordinates, triangle ratios, crossings, grains, and aspects
are different. The two cross-ratios are nevertheless identical because every
receiver carries a projective face of the same marked source line.

## One source emanation

Move only the source occurrence

\[
D:\frac14\longrightarrow\frac13
\]

and rebuild the same contemporary event cut. The result is:

```text
exact D face changed: receivers 1, 2, 3, 4
finite grain changed: receivers 1, 2
finite grain retained: receivers 3, 4
```

Thus receivers 3 and 4 experience a real exact change which their current
finite apertures tolerate. They do not own enough grain to present that
change as a different cell.

Both overlapping projective cells change at every receiver:

\[
\chi(A,B;C,D):
\frac32\longrightarrow\frac{21}{13},
\]

\[
\chi(B,C;D,E):
\frac32\longrightarrow\frac{21}{16}.
\]

The changed occurrence therefore propagates into both cells that contain it.
The second triangle \(CDQ\) also changes its side-ratio face independently at
all four receivers.

## Interpretation

The result closes five bounded claims.

1. **The joint face is an image, not a product.** There is one tuple per
   source occurrence. No arbitrary combination of receiver-local values is
   admitted.
2. **Entanglement is source sharing.** One source change alters every exact
   receiver face in the same successor even where a finite grain remains
   dark.
3. **Tolerance is receiver-relative but consequence is joint.** Retaining
   one aperture does not imply that nothing changed. Another receiver or a
   transported invariant can make the difference consequential.
4. **Three plus one is an elementary local cell.** A pivot triple fixes the
   local projective gauge and the fourth member supplies the swing.
   Overlapping cells carry one occurrence into several later comparisons.
5. **Resolution can be allocated rather than maximized.** A coarse face may
   retain a wide stable aperture while a fine face resolves the seam. The
   family needs refinement only where every current face would otherwise
   identify alternatives with different consequences.

The bounded construction does not choose a universal receiver count. Four is
the local population required for one nondegenerate projective cross-ratio.
Larger incidence grows by adjoining overlapping cells; a receiver may depart
when its complete face factors through the remaining family at the declared
objective.

## Reproduction

```sh
cargo test -p relational-geometry
cargo run -p relational-geometry --example entangled_receiver_atlas
```

Source:

- `crates/relational-geometry/src/receiver_atlas.rs`
- `crates/relational-geometry/examples/entangled_receiver_atlas.rs`

