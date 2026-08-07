# JOINT DECORATED PATH ATLAS 01

**Date:** 2026-07-25  
**Grade:** EXACT HOST CONSTRUCTION / JOINT NONCOMMUTATIVE PATH CARRIER /
SOURCE AND SCREEN PARAMETERS TYPED APART / CO-PRESENT RECEIVER REFINEMENT /
EXACT LOCAL TURN RETURN / NO FLOATING POINT / NO BEVY CHANGE / NO SOMA
INTERIOR CHANGE

## Question and stop

The prior receiver-topology atlas proved that an unweighted source loop is
geometry-blind and an unweighted receiver loop is perspective-dependent. The
present question was what smallest exact carrier can preserve causal paths
through changing perspectives without turning a projection crossing into a
source junction or collapsing the result to one scalar.

The stop was one bounded construction which:

1. retains lawful source paths;
2. carries the union of exact crossing parameters founded by two co-present
   receivers;
3. exposes exact interval geometry and receiver-local crossings;
4. composes one declared exact turn law around every primitive path; and
5. distinguishes receiver change from source emanation while preserving the
   closed return.

## Corrected crossing record

A visible crossing is not one undifferentiated screen point. For projected
branches \(a\) and \(b\), it now retains

\[
(a,s_a;\ b,s_b;\ r),
\]

where \(s_a\) and \(s_b\) are the exact parameters on their respective source
branches. Screen-chord interpolation parameters remain separately named
diagram testimony. This matters under non-affine receiver projections.

In the initial precessed tetrahedral cut:

```text
AC source parameter = 21/47
BD source parameter = 36/47
screen crossing      = (1344/1175,252/235)
AC over BD           = true
orientation          = +1
```

The crossing does not create an \(AC\leftrightarrow BD\) source transition.

## Joint carrier

The operator carries the six source branches of \(K_4\), their twelve
oriented darts, and the 24 lawful nonbacktracking transitions through actual
source vertices. A dart carries its source branch/frame/order and source
metric, plus one exact face for each co-present receiver. Each receiver face
contains:

- the union of source-parameter cuts founded by the whole receiver family;
- exact projected and gauge-relative interval chords; and
- only that receiver's own crossing marks.

The union is not a Cartesian completion of separate images. It is the common
grain of the two receivers observing the same source cut.

## Exact co-present refinement

Before source emanation:

```text
AC joint cuts: [0,21/47,1]
BD joint cuts: [0,36/47,1]
```

The direct receiver sees no crossing, yet it evaluates both interval pieces:

```text
direct AC intervals: [7056/2209,10816/2209]
direct BD intervals: [12960/2209,1210/2209]
```

The precessed receiver both evaluates the pieces and carries the crossing:

```text
precessed AC intervals: [377104/55225,5202496/497025]
precessed BD intervals: [418464/55225,351626/497025]
```

After only \(D_z:1\to1/4\), the precessed crossing departs. The common
subdivision therefore returns to \([0,1]\) for both receivers. The direct
receiver's complete projected chords remain \(AC^2=16\) and \(BD^2=10\), but
its interval decomposition changes because the co-present grain changed.

This is the exact useful sense in which the perspectives are coupled: a mark
resolved by one receiver changes the joint observational partition available
to the other. It does not assert physical nonlocality.

## Lawful primitive paths

The complete primitive source population through length four is unchanged:
eight oriented triangles and six oriented quadrilaterals. The source metric
word changes precisely on paths containing one of \(AD,BD,CD\).

For the crossing-bearing lawful loop

```text
AC+ BC- BD+ AD-
```

the source metric word changes from

\[
(16,32,11,3)
\quad\longrightarrow\quad
\left(16,32,\frac{161}{16},\frac{33}{16}\right).
\]

The direct receiver's complete chord word remains

\[
(16,32,10,2),
\]

but its joint interval word loses the \(AC\) and \(BD\) subdivisions.

The precessed receiver changes from

\[
\left(\frac{7696}{225},\frac{3616}{225},
\frac{2906}{225},\frac{1586}{225}\right)
\]

to

\[
\left(\frac{7696}{225},\frac{3616}{225},
\frac{1424}{225},\frac{1184}{225}\right).
\]

Its exact local turn word initially is

\[
\left(
\left(-\frac{241}{481},-\frac{225}{481}\right),
\left(-\frac{121}{226},-\frac{325}{452}\right),
\left(-\frac{223}{1453},\frac{1050}{1453}\right),
\left(-\frac{1658}{793},\frac{550}{793}\right)
\right),
\]

and changes after emanation. Both words multiply exactly to \((1,0)\).
Reverse causal orientation is retained as a separate primitive path and also
returns exactly.

## Meaning

The construction closes the ambiguity left by the prior atlas.

- **Source recurrence is the lawful spine.** Receiver crossings decorate it
  but cannot splice unrelated branches.
- **The receiver family can refine a path jointly.** A crossing visible to
  one receiver can partition another receiver's otherwise unchanged chord.
- **Closure is not identity.** Every closed turn word returns to \((1,0)\),
  so that invariant alone is much too coarse.
- **The path interior carries the distinction.** Ordered source darts,
  source metrics, joint cuts, receiver interval metrics, crossings, and local
  turn factors distinguish the contemporary event.
- **No scalar weight has been guessed.** The result is a serializable formal
  path carrier on which a selected domain may later define an evaluation
  functor.

This is useful beyond visualization. The same structure can carry a
mathematical derivation, an algorithmic execution, or another causal ecology
provided that ecology supplies its source order, incidence, receiver maps,
and evaluation law.

For RH, the carrier now has the information a weighted/twisted loop treatment
would need, but no Riemann-zeta identity follows merely from having it. An RH
specialization would still owe an exact evaluation which connects these
decorated primitive paths to prime Euler factors and the Archimedean
completion.

## Reproduction

```sh
cargo test -p relational-geometry
cargo run -p relational-geometry --example joint_decorated_path_atlas
```

Source:

- `crates/relational-geometry/src/decorated_path.rs`
- `crates/relational-geometry/src/receiver_topology.rs`
- `crates/relational-geometry/examples/joint_decorated_path_atlas.rs`
