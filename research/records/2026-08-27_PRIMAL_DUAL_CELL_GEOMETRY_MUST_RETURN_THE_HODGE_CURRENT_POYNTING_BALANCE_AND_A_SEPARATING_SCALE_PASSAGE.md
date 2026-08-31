# Primal/dual cell geometry must return the Hodge current, Poynting balance, and a separating scale passage

## 1. Position

[proved-derived; formal-checked] The preceding construction closed the common
connection--Stokes--descent joint and constructed a positive finite-cell Hodge/co-curl law with
trivial metric radical.  Its exact return is recorded in
`2026-08-26_THE_MILLENNIUM_LINE_IS_RECEIVER_INDEXED_TRANSPORT_COHOMOLOGY_AND_THE_MISSING_JOINT_IS_CONNECTION_STOKES_DESCENT.md`.

[open] The positive Hodge weights in that return are still declared independently at every cell.
They have not yet been returned from primal/dual cell measures, attached to addressed quantity
origins, used in a complete electromagnetic storage/current law, or transported through a scale
passage that preserves both constitution and energy.

## 2. Existing owners and absent edges

[proved-derived; formal-checked] `HolonicDiscreteMaxwellOperator.lean` already owns the faithful
edge/face incidence, finite Stokes, positive weighted pairings, material co-curl
`M₁⁻¹ Bᵀ M₂`, trivial metric radicals, and passive curl--curl actions.

[proved-derived; formal-checked] `HolonicTypedOriginDimensions.lean` already keeps length, mass,
source time, and receiver time as distinct dimension axes and supplies addressed
`QuantityOccurrence`s whose scalar coordinate is only a receiver face.

[proved-derived; formal-checked] `HolonicEntropyActionInduction.lean` already owns the exact
current convention

```text
storage(k+1) - storage(k) + outwardFlux(k) = production(k),
```

and its finite telescope.  `HolonicPortResolvedBoundaryTransport.lean` refines the outward current
into addressed ports.  `HolonicGranularBoundaryRadiation.lean` already owns boundary/constitutive
adjointness and scale-natural boundary transport.  `HolonicMaxwellPropagation.lean` already owns
the paired curl naturality square under a receiver fold.

[measured] A source search returned no owner which derives the positive Maxwell Hodge weights from
primal/dual cell measures, no exact midpoint electromagnetic energy identity, and no
Hodge-pairing-preserving scale passage.  These are the absent relations.  A new subject-named
Maxwell, Navier--Stokes, Hodge, or Yang--Mills carrier would duplicate standing rather than close
them.

## 3. Exact geometric constitution

[definition] On the present four-dimensional cellular carrier, one primal edge has length type,
its dual cell has three-volume type, one primal face has area type, and its dual face has area
type.  Before material response is added, the diagonal geometric Hodge coordinates are therefore

```text
edgeWeight(e) = dualEdgeMeasure(e) / primalEdgeMeasure(e),
faceWeight(f) = dualFaceMeasure(f) / primalFaceMeasure(f).
```

Their dimensions are respectively `L²` and the dimensionless line.  The four measure occurrences
must retain whether they came from a primal edge, dual edge, primal face, or dual face; equal
rational coordinates do not identify those origins.

[project-postulate] Strictly positive exact rational source measures are sufficient to construct
the existing real positive Hodge carrier by exact rational-to-real transport.  Positivity is a
firing hypothesis, not an inferred mesh property.  Material permittivity, permeability,
conductivity, loss, and coupling remain additional typed constitutive maps; geometric measure
ratio alone must not be advertised as their calibration.

## 4. Exact discrete Poynting identity

[definition] For any history `x`, use the exact arithmetic midpoint

```text
mid(x,k) = (x(k+1) + x(k)) / 2.
```

For every symmetric bilinear Hodge pairing the polarization identity is

```text
<mid(x,k), Δx(k)> = ( <x(k+1),x(k+1)> - <x(k),x(k)> ) / 2.
```

This is exact over the finite carrier and introduces neither a limit nor a rounded time step.

[project-postulate] Let the midpoint Maxwell grain satisfy

```text
ΔB = -curl(E_mid),
ΔE = K(B_mid) - J.
```

Define stored field energy as one half of the edge and face Hodge self-pairings, source work as
`<E_mid,J>`, and the boundary/interface defect as

```text
P_boundary = <curl(E_mid),B_mid>_face - <E_mid,K(B_mid)>_edge.
```

Then exact polarization must return

```text
ΔEnergy + P_boundary + sourceWork = 0.
```

When `K` is the returned material co-curl, weighted adjointness makes `P_boundary = 0` on the
closed four-torus.  On a cut body or material interface the same nonzero defect is the exact
outward/interface current to be resolved by the standing boundary-port owner.  It is not an error
term.

## 5. Scale passage and firing falsifier

[definition] A constituted scale passage must transport edge and face sections, intertwine curl
and material co-curl, and preserve both Hodge pairings.  Pairing preservation is stronger than
preservation of one displayed energy value: it retains every cross-term and therefore every
polarization/current consequence.

[project-postulate] Positive definiteness forces every such edge and face transport to be
injective.  Consequently a noninjective coarse quotient cannot preserve the complete constituted
energy/current family.  It must either retain a reconstruction fibre with a richer decoder or
declare the lost energetic directions outside the admitted receiver family.  This is the firing
insufficiency condition for every source-specific continuum or global reconstruction.

[project-postulate] Constituted scale passages must compose.  Their composed curl, co-curl, and
pairing squares are the exact finite staircase consumed directly by Navier--Stokes, Hodge, and
Yang--Mills.  RH, BSD, and P versus NP consume the same theorem form only after their arithmetic,
analytic, or computational source carriers supply a positive pairing and successor family.

## 6. Construction contract

[open] Close this deed inside the existing typed-dimension and discrete-Maxwell owners:

1. add the four spatial measure dimensions and prove the two Hodge-ratio dimension identities;
2. construct addressed positive primal/dual cell geometry and its exact map to
   `PositiveCellHodge`;
3. prove the midpoint polarization identities and exact Poynting/current balance;
4. factor the history through the standing `CurrentBalance` owner and prove the closed/source-free
   controls;
5. construct pairing-and-curl-natural scale passage, prove its transports injective, and prove
   composition; and
6. run the focused build and axiom audit before promoting any catalog or roadmap claim.

[open] This contract does not claim an official Millennium result, a continuum reconstruction, or
a calibrated physical material.  Its accepted return is the checked common constitutive passage
and the exact hypotheses which a source-specific global theorem must discharge.

## 7. Returned construction

[proved-derived; formal-checked] `HolonicTypedOriginDimensions.lean` now defines the primal edge,
dual edge-cell, primal face, and dual face measure dimensions as `L`, `L³`, `L²`, and `L²`.  It
proves exactly that the corresponding four-dimensional edge Hodge ratio has dimension `L²` and the
face Hodge ratio has dimension zero.

[proved-derived; formal-checked] `HolonicDiscreteMaxwellOperator.lean` now owns one addressed
`PositivePrimalDualCellGeometry`.  Its strictly positive rational measure functions return the
exact ratios

```text
edgeHodgeWeight(e) = dualEdgeMeasure(e) / primalEdgeMeasure(e),
faceHodgeWeight(f) = dualFaceMeasure(f) / primalFaceMeasure(f),
```

and transport them into the pre-existing real `PositiveCellHodge`.  The primal and dual quantity
origins are formally unequal even when their scalar coordinates happen to agree.

[proved-derived; formal-checked] The same owner proves exact weighted midpoint polarization and the
finite identity

```text
Energy(k+1) - Energy(k) + boundaryPower(k) + sourceWork(k) = 0.
```

Here `boundaryPower` is the exact difference between the curl pairing and the proposed face-to-edge
pairing.  It vanishes when that map is the constituted Hodge co-curl.  A midpoint Maxwell history
factors through the standing `CurrentBalance`, returns its complete finite telescope, conserves
energy in the closed source-free control, and makes energy antitone when outward boundary power and
material work are both nonnegative.

[proved-derived; formal-checked] `CellHodgeScalePassage` now retains edge and face transports, both
curl/co-curl naturality squares, and both complete bilinear Hodge pairings.  Such passages preserve
field energy and compose.  Positive definiteness proves both transports injective.  The concrete
zero edge transport is formally noninjective and therefore cannot occur as the edge face of any
complete constituted scale passage.  This is the promised firing counterexample: a lossy quotient
must retain a reconstruction fibre or narrow the admitted receiver family.

## 8. Verification and assumption audit

[measured] The focused command

```text
lake build ElementaryHolonics.Millennium.HolonicTypedOriginDimensions \
  ElementaryHolonics.Millennium.HolonicDiscreteMaxwellOperator
```

completed successfully with 3334 jobs.  Direct `lake env lean` checking of the modified Maxwell
owner also completed successfully.  The added audit declarations report only Lean/Mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound`; the origin-distinction proofs do not use
`Classical.choice`.

[project-postulate] The construction assumes exact positive rational primal and dual measures.  It
does not derive those measures from an embedded smooth mesh or a physical specimen.  The midpoint
Faraday and Ampere laws are hypotheses of each admitted history.  The exact Poynting conclusion is
conditional on those laws but contains no approximation, limit, fitted coefficient, or rounded
time step.

[project-postulate] The scale carrier preserves every cross-pairing, not merely one energy value.
Its injectivity theorem therefore does not forbid all coarse graining.  It proves that a lossy
coarse graining cannot preserve this *complete* receiver family without retaining the collapsed
fibre.  A narrower future receiver may still descend through a noninjective quotient after proving
the corresponding factorization theorem.

[open] Material permittivity, permeability, conductivity, loss, pump response, and cross-coupling
have not been derived from the geometric ratios.  A cut-body trace has not yet converted a nonzero
adjoint defect into an addressed port population.  No source-specific directed scale system or
continuum reconstruction has been instantiated.  No official Millennium statement is inhabited
or refuted by this return.

## 9. Exact residual

[definition] The next deed is no longer another Hodge-weight or energy carrier.  It is the first
source constitution passage:

1. choose one actual primal/dual conductor--core complex already expressible by the standing
   incidence owners;
2. derive its typed anisotropic material maps from exact cell and interface data;
3. prove that its cut/interface port ledger equals the returned adjoint defect;
4. construct its first two scale occurrences and either inhabit `CellHodgeScalePassage` or return
   the exact collapsed reconstruction fibre; and
5. expose that source-specific return through the common local-to-global receiver used by the
   Millennium catalog.

[project-postulate] This residual is shared rather than Maxwell-only.  Electromagnetism supplies the
first constituted source because its incidence and current laws are now present.  Navier--Stokes,
Yang--Mills, and Hodge require the same boundary/constitution/scale passage on their respective
velocity, connection, and cycle carriers.  BSD, RH, and P versus NP require the same theorem shape
after their arithmetic, spectral, or computational sources supply the local current, positive
pairing, successor family, and official receiver.
