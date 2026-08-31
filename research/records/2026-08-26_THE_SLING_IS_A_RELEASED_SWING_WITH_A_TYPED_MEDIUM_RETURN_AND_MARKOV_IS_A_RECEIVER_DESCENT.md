# The sling is a released Swing with a typed medium return, and Markov is a receiver descent

Date: 2026-08-26  
Scope: Swing, impulse, release, free transport, atmosphere/field response, gravity assist,
deterministic Markov descent, ocular transport, interaction chains, and shared Millennium edges

## Result

[proved-derived; formal-checked] `HolonicSlingTransport.lean` now refines the standing
`SuccessorCurrent` rather than creating another dynamics owner.  One local sling occurrence obeys

```text
coordinate(successor x) - coordinate(x)
  = impulse(x) + mediumReturn(x).
```

The impulse is the deliberate pivot/release current; `mediumReturn` retains gravity, atmosphere,
drag, lattice response or another declared continuation ecology in the same typed quantity line.

[proved-derived; formal-checked] Structural induction gives the exact finite chain law

```text
coordinate(orbit K) - coordinate(initial)
  = sum_{k<K} (impulse(orbit k) + mediumReturn(orbit k)).
```

Every local exchange remains in the source history.  The theorem neither samples trajectories nor
replaces their lineage by endpoint equality.

[proved-derived; formal-checked] A medium is negligible only relative to an additive receiver whose
kernel contains every admitted medium return.  Under that exact hypothesis, the received terminal
difference equals the received impulse sum.  The medium currents remain in the source and its
reconstruction fibre; no numerical tolerance, rounding rule or small-parameter estimate is used.

[proved-derived; formal-checked] The deterministic Markov criterion is now named explicitly.  A
receiver face has a well-defined successor transformer exactly when every two complete states it
identifies also have equal received successor faces:

```text
exists U, U(receiver x) = receiver(successor x)
  iff
receiver x = receiver y -> receiver(successor x) = receiver(successor y).
```

Thus a projected process is Markov precisely when its reconstruction fibres are successor-stable.
If hidden wind, spin, shape, optical phase or boundary state later separates one fibre, that coarse
receiver is not a deterministic Markov state.

## Swing to impulse

[proved-derived; formal-checked] The frozen-board Swing already owns

```text
swing(anchor,body) = anchor + anchor - body.
```

Its complete release difference is now named `swingImpulse` and satisfies

```text
swingImpulse(anchor,body)
  = swing(anchor,body) - body
  = (anchor-body) + (anchor-body).
```

The target reconstructs exactly as `body + swingImpulse`.

[proved-derived; formal-checked] Geometry and momentum remain different typed lines.  A declared
additive realization map transports the geometric Swing difference into the momentum line; only
then does `releasedMomentum - priorMomentum` equal the realized impulse.  This supplies an exact
entrance for the classical impulse--momentum law without identifying length and momentum scalars.

[proved-standard; external-source] In classical mechanics impulse is the time-integrated force and
equals momentum difference, `J = Delta p`.  Source:
[OpenStax, University Physics, impulse and momentum equations](https://openstax.org/books/university-physics-volume-1/pages/9-key-equations).

[proved-derived; formal-checked] A physical sling is not restricted to one affine half-turn.  The
file builds a tagged generator population containing an addressed Swing release and arbitrary
deterministic medium generators.  Because `transportWord` reads right-to-left, the release is the
first occurrence and the medium word follows it.  The theorem `releasedMediumWord_eq` proves that
composition exactly, and `releasedMediumWord_retains_lineage` returns the full nested addressed
fibre and every joining equality.

[proved-derived; formal-checked] This construction also records a useful limitation.  One frozen-
board affine Swing is a point reflection, so it cannot by itself stand for every physical
deflection angle.  A general sling turn enters through the already-owned ordered connection/
holonomy transport or a source-specific isometry; the Swing provides the primitive returned
difference and orientation reversal, while the connection carries their coarse-grained ordered
composition.

## Gravity assist is the frame-return theorem

[proved-derived; formal-checked] Let `V` be the pivot body's exterior-frame velocity and let
`u_in,u_out` be the incoming and outgoing velocities relative to that pivot.  If the ideal orbital
law returns equal relative squared speeds,

```text
|u_out|^2 = |u_in|^2,
```

then Lean proves the exact finite-coordinate identity

```text
|V + u_out|^2 - |V + u_in|^2
  = 2 V dot (u_out - u_in).
```

The energy/speed difference seen by the exterior receiver is therefore carried by the orientation
change relative to the moving pivot.  Equal speed in the pivot frame does not imply equal speed in
the exterior frame.

[proved-standard; external-source] NASA's gravity-assist accounts describe the same three-body
exchange: asymptotic speed relative to the flyby body is retained in the idealized encounter while
the relative direction turns; adding the planet's orbital motion changes the Sun-relative
velocity, with conservation applying to the complete system.  Sources:
[NASA, Basics of Space Flight](https://science.nasa.gov/learn/basics-of-space-flight/primer/) and
[NASA, Cassini gravity assists](https://science.nasa.gov/mission/cassini/gravity-assists/).

[project-postulate] The remaining source realization is dynamical rather than kinematic: derive
the equal-relative-speed premise, deflection/holonomy and encounter boundary from a declared
gravitational potential or spacetime connection.  Atmosphere, thrust and tidal exchange enter as
additional resolved medium ports; when any survives the chosen receiver, the ideal premise fires
false rather than being absorbed into an error term.

## Football, atmosphere, and exact coarse graining

[project-postulate] A football state sufficient for deterministic transport contains position,
linear momentum, orientation, angular momentum/spin, body deformation and the admitted local
atmospheric boundary state.  Hand contact supplies a resolved impulse and torque; release changes
the boundary condition; later aerodynamic pressure and shear supply `mediumReturn` currents.

[proved-derived; formal-checked] The formal notion of exact coarse graining is already available:
the quotient receiver must commute with every admitted local generator, after which naturality
extends through every ordered word.  It is therefore lawful to replace molecular atmosphere by a
pressure/drag constitutive organ only when the selected quotient fibres are stable under every
future deed being claimed.  If two molecular states with the same coarse pressure/wind face return
different admitted ball trajectories, the quotient is insufficient and its fibre reopens.

[interpretation] Spin stabilization is a particularly direct sling face.  The release fixes a
linear impulse and a rotational current; the body's shape and angular momentum constrain which
atmospheric modes can couple strongly over the declared receiver window.  A wind contribution
called negligible is not absent: its accumulated current is either killed by that receiver or the
claim fails.

[project-postulate] The next mechanical lift should transport the engine's exact quadratic hinge
law into Lean as a source realization of `HolonicSling`.  Its fields are already explicit in the
engine:

```text
p(k+1) = p(k) - stiffness * q(k) + externalImpulse(k)
q(k+1) = q(k) + p(k+1) / inertia.
```

The Lean passage must retain typed units, action balance, boundary current and the exact quadratic
orbit invariant; it may not copy the Rust state as a new ontology.

## Light through the eye is the same composition shape

[interpretation] The ocular source and the sling share the composition shape

```text
boundary injection/release
  -> ordered medium interactions
  -> port-resolved return
  -> constitutive receiver
  -> retained reconstruction fibre.
```

For the football the injected action is a mechanical impulse and the medium return is aerodynamic.
For the eye the injection is an optical boundary current, the medium transports complex field
state, and the returns include escape, absorption and photochemical capture.  The common theorem is
the addressed balance/chronology passage; their material constitutive laws remain typed instances.

[proved-derived; formal-checked] Both cases now share exact controls.  Removing the medium is lawful
only through a receiver-kernel or dynamically exact quotient theorem.  Reordering noncommuting
interactions changes the word.  Equal terminal images do not identify paths.  A later receiver that
separates two collapsed histories proves that the proposed coarse state was insufficient.

## Millennium edges

[project-postulate] The sling supplies a common exact instrument rather than an `NS`-only deed:

| Problem | Sling edge | Exact remaining obligation |
|---|---|---|
| Navier--Stokes | impulse plus medium-return decomposition; ordered boundary current; quotient falsifier | realize the medium as the incompressible nonlinear field and prove uniform continuum scale control or return a singular source |
| Yang--Mills | pivot-frame connection, path-ordered turn, holonomy and receiver-visible energy difference | construct the compact gauge source, quantum continuum measure and positive mass-gap receiver |
| Hodge | source/current decomposition, receiver kernel, closed versus exact circulation and retained harmonic fibre | realize the official smooth projective rational cohomology and algebraic-cycle passage |
| BSD | torus winding chronology and receiver-preserved interaction current | realize elliptic arithmetic, Selmer descent and the official analytic/algebraic rank bridge |
| RH | deterministic generator word, spectral receiver and quotient insufficiency | construct a source-faithful operator/Mellin passage whose positivity is equivalent to the critical zero locus |
| P versus NP | complete path lineage versus endpoint/receiver quotient | prove a complexity-preserving reduction and asymptotic separator rather than one finite navigation invariant |

[proved-derived; formal-checked] The shared proved local-to-global law is now: every finite sling
difference is the exact sum of its deliberate and medium currents, and every lawful receiver
quotient must preserve successor conduct across its full fibres.  These theorems do not inhabit an
official Millennium receiver, but they close the missing primitive used by each proposed
source-specific realization.

## Falsifiers and next deed

[open] The sling realization must return an obstruction if any of the following fires:

- the local impulse/medium decomposition leaves a nonzero residual;
- one declared complete state has two successors without an added unresolved interaction face;
- the medium return survives the receiver that called it negligible;
- replacing an ordered interaction word by its multiset changes the result;
- equal coarse states have different received successors;
- a claimed closed sling retains nonzero boundary current or holonomy;
- an atmospheric or optical medium is removed and the admitted endpoint changes;
- a gravity assist omits the moving pivot frame and falsely conserves exterior-frame speed.

[open] The next exact mathematical deed is to compose this sling with the port-resolved boundary
history and a source-specific constitutive medium.  Locally, each successor returns impulse,
stored difference and addressed outward ports.  Globally, telescoping must commute with the
receiver quotient and with the scale/refinement map.  The first source target should be whichever
of incompressible fluid transport, coherent ocular field transport or the exact quadratic hinge
can return that complete square with the fewest new hypotheses.

## Artifacts

[proved-derived; formal-checked] Formal artifact:
`soma/formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicSlingTransport.lean`.

[proved-derived; formal-checked] Reused formal artifacts: `Swing.lean`, `Chronology.lean`,
`HolonicComposition.lean`, `HolonicEntropyActionInduction.lean`,
`HolonicPortResolvedBoundaryTransport.lean`, and `Foundation/Receiver.lean`.
