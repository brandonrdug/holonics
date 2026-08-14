# The aperture is an interaction Hamiltonian, and a phase object is invisible to the magnitude face

**Date:** 2026-08-14
**Truth status:** `proved-standard` for every classical result named in §§4–8 (Fresnel, Snell as
tangential-wavevector conservation, Bragg/von Laue, the Pockels selection rule, the acousto-optic
conservation pair, Kramers–Kronig, Goriely–McMillen); `established-bounded [measured]` for every
figure taken from this tree; `interpretation` for the Holonic Interaction as the unit and for the
identification of the aperture with the interaction term.
**Evidence:** `measured` on this tree at `b8724d5`; owners opened and cited by line; the aperture
orbit and the orientation controls re-run this session.
**Provenance:** Brandon, direct conversation 2026-08-14, supplying the optical model, the two
extensions, the naming of the perturbation as imaginary, and the whip as the chain instance. The
composition of that model with this body's existing owners, and the theorem in §3, are the
assistant's and are graded as such.
**Band:** THE APERTURE IS THE INTERACTION TERM / A PHASE OBJECT IS INVISIBLE TO INTENSITY /
ONE CONSERVATION LAW AT TWO SYMMETRY GRAINS / CAUSALITY WELDS THE LENS TO THE PERTURBATION /
THE RAY DIAGRAM IS A RENDERING / THE WHIP IS A CHAIN OF ZERO-REMAINDER REBASES

---

## Present question

This body has an `aperture` on almost every reading, and had no account of what an aperture *is*.
What is it physically, what is the unit of interaction it selects, and what follows for chains,
compression and reversibility?

## 1. The aperture is an interaction Hamiltonian

Brandon, 2026-08-14: *"What you mean by the 'aperture' is an Interaction Hamiltonian."*

The reading splits as physics splits it:

```text
   H  =  H_0        free propagation, the current with no interaction
      +  H_int      the lattice: lenses, media, the standing structure    <- the perspective's identity
      +  H_pert     the external modulating field, dynamic                <- the third body
```

The perspective carries `H_int` as part of its identity, and that is his point about the lens: *"the
lens itself is apart of the perspective's identity because it is an invariant constraint for the
instants of the optical diagram being represented."* A perspective is not a viewpoint; it is a
viewpoint **plus the standing structure through which it admits**.

**And the diaphragm is discretely composed.** The aperture polygon's finite side count is not a
detail: the far-field pattern is the Fourier transform of the aperture shape, so an `n`-bladed
aperture returns its spikes as the transform of that polygon — the star-polygon structure
`crates/holonic-engine/src/winding_inertia.rs` already computes, where the sign of a direction is
decided by how far its star polygon winds. **The aperture's discreteness appears in the transform as
windings.** That is `signs_are_windings`, in optics.

### Measured, this session, on real deposits

The claim that the selecting operator decides what the chain structures even are is not analogy. The
same 31 committed artifacts, under this body's four declared apertures:

| aperture | sites | chains | longest |
|---|---|---|---|
| `ByDeclaration / Withheld` | 15 | 14 | 2 |
| `ByDeclaration / Founded` | 16 | 15 | 2 |
| `ByRoute / Incidence` | 45 | **208** | 2 |
| `ByRoute / Multiplicity` | 45 | 208 | 2 |

Fourteen chains or two hundred and eight, from identical bytes, decided by the identity operator
alone — under `ByDeclaration` all 31 artifacts share one name and collapse to a single 0-cell.
His statement of the general case: *"the scope you use as the operator to select the chain series as
groups determines what the chain structures are even observed as."*

## 2. The Holonic Interaction, typed

The unit is four bodies, not two:

```text
   |source>         an object emanating current
   H_int            the intermediary lattice (lenses / crystal), STANDING
   H_pert           an external field modulating passage, DYNAMIC
   <perspective|    the receiver, with its own aperture and its own quantum properties in the instant
```

His second extension is the one that makes it circuitry rather than ray-chasing: *"The problem is no
longer about arbitrary light rays, it is a problem about the initial set of potential rays/currents
emanating from a source object or multiple source objects and their Hamiltonian paths through the
lattices and their reflection/refraction paths (junctions), it is about circuitry."*

A junction is an interface; a path through the lattice is a sequence of junctions; the population of
paths is the object, and no single ray is.

## 3. THE THEOREM — a phase object is invisible to the magnitude face

A pure phase grating has transmission `t(x) = e^{i phi(x)}`, so `|t| = 1` everywhere. **An intensity
receiver measures nothing.** The diffraction orders are entirely in the phase: they are the Fourier
coefficients of `e^{i phi}`, Bessel amplitudes for sinusoidal `phi`. Zernike phase contrast exists
precisely to convert phase into amplitude so that a magnitude reader can see a structure that was
fully present and completely invisible to it.

**This is not an analogy for what this body measured on 2026-08-14. It is the same theorem.**

`derivation_atlas::found_circuit` founds a reach 1-cell with boundary `+derivation, -statement`,
identical in sign to a recruitment cell, so the statement a derivation *proved* is oriented as an
input to it. Flipping that one boundary is negating one generator — a unimodular basis change, an
isomorphism of the chain complex. Measured under the flip:

```text
   rebase_invariants        16 passed, 0 failed      Smith normal form unmoved
   derivation_atlas         39 passed, 0 failed      the atlas's own readings unmoved
   whole engine             24 failed, every one in a reader that TRAVERSES
```

and the route population under the founded aperture moves `14 -> 29` with the longest route `2 -> 3`.

**So the same operation is a rebase with zero remainder to one receiver and a total loss to another.**
Nothing is deleted; every term and both signs are present. The magnitude face cannot see it; the
phase face sees nothing else. `CLAUDE.md`'s `|alpha|^2 = alpha alpha-bar` as the quotient by the
phase circle is this statement one level up: the intensity reading is exactly the quotient that
deletes the coordinate the perturbation lives in.

**Consequence, and it is a standing rule.** An invariant computed on the undirected complex — Betti
number, invariant factor, torsion, a potential's chord residual — is *structurally blind* to
orientation. A defect that lives in the phase cannot be found by any number of magnitude checks, and
this one survived because the only organ that traverses was reachable solely from `#[cfg(test)]`.
The blindness and the deadness were one fact.

## 4. Snell and Bragg are one conservation law at two symmetry grains

Snell is not a refraction rule. It is **conservation of the tangential wavevector**, and
`crates/holonic-engine/src/analytic_field.rs`'s `exact_refraction_fiber` retains
`tangential_covector` by name. Continuous translation symmetry along the interface conserves
`k_parallel` exactly.

Bragg breaks that symmetry down to a discrete subgroup, so Noether returns conservation only
**modulo a reciprocal lattice vector**: `k_out = k_in + G`, equivalently `2 d sin(theta) = n lambda`.
`canon/TABLET_THE_MANIFOLD.md:371` already carries the row — *the lattice selects by phase
coherence; the reciprocal lattice returns discrete directions.*

**So Bragg scattering is a compression with a certified remainder in this project's own vocabulary:**
momentum is conserved in the quotient, and `G` is exactly what the discreteness costs. The tree
computes the continuous case exactly and states the discrete case in canon, and **no current crosses
between them.**

And phase matching is Fourier analysis literally, not by resemblance: the coupling is
`integral e^{i (Delta k) z} dz` over the interaction region — the Fourier transform of that region's
indicator evaluated at the momentum mismatch, going as `sinc^2(Delta k L / 2)`. Quasi-phase-matching
supplies the missing `Delta k` from a grating vector, which is Bragg read from the other side.

## 5. What each perturbation selects on

**Pockels is a parity selection rule.** `Delta(1/n^2)_ij = r_ijk E_k`, and the third-rank tensor `r`
vanishes identically in every centrosymmetric crystal — which is why those media show only the
quadratic Kerr effect. **The linear response exists only where inversion symmetry is broken.** A
parity argument decides whether the term exists at all, before any magnitude is computed.

**The photoelastic effect is the same shape driven by strain**, `Delta(1/n^2)_ij = p_ijkl S_kl`.
Driven by a sound wave it becomes an acousto-optic modulator: a **travelling** phase grating, which
is the dynamic third body in its cleanest instance. Light Bragg-diffracts off the phonon and both
conservation laws hold exactly:

```text
   omega_out = omega_in +/- Omega       energy,   from time-translation symmetry
   k_out     = k_in     +/- K           momentum, from the lattice's DISCRETE symmetry
```

A genuine three-body interaction with the lattice as mediator, and the frequency shift is the
acoustic quantum. This is the concrete object the fourth body of §2 was introduced for.

## 6. Causality welds the lens to the perturbation

Brandon: *"The complex axis is where the external field comes from, it is intuitive to call the
external perturbation 'imaginary'."*

This is exact for a phase modulation, which enters as `e^{i phi}`, and for absorption, which is the
imaginary part of the index. **But the two parts are not independent, and what forbids it is
causality.** `crates/holonic-engine/src/causal_reflection.rs` states the chain in its own opening: a
response cannot precede its stimulus, so the complex susceptibility is holomorphic in the upper half
plane, so its real and imaginary parts are Hilbert transforms of each other —

```text
   Re chi(w) = (1/pi) P integral  Im chi(w') / (w' - w)  dw'
```

**So the lens and the perturbation are one body with two faces, locked by time parity.** Refraction
and absorption cannot be varied independently; fixing one fixes the other.

## 7. The ray diagram is a rendering, and the CRT is the proof

His objection: *"we are attempting to draw light rays that are omnipresent along the paths that we
are illustrating for the duration of their path"* — and the reason it matters is that the limit is
never one sample: *"there are always two things that must be sampled, and it is always a measurement
and a ratio."*

**A cathode ray tube has no image on its screen.** It has a beam painting a raster of arrival
events, and a picture exists only because phosphor persistence and the observer integrate over
arrival times. Nothing is ever simultaneously present. The image is a time-integral of a moving
contact point, and the ray diagram's simultaneity is the one thing a CRT physically cannot have.

Computationally this is not optional, because different paths through a lattice have different
optical path lengths: **what reaches a perspective in one frame departed at different ticks.**

**And this body already carries the structure.** `crates/holonic-engine/src/receiver_current.rs`'s
`ExactReceiverCurrentWitness` carries `arrival_chronology`; equal-arrival predecessors are retained
in one factorized body; later arrivals are kept as `deferred_arrivals` rather than dropped. That is
the arrival spread, implemented, exact, and — until this session — reachable only from a test module.

## 8. The whip is a chain of zero-remainder rebases

At an impedance step the reflection is

```text
   Gamma = (Z_2 - Z_1) / (Z_2 + Z_1)
```

which is simultaneously the Fresnel amplitude coefficient at normal incidence, the transmission-line
reflection, and the Smith chart. **One law.** `analytic_field::exact_scalar_interface_coefficients`
computes it over `Rat` with the energy residual retained, and the fiber carries incident and
transmitted **admittances**, `Y = 1/Z`.

A whip is a taper: `Z = sqrt(T mu)`, and as mass per length falls the impedance falls, so the same
power is carried at rising velocity until the tip exceeds Mach 1 (Goriely–McMillen). Nothing
amplifies — which is `CLAUDE.md`'s standing correction, *"It doesn't amplify it. Gear ratios."*

**The reason nothing is lost is that the taper is adiabatic**: slow against the wavelength, so the
infinitesimal reflections cancel and every link transmits whole. So each link is a **rebase with zero
remainder**, and the crack is the composed ratio. Gear ratios, as a theorem.

**And the converse is the part that governs chains: an abrupt step is a compression, and the
reflected wave is exactly its remainder.** Reflection is not loss. It is the retained fiber of a
junction that did not match.

## 9. Chains, compression, and what reversibility actually is

His statement of the unit: *"if you are referring to only one Holonic Interaction, you are referring
to a selected scope apart of an infinitely larger causal complex."* One interaction is an aperture on
a chain, and the chain continues in both directions through potentials.

**Where compression belongs.** *"this is where compression should actually occur in that these
microscopic steps and rotations in during the interaction contribute to the images of the Holonic
Interaction's lightning patterns."* The interior micro-steps of one interaction are the collapsed
population; the exterior face is the lightning image. The compression is lawful exactly when the
separating word is retained — which `receiver_exact_compression` already returns, per collapsed pair,
with the receiver that saw the difference.

**What reversibility is, and is not.** *"the reversed path can be reconstructed, but it is not
certain and there is no way for the observer to know if they've literally reconstructed the exact
same path, they can only reconstruct an analogous and sufficient path… No path across time is ever
the same path as it once was either, to be interacted with and changed is to then be a different
thing."*

In the optical model this is not a caveat, it is the dynamics: the perturbation is dynamic, so the
second pass sees a different `chi`. **Sufficiency is decided by the declared receiver family, never
by identity.** And three conditions are required for a return at all, each independently absent in
this body before this session:

| condition | owner | state before 2026-08-14 |
|---|---|---|
| the relation retained, not collapsed to a count | `running_integral::ReachedBy` | the walk returned two sets |
| the hand carried, not deleted into a magnitude | `ReachedBy::hand`, `CausalTransportHand` | absent |
| the orientation admitting the traversal | the reach 1-cell's boundary sign | refused, and invisible to every invariant |

## 10. What is owed — CORRECTED THE SAME DAY, and two of the three claims were wrong

The first version of this section named three couplings. A sweep of the composition surface
refuted two of them within the hour. Both errors are kept, because both have a cause worth carrying.

### 10a. The chain already exists — in the amplitude channel

*"No composition of interfaces"* was **false as stated.**
`crates/holonic-engine/src/dimensional_wave.rs:883` `enact_wave` already feeds one junction's
departure into another junction's arrival, for as many ticks as it is enacted:

```text
   :962-978   v = 2 (sum_j Y_j a_j) / (sum_j Y_j)      the junction solve
   :1001      b_i = v - a_i                            each port's departure
   :1011-1012 transported = b_i.rotate(cos, sin)       the propagation phase
   :1013-1015 refuses if the rotation moved the norm   NonunitPhaseTransport
   :1018-1028 schedule_arrival(cursor + port.delay) at the OPPOSITE port
   :997-1000  it re-enters as `incoming` at the next junction
```

Measured: `wave_arcs=10 wave_modes=3 ticks=24 final_energy=25`, every residual exactly zero, with a
two-frame energy ledger and a `PassiveEnergyFailure` refusal.

**And the two laws are one law.** At a two-port junction with a single incoming `a_1`:

```text
   b_1 = a_1 (Y_i - Y_t)/(Y_i + Y_t) = r a_1
   b_2 = 2 Y_i a_1 /(Y_i + Y_t)      = t a_1
```

`exact_scalar_interface_coefficients` is **the closed form of the chained law's two-port special
case**. The composition is a join between two owners, not a construction.

**What is actually a leaf is the GEOMETRIC channel.** `exact_refraction_fiber` returns a reflected
covector and a transmitted regime and **nothing consumes either** — its one consumer outside its own
tests is `examples/analytic_field_transport.rs:508`, which loops three modes over one overlap with a
hardcoded incident covector `(3,4,0)` and writes the result to a TSV. The chained law carries
`ExactComplexWaveCurrent { real, imaginary }` and a scalar admittance: no covector, no normal, no
wave number, no regime, no hand.

**And the transmitted direction is withheld on purpose**, because its square root is irrational over
`Rat`. Chaining two interfaces therefore needs either a declared quadratic extension — and
`multiquadratic.rs` is this body's existing carrier for exactly that, `sqrt(d)` with `d` rational,
as the twisted group algebra of `(Z/2)^n` — or a formulation that never needs the direction itself.

### 10b. A seam defect at that boundary, and two tautological receipts

**Two independently declared admittance tables describe the same physics and are never checked to
agree:** `ExactAnalyticFieldMode::interface_admittance` per material germ (`analytic_field.rs:371`,
read by `interface_optics`) and `ExactAnalyticFieldArc::admittance` per arc (`:386`, compiled into
the chained law's port admittance). Validation at `:1557-1605` checks each is positive and correctly
keyed and never compares them. The reading and the conducting can use different numbers for one
material.

**Two receipts in this module could not have come out otherwise**, and by the tautology rule they are
`definition` grade rather than evidence:

- `incident_dispersion_residual` is stored at `:1089`, but construction returns `Err` at `:1067`
  unless it is zero — **the field is identically zero in every value that exists.**
- `energy_residual` at `:1152-1154` expands to
  `Y_i [1 - ((Y_i-Y_t)^2 + 4 Y_i Y_t)/(Y_i+Y_t)^2] = 0` for **every** positive pair.

The honest content of the module is the three-way fiber — `Traveling`, `GrazingOpen`,
`EvanescentOpen` — which holds the non-propagating regimes open instead of fabricating a transmitted
section, and refuses `NonpropagatingModeAdmitted`. That one can fail and does.

### 10c. The lattice crossing is blocked by a measured theorem, not a missing function

`lattice_gauge`'s lattice is **purely combinatorial** — `Link { id, tail, head }`, `Plaquette { id,
walk }`, `OrientedEdge { edge, forward }`. No coordinate, no position, no metric, no embedding. An
incident covector has nothing to address, and only `lib.rs` names both modules.

The real obstruction is arithmetic. The analytic phase `ExactWavePhaseTransport { cosine, sine }`
generates **SO(2, Q)**, which is infinite; a `StructureGroup` is finite. **The only elements of
SO(2, Q) of finite order are the four Niven points** — and `causal_reflection`'s driver has already
*measured* exactly this: **4 of 88 distinct rational circle points are roots of unity, of orders
1, 2, 4, 4.** So the entire finite part an exact rational phase can hand a gauge group is `Z/4`.
Anything richer needs `Q(zeta_N)`, which that module's own bounds block states nothing here supplies.

This is a named, already-measured obstruction sitting between the two modules — and it is the same
carrier `winding_inertia::lattice_admits_order` uses to derive the **crystallographic restriction**
from `niven_value` rather than hardcoding `{1,2,3,4,6}`.

### 10d. THE CAUSALITY LOCK IS DRIVEN, AND THE ERROR HAS A NAMED CAUSE

The first version of this section said the Kramers-Kronig organ's exercise was unverified. **It is
driven, and driven hard.** `examples/the_reflection_locks_the_faces.rs` returns **18 declared
controls, 0 failed**: the lock biconditional decided over **3,238 exhaustively enumerated responses**
at three apertures with 0 law failures and 11,856 standing residual addresses; exactly 4 of 88
rational circle points are roots of unity; two lattices refused by name with their exact miss; 24
regrained readings bit-identical; 10 of 10 refusals firing by name; and the aliasing failure past the
four-point aperture **exhibited rather than asserted**. `derivation_integral` reaches it on every
route pair, and two further drivers conduct through it. Public reach is essentially total — exactly
one item is test-only.

**The cause of the error is a sentence the driver printed about itself.** Its header read *"It has
one library caller and no direct driver. This file conducts through it,"* and it printed
`(one library caller, no driver)` in its own output. **The file declaring the absence was the
driver.** True for the minutes before it existed, false from the commit that added it, and read by
three sessions since — including into a governing document earlier today.

Repaired at the source 2026-08-14, with the reason written where the next reader meets it. **A
module's reach is a measurement and decays like one; a driver may not describe its own organ as
undriven.**

### 10e. What is genuinely absent, measured

`diffract`, `bragg`, `brillouin`, `structure_factor`, `unit_cell`, `bloch` return **zero code hits**.
`grating` matches 35 files and **every one is a false positive** — `integrating` and
`reintegrating`. `Hamiltonian`, `symplectic`, `poisson_bracket`, `eikonal`, `group_velocity` have
**no hits in any Rust file** anywhere; all 27 are prose. `reciprocal` is never the reciprocal
lattice; it is the reciprocal Ihara zeta and plain multiplicative inverse.

The one structurally symplectic owner carries none of the vocabulary:
`ExactAnalyticAdvectionLaw` (`analytic_field.rs:1180`) states `A^T Omega + Omega A = 0` with a Cayley
successor preserving the `Omega` form exactly, and a grep for "symplectic" will never find it.

## What this record does not claim

It claims no new physics: every classical result above is standard and is cited to be composed with,
not rederived. It does not claim the machine performs optics — it claims the machine already owns the
exact junction law, the arrival chronology, the lattice holonomy and the causality lock as separate
organs, and that composing them is the deed. It schedules nothing; the roadmap and the position
record remain the scheduling authorities.
