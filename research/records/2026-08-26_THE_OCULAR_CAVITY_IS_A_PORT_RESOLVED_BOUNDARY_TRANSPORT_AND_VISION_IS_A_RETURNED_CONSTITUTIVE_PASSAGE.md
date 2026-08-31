# The ocular cavity is a port-resolved boundary transport and vision is a returned constitutive passage

Date: 2026-08-26  
Scope: ocular optics, chronology, lossy boundary current, phototransduction, retinal aggregation,
the Complex Parametron, toroidal modes, entropy, receiver fibres, and shared Millennium passages

## Result

[proved-derived; formal-checked] `HolonicPortResolvedBoundaryTransport.lean` now supplies the exact
finite carrier exposed by the ocular example.  One chronology-indexed history retains stored
quantity, incoming current, and every current returned through a finite addressed port population:

```text
storage(k+1) - storage(k) + sum_port returned(port,k) = incoming(k).
```

[proved-derived; formal-checked] The carrier maps directly into the existing `CurrentBalance`
owner by summing the resolved boundary ports.  Its finite telescope is

```text
storage(K) - storage(0)
  + sum_{k<K} sum_port returned(port,k)
  = sum_{k<K} incoming(k).
```

No occurrence, limit, rounding, or stochastic premise is needed for this identity.

[proved-derived; formal-checked] In an ordered quantity line, if every addressed return is
nonnegative, then a null total return is equivalent to nullity of every port current.  With no
further input, stored quantity is antitone.  Both conclusions are exact order theorems; neither
asserts exponential decay or fixes a material absorption coefficient.

[proved-derived; formal-checked] The ocular optical-energy source chart currently declares five
mutually exclusive terminal faces: escape, retinal-pigment deposit, vascular deposit,
photochemical capture, and unresolved exterior.  Thermal and neural currents are deliberately
excluded from that sibling sum: they are downstream quantities obtained only through constitutive
maps from absorbed optical energy or photochemical state.  This prevents one deposited energy
occurrence from being counted twice.

## Source audit: what the eye actually supplies

[proved-standard; external-source] The vertebrate eye is a refracting, scattering, absorbing,
photochemical, and neural transport ecology.  The photon/field passage is distributed across the
cornea and pupil, lens, ocular media, retina and retinal pigment epithelium; photoreceptor output is
then transformed by retinal circuitry before ganglion-cell axons leave through the optic nerve.
Feynman's account emphasizes that spatial combination and differentiation already occur in the
retina, so the optic nerve is an exterior neural return rather than a geometric-optics focal point.
Source: [Feynman, *Color Vision*](https://www.feynmanlectures.caltech.edu/I_35.html).

[established-bounded; external-source] The linked Monte Carlo retinal paper is an absorption and
energy-deposition model containing hemoglobin, retinal-pigment melanin, choroidal melanin, and
scattering coefficients.  In its modeled vessel regions, blood absorbs most incident energy;
outside those regions, substantial energy reaches the RPE and choroid.  It does not establish one
universal `2%--10%` RPE reflectance law, and its random histories are a numerical estimator for a
declared radiative-transfer model rather than evidence that optical causality is intrinsically
random.  Source: [Shih et al., retinal energy deposition model](https://pmc.ncbi.nlm.nih.gov/articles/PMC4881288/).

[proved-standard; external-source] Rod outer segments contain stacked sealed discs, whereas
mammalian cone outer segments contain membrane invaginations continuous with the plasma membrane.
Photon capture changes retinal/rhodopsin, activates transducin and PDE6, reduces cGMP, closes CNG
channels, hyperpolarizes the receptor and changes neurotransmitter release.  A common membrane
carrier must therefore preserve enough source fibre to separate rod discs from cone invaginations;
the word `disc` cannot erase that distinction.  Source:
[Sia et al., *Quantum biology of the retina*](https://onlinelibrary.wiley.com/doi/10.1111/ceo.12373).

[established-bounded; external-source] The quantum-classical rhodopsin study returns a molecular
constitutive passage rather than a binary detector: its model reports a cis--trans efficiency near
`0.67`, an excited-state population split on a femtosecond scale, and modulation by the protein
electrostatic environment.  This is useful evidence for a fast, structured, receiver-dependent
conversion from optical excitation to molecular morphology, but it does not identify rhodopsin
with a Parametron.  Source:
[Mroginski et al., rhodopsin photoisomerization model](https://pmc.ncbi.nlm.nih.gov/articles/PMC8983576/).

[proved-standard; external-source] The gradient-index Hamiltonian-optics thesis distinguishes
geometric path length `s`, optical path `psi` with `d psi = n ds`, physical time `t` with
`d psi / dt = c`, and numerical integration parameters.  It therefore supports a crucial type
separation: chronology, geometric displacement, optical phase/path and apparatus stepping are not
one interchangeable scalar parameter.  Source:
[Menting, *Time integration methods for gradient-index media using Hamiltonian optics*](https://pure.tue.nl/ws/portalfiles/portal/187579674/Menting.pdf).

[established-bounded; external-source] The linked normal-mode study predicts spheroidal and
toroidal *mechanical* modes for an idealized homogeneous/isotropic eye across a broad frequency
range.  It supplies a bounded external source for a toroidal mechanical receiver face, not an
optical whispering-gallery theorem for the living retina.  Source:
[Verriest et al., mechanical normal modes of the eye](https://pmc.ncbi.nlm.nih.gov/articles/PMC5603173/).

[proved-standard] Total internal reflection requires incidence from a higher refractive index into
a lower one above the critical angle.  The quoted vitreous-to-retina values run from roughly
`1.336` to `1.35`, so that particular direction does not support total internal reflection.
Grazing Fresnel return, distributed scattering and source-specific guided modes remain different
questions; a retinal whispering-gallery mode would require measured resonant circulation,
quality factor, angular spectrum and roughness dependence.

[proved-standard] The ocular lens is transparent living tissue whose name `crystalline lens` does
not assert a periodic solid-state crystal lattice.  A finite incidence lattice is still a lawful
discretization of its molecular and cellular transport, but the realization theorem must preserve
the index field, scattering/absorption response and scale-reconstruction fibre rather than infer
those laws from the noun `crystalline`.

## The exact source realization

[project-postulate] A source-faithful finite optical realization has an oriented occurrence
complex `(V,E,F; partial_1, partial_2)` and a chronological successor family `T_k`.  Each transported
occurrence retains at least an addressed branch, frequency or wavelength, polarization, complex
amplitude/phase when coherent, causal cut and lineage.  Its port diagram is

```text
exterior illumination
  -> aperture / refractive injection
  -> ocular-medium propagation
  -> retinal / RPE contact
  -> {escape, pigment deposit, vascular deposit,
      photochemical capture, unresolved exterior}

photochemical capture
  -> rod/cone constitutive response
  -> bipolar/horizontal/amacrine/ganglion transport
  -> optic-nerve exterior return.
```

[project-postulate] A finite complex field state `z_k` should advance through one declared block
transport assembled from aperture injection, index-dependent propagation, scattering, absorption,
photochemical response and escape.  Exact rational or algebraic finite maps are admissible.  A
contractivity, positivity, passivity or energy-loss statement is a separate constitutive theorem;
it is not a property of an arbitrary matrix.

[project-postulate] Coherent propagation must retain complex amplitude, relative phase,
polarization and wavelength until a declared receiver removes them.  A scalar diffusion law is a
later quotient and cannot substitute for a field transport whose admitted successors can still
separate phase.  Monte Carlo sampling is likewise an apparatus receiver for evaluating a
transition law, while the exact law and its unresolved histories remain the causal object.

[proved-derived; formal-checked] The existing Parametron incidence theorem gives the correct finite
integration-by-parts skeleton:

```text
branch drop = incidence(nodal state),
<branch current, incidence potential> = <boundary current, potential>.
```

Consequently a closed winding current pairs to zero with an exact potential drop.  Nontrivial loop
phase requires a declared connection or holonomy; geometric closure by itself does not create it.

[proved-derived; formal-checked] The existing torus realization now has an exact scope boundary:
integral four-torus winding populations are equivalent to their *realized image* among Complex
Parametron branch-current sections.  Four cut receivers reconstruct every winding coordinate, and
the alternating entropy/action two-current of two realized windings is exactly the real-coordinate
cast of the integral `cycleWedge`.  Arbitrary branch currents outside that image are not silently
called toroidal.

[interpretation] The whole eye need not be topologically a torus for toroidal holonics to apply.
A torus enters at a founded closed phase/winding subcomplex, at a returned mechanical toroidal
mode, or at a product of periodic transport coordinates.  The simply connected ocular cavity,
closed current cycles, retinal incidence sheet and neural convergence graph are distinct source
faces and must not be collapsed into one ring drawing.

## Singularities, caustics, and the two-endpoint intuition

[proved-standard] Three mathematically different events can look like an endpoint to a receiver:

1. an aperture is a boundary bottleneck selecting admitted incoming modes;
2. an optical caustic is a critical/rank-loss locus of a projection from transported rays or field
   histories to a receiver chart;
3. optic-disc convergence is many-to-one neural incidence followed by an exterior axonal return.

Calling all three `singularities` deletes the distinctions needed to reconstruct the passage.

[interpretation] The user's two-singularity swing becomes exact after replacing two point masses by
an addressed span between an input bottleneck and a returned receiver fibre.  The middle object is
not a featureless vitreous gap: it owns refractive transport, scattering, absorption, caustics and
the complete histories collapsed by the final reading.  The swing therefore measures a returned
difference between boundary occurrences while retaining the path population that produced it.

[project-postulate] The apparent evolutionary chicken-or-egg question should be posed as coupled
morphology and transport, not as absence of chronology:

```text
M(k+1) = Phi(M(k), J(k), returned_consequence(k)),
J(k+1) = T(M(k+1), J(k), exterior_input(k+1)).
```

Neither lens morphology nor retinal/axonal morphology is declared the unique global origin.  Every
local developmental event remains ordered, while the long recurrence permits refractive geometry,
photochemistry and neural branching to constrain one another through returned consequences.  A
successful realization must survive intervention on each morphology component and detached
remount of the resulting change.

## Time, heat, entropy, and visibility

[proved-derived; formal-checked] Chronology is the ordered successor structure, while a displayed
time coordinate is a section into a typed quantity line.  The existing entropy theorem proves

```text
S(k+1) - S(k) + outward_entropy(k) = production(k).
```

Entropy is monotone only after the admitted boundary current lies in the chosen receiver kernel
and the received production belongs to its positive cone.  Time orientation and entropy
orientation can be coupled by a source law, but chronology alone does not identify them.

[project-postulate] Optical deposit becomes heat only through a typed material constitution from
the optical-energy line into internal energy and entropy production.  Photochemical capture enters
a different biochemical state line, and retinal voltage/current enters another electrophysiology
line.  Exact conservation is checked before these rebases; adding their scalar coordinates without
the constitutive squares is dimensionally and causally malformed.

[proved-derived; formal-checked] A receiver can kill every resolved boundary current while the
source still retains them in its kernel.  Conversely, under nonnegative port readings, a null
aggregate is equivalent to nullity of every visible port occurrence.  This is the concrete ocular
form of `nullity of the null`: it is a theorem about a declared cone and receiver, not an inference
that the complete field history was empty.

## Gravity, dark-sector inference, and the exact reusable lesson

[proved-standard] Gravitational lensing and ocular refraction both transport observations through
geometry, but they use different connections, constitutive laws, scales and source equations.  The
shared mathematical lesson is the inverse problem: one receiver image may have a nontrivial fibre
of source fields and histories, especially near caustics or rank-loss loci.

[project-postulate] The exact dark-sector bridge is therefore a receiver-insufficiency theorem, not
an ocular identification.  Given a calibrated gravitational source model `G`, matter model `M` and
receiver `rho`, define the retained residual

```text
Delta_rho = observed_rho - rho(reconstruct(G,M,boundary,data)).
```

If `Delta_rho != 0`, the admitted realization does not factor the observation.  The next lawful
object is the complete fibre of added source, geometry, boundary and calibration terms that can
close that returned difference.  Naming the fibre `dark matter`, `dark energy`, heat, leakage or
hidden winding requires a further source-specific theorem and intervention that separates those
possibilities.

[project-postulate] Contraction and expansion can be studied through the same typed deformation
carrier only after metric/connection transport, stress--energy coupling, boundary return and scale
passage are installed.  A local optical loss port demonstrates why unreturned current must be kept
explicit; it neither supplies the cosmological constant nor replaces the Einstein receiver.

## Millennium passages

[project-postulate] The ocular construction contributes one exact reusable edge to several
Millennium routes, while closing none of their official receivers by itself:

| Problem | Reused edge | Remaining source-specific passage |
|---|---|---|
| Hodge | finite incidence, boundary/coboundary pairing, winding and reconstruction fibre | smooth projective carrier, rational/algebraic-cycle realization, continuum comparison |
| Navier--Stokes | exact storage/input/outward-flux telescope; finite lossy boundary chronology | incompressible nonlinear constitutive law, continuum scale theorem, uniform regularity or singular receiver |
| Yang--Mills | complex branch current, connection/holonomy obligation, positive receiver cone | compact gauge sector, continuum quantum measure, calibrated spectral-gap theorem |
| BSD | torus winding realization, receiver-natural exterior two-current | elliptic-curve source map, Selmer/Tate--Shafarevich control, official rank equality |
| RH | caustic/rank-loss and receiver-fibre discipline | Mellin/spectral source realization whose positivity is equivalent to the official zero locus |
| P versus NP | path populations and quotient insufficiency | complexity-preserving reduction and asymptotic lower-bound receiver |

[proved-derived; formal-checked] The immediate shared theorem returned here is stronger than an
optical analogy: finite local balance plus resolved nonnegative ports yields an exact global
telescope and an exact zero-total/zero-each equivalence.  The official open problems still require
their named continuum, arithmetic, gauge or complexity source maps.

## Firing falsifiers and next construction

[open] The ocular realization must return an obstruction under any of these tests:

- a claimed `2%--10%` RPE law fails wavelength- and angle-resolved reflectance measurement;
- a claimed whispering-gallery passage returns no reproducible circumferential resonance or
  quality factor in intact ocular tissue;
- two coherent histories with equal intensity yield different phase-sensitive successors, while
  the proposed receiver deleted the phase fibre;
- a single membrane law cannot separate sealed rod discs from cone membrane invaginations;
- event reordering changes physical successors while a scalar-time model returns the same result;
- RPE, vascular, photochemical or neural ablation changes the observed return without changing the
  alleged owning path;
- a finite discretization fails refinement/rebase comparison and therefore has no admitted
  continuum source passage.

[open] The next exact construction is a source realization square from a finite coherent optical
field and material response into `PortResolvedBoundaryHistory`, followed by two separate
constitutive returns: absorptive deposit into heat/entropy and photochemical capture into retinal
neural current.  The square must preserve chronology, frequency, phase, polarization, port lineage
and the full receiver fibre.  Its negative control reverses chart orientation together with every
incidence and constitutive map; moving only one physical coupling must instead change the returned
current.

## Artifacts

[proved-derived; formal-checked] Formal artifact:
`soma/formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicPortResolvedBoundaryTransport.lean`.

[proved-derived; formal-checked] Reused formal artifacts:
`HolonicMembraneActionTransport.lean`, `HolonicEntropyActionInduction.lean`,
`HolonicTorusParametronRealization.lean`, and
`HolonicTorusEntropyParametronEquivalence.lean`.
