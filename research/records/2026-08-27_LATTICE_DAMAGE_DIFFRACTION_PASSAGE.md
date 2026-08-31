# Lattice damage and diffraction are one returned-incidence passage

**Date:** 2026-08-27  
**Kind:** source synthesis and exact construction specification. **This record schedules nothing.**
The live roadmap and construction state remain the only scheduling authorities.  
**Truth grades:** `proved-standard` for the finite algebra stated below; `established-bounded` for
the cited experimental and numerical source returns; `project-postulate` for the proposed common
carrier; `interpretation` for the cross-domain readings; `open` for the named formal passages.

## Result

[project-postulate] The source packet does not require a new fracture ontology.  It supplies a
missing composition among owners already present in Holonics:

```text
oriented incidence
  -> compatibility / equilibrium kernels
  -> constitutive edge current
  -> receiver-selected failure
  -> changed incidence
  -> changed later current
  -> boundary radiation and returned morphology.
```

[interpretation] This is the microscopic circulation already used for learning: current does not
merely cross standing; when a declared constitutive threshold is crossed it changes the standing
through which later current travels.  A crack, a line defect, a trained local organ and a changed
optical aperture remain different source species.  Their common relation is the typed returned
incidence passage, not the exterior noun attached to it.

## Exact finite carrier

[project-postulate] Let `V` be a finite vertex population, `E` a finite oriented branch population,
`B : displacement(V) -> extension(E)` its incidence/compatibility map, `w_e >= 0` a situated edge
stiffness, and `D_k subset E` the branches departed by chronology `k`.  The surviving stiffness and
stored displacement energy are

```text
w[D]_e = if e in D then 0 else w_e,
E_D(u) = (1/2) sum_e w[D]_e * |(B u)_e|^2.
```

[proved-standard] If `D subset D'`, then `E_D'(u) <= E_D(u)` for every fixed displacement `u`.
The proof is termwise: every removed nonnegative summand becomes zero and every retained summand is
unchanged.  This theorem is exact, finite and independent of a continuum or probabilistic limit.

[proved-standard] The preceding inequality is not a fixed-load law.  Under a declared load, gauge
quotient and invertible positive stiffness operator, removal may increase the minimizing
displacement and the compliance.  Fixed displacement, fixed force and fixed boundary current are
different receivers and may not be compared without the constitutive rebase joining them.

[project-postulate] A deterministic damage return has the form

```text
D_(k+1) = D_k union {e | failureReceiver(e, state_k, history_k)},
state_(k+1) = conduct(B, w[D_(k+1)], boundary_(k+1), state_k).
```

[proved-standard] The union law gives `D_k subset D_(k+1)` by induction.  It does not say that
energy, entropy or information is globally monotone: those conclusions additionally require a
named storage line, current, aperture, boundary condition and receiver quotient.

[project-postulate] The dual operator `B*` returns equilibrium.  Compatible infinitesimal motions
occupy `ker B`; self-stresses occupy `ker B*`.  Damage changes both kernels because it changes the
incidence population, so a crack front is a moving rank/kernel seam rather than only a drawn slit.
The existing `Rigidity.lean` witnesses this primal/dual distinction on exact rational material.

## What the fracture sources establish

[established-bounded; external-source] Topological Maxwell lattices can localize protected floppy
modes or states of self-stress at domain walls, and that localization redirects stress and failure.
The more recent damage-functionalisation study uses those modes to control damage propagation.
Sources: [fracturing of topological Maxwell lattices](https://arxiv.org/abs/1801.08557) and
[damage functionalisation](https://arxiv.org/abs/2503.22556).

[established-bounded; external-source] Triangular lattice geometry changes how quenched disorder
appears in fracture, with distinct regimes controlled by geometry and disorder parameters; the
reported toughening is nonmonotone.  This supports a geometry-indexed constitutive receiver, not a
universal scalar disorder law.  Source:
[How Geometry Tames Disorder in Lattice Fracture](https://arxiv.org/abs/2602.09737).

[established-bounded; external-source] Atomistic fracture paths depend on the discrete lattice and
may differ qualitatively between quantum-mechanical and empirical descriptions.  Matching a
continuum crack-tip field to the atomic lattice can predict toughness beyond a free-surface-energy
reading.  Sources: [Al fracture comparison](https://arxiv.org/abs/0907.3572) and
[lattice structure and fracture toughness](https://arxiv.org/abs/1910.09343).

[established-bounded; external-source] Strong edge-energy anisotropy can produce bifurcated,
deflected or rough crack paths, while weaker anisotropy can return a different brittle path.  This
is evidence that edge orientation belongs inside the constitutive carrier rather than being
averaged away before path selection.  Source:
[edge-energy anisotropy paper](https://www.sciencedirect.com/science/article/abs/pii/S0022509624000450).

[established-bounded; external-source] Silicene fracture depends on its buckled lattice,
temperature and armchair/zigzag orientation.  The paper is a membrane-fracture source; it does not
itself study eyes or ommatidia.  Source:
[Mechanical Properties and Fracture Dynamics of Silicene Membranes](https://arxiv.org/abs/1408.1731).

[established-bounded; external-source] Resonant mid-infrared excitation of an optical phonon in
hBN produces subwavelength line defects with crystal-orientation and polarization dependence; the
reported response repeats with the lattice's sixfold orientation and disappears off resonance in
the cited experiment.  Source: [hBN unzipping](https://arxiv.org/abs/2205.12310) and its
[full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC11062566/).

[established-bounded; external-source] Grain size, grain boundaries, dislocation transport,
nanotwinning and stacking-fault conversion alter the crack path in atomistic CoCrNi simulations.
The returned transition from transgranular toward mixed or intergranular propagation is another
case where a scalar toughness value does not reconstruct the active incidence history.  Source:
[CoCrNi crack propagation study](https://www.sciencedirect.com/science/article/pii/S223878542601094X).

[proved-standard; external-source] In general operational theories, ideal repeatable measurement
and exact coarse-graining constrain later compatible measurements; composition and parallel
preservation matter.  This is an external theorem family whose shape agrees with Holonics'
receiver-quotient, reconstruction-fibre and interchange obligations.  It does not prove those
project obligations.  Source:
[measurement sharpness, nonlocality and contextuality](https://arxiv.org/abs/1404.3348).

## Diffraction, prisms and the finite cancellation theorem

[project-postulate] For addressed apertures or lattice sites `x_j`, complex weights `a_j` and wave
covector `k`, the exact finite structure receiver is

```text
S(k) = sum_j a_j * exp(i * <k, x_j>).
```

It retains relative phase until a later intensity receiver applies `|S(k)|^2`.  The latter cannot
reconstruct every coefficient, phase or path without a declared reconstruction fibre.

[proved-standard] If one receiver sees a complete nontrivial cyclic orbit with equal amplitude
and successive phase ratio `zeta`, where `zeta^N = 1` and `zeta != 1`, its contribution is exactly
zero:

```text
sum_(j=0)^(N-1) zeta^j = (zeta^N - 1) / (zeta - 1) = 0.
```

The zero is a group-character cancellation, not a rounded optical darkness.  Removing one site,
changing one weight, changing the wavelength, or rebasing the receiver reopens the retained
coefficient fibre.

[interpretation] A prism, ommatidial array or retinal aperture lattice can therefore select
wavelength and direction through exact phase incidence.  The vision connection belongs to the
existing port-resolved ocular passage: local apertures and waveguides return into a global receiver
while retaining absorption, scattering, phase and boundary histories.  The fracture papers add
orientation-sensitive lattice constitutions; they are not themselves evidence about biological
vision.

## The RH passage, stated without a thematic shortcut

[open] A finite diffraction zero is not a Riemann zero.  The exact connection has four owed maps:

1. found a dilation-indexed family of lattice currents whose scale sum is a theta kernel;
2. prove its Poisson/reflection law and retain the exceptional and boundary terms;
3. transport the kernel through the Mellin receiver to the completed zeta chart;
4. construct the positive source-faithful operator or form whose radical is equivalent to the
   official critical-line zero condition.

[proved-derived; formal-checked] The repository already owns steps of this route in
`RH/ThetaMellin.lean`, `RH/MellinHorizon.lean`, the theta modules and the Weil-form modules.  The
new source packet sharpens the missing source realization: construct the cyclic phase-incidence
current before taking intensity or spectral quotients, and preserve every defect introduced by a
missing site, edge, scale or boundary return.

[interpretation] The sixfold hBN receiver is useful calibration material because its finite group
action, polarization dependence, resonant selection and line-defect return can all be measured in
one causal passage.  It becomes RH-bearing only after the four exact maps above commute.

## Consumption by the common Millennium carrier

| receiver | exact consumption of this passage | remaining separating edge |
|---|---|---|
| Hodge | changed incidence, chain boundary, prism naturality and cancellation of internal faces | global cycle reconstruction and algebraic-cycle admission |
| Yang--Mills | connection-dependent branch current, dual equilibrium, holonomy and positive quotient | continuum gauge field, sector constitution and positive mass gap |
| Navier--Stokes | dynamic Laplacian, storage/current balance and defect-dependent diffusion | uniform scale passage or official singular receiver |
| RH | cyclic character cancellation, theta scale current and Mellin reflection | positivity equivalent to horizontal zero placement |
| BSD | orientation-sensitive lattice theta coefficients and local/global reconstruction | the constitutive Waldspurger/Tunnell correspondence and rank equality |
| P versus NP | evolving constraint incidence and receiver-preserving condensation | uniform complexity-class carrier and lower-bound passage |

Every row above is an [interpretation].  None identifies the source theories.  It states which
typed relation can be consumed and the exact edge still separating that consumption from the
official receiver.

## Lean realization boundary

[open] Do not found `Fracture`, `Crack`, `Eye`, or `Material` cabinets.  First compose these current
owners:

- `Rigidity.lean`: compatibility/equilibrium kernels and self-stress;
- `HolonicComplexParametron.lean`: complex incidence modes and orientation covariance;
- `HolonicPortResolvedBoundaryTransport.lean`: exact storage and addressed boundary return;
- `HolonicEntropyActionInduction.lean`: chronological returned action;
- `HilbertTransportSpectrum.lean`: Laplacian energy, harmonic radical and positive quotient;
- `RH/ThetaMellin.lean`: founded theta-to-Mellin passage;
- `HodgeTriangleHomotopyPrism.lean`: local homotopy current and its lateral-face ledger.

[open] The smallest new formal return is a finite mask theorem over the existing incidence carrier:
masking additional nonnegative branch stiffness weakly decreases fixed-displacement energy, the
damage union is monotone, and the induced boundary/current diagram commutes.  After that return,
the cyclic structure-factor cancellation should be proved over the existing complex turn/winding
owner and connected to the theta source by an explicit scale action.  Only a concrete absent type
or constitutive port exposed by those compositions authorizes a new owner.

