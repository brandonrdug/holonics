# The cosmological constant is inferred through plural receiver fibres and a printed decimal is not the measurement

Date: 2026-08-25

## 1. The correction

[proved-standard] The geometric cosmological constant, its normalized density coordinate, and its
vacuum-density coordinates are related by

```text
Omega_Lambda,0 = Lambda c^2 / (3 H_0^2)
Lambda          = 3 Omega_Lambda,0 H_0^2 / c^2

rho_Lambda      = Lambda c^2 / (8 pi G)       -- mass-density chart
epsilon_Lambda  = Lambda c^4 / (8 pi G)       -- energy-density chart.
```

They are not four names for one bare scalar.  They occupy different quantity lines and the last
three transports require additional coordinates or couplings.

[proved-standard] Their conventional dimensions are

```text
[Lambda]         = L^-2
[H_0]            = T^-1
[Omega_Lambda]   = 1
[rho_Lambda]     = M L^-3
[epsilon_Lambda] = M L^-1 T^-2.
```

[proved-derived; formal-checked] `HolonicCosmologicalInference.lean` refines the first identity to

```text
H_source^-1 tensor H_receiver^-1
-------------------------------- = inverse oriented length product,
 c_source       tensor c_receiver
```

and proves that this returns `cosmologicalConstantDim = -2 length`.  The two rate occurrences are
not deleted before the dimension receiver returns the conventional exponent.

[proved-standard] Even if the geometric `Lambda` is exactly constant,

```text
Omega_Lambda(z) = Lambda c^2 / (3 H(z)^2)
```

changes with epoch whenever `H(z)` changes.  A bare `Omega_Lambda` therefore needs an epoch and an
expansion chart.  Most present tables mean the present-day coordinate `Omega_Lambda,0`.

[proved-derived; formal-checked] The exact returned difference between two constant-`Lambda`
parameter-chart occurrences is

```text
Lambda_2 - Lambda_1
  = (3/c^2) [Omega_2 (H_2^2-H_1^2) + (Omega_2-Omega_1) H_1^2]
  = (3/c^2) [Omega_1 (H_2^2-H_1^2) + (Omega_2-Omega_1) H_2^2].
```

These are two path orderings of one exact difference ledger.  They do not linearize the map and
they are not independent-error propagation.

## 2. What an observational paper actually measures

[proved-standard] A cosmological observation begins with detector occurrences: sky maps, spectra,
light curves, redshifts, galaxy positions, shapes, or arrival-time differences.  `Lambda` is not
one of those detector coordinates.

[definition] The complete inference passage is

```text
detector occurrences
  -> calibration and selection chart
  -> typed observable vector y with redshift/sky window W
  -> model prediction T_M(theta, nuisance)
  -> residual and covariance/likelihood
  -> joint parameter population P(theta,nuisance | y,M)
  -> declared derived-quantity map D_M(theta) = Lambda
  -> pushed-forward Lambda population
  -> optional marginal centre/band/decimal receiver.
```

[interpretation] The holonic object is this complete addressed passage and its reconstruction
fibre, not its last printed coordinate.  A mean, median, maximum-posterior point, covariance matrix,
or interval is a later receiver face.  Each can delete curved degeneracies, multiple modes,
nuisance directions, data lineage, redshift support, prior geometry, and model identity.

[proved-derived; formal-checked] `HolonicCosmologicalInference.lean` implements an exact finite
version of the last nonlinear passage.  A rationally weighted joint population is pushed through
an arbitrary target map; summing over the finite returned image recovers exactly the complete
source weight.  No floating-point centre, Gaussian replacement, or rounding is used.

[proved-derived; formal-checked] The same file proves that

```text
(H, Omega) |-> 3 Omega H^2 / c^2
```

is not injective.  In particular, `(H,Omega)=(1,1)` and `(2,1/4)` return the same `Lambda`
coordinate.  More generally `(H,Omega)` and `(sH,Omega/s^2)` share a fibre for every nonzero `s`.
Consequently no printed `Lambda` coordinate can reconstruct the joint expansion state.

## 3. CMB: a long light-cone and acoustic receiver

[established-bounded; measured] Planck's primary observables are temperature and polarization
angular cross-spectra and a four-point reconstruction of the lensing-potential spectrum.  The
theory spectra are generated from a cosmological parameter state and compared through separate
high- and low-multipole likelihoods.  Planck did not sample `Lambda` as a base coordinate in flat
base-`Lambda`CDM.  It sampled

```text
(omega_b, omega_c, theta_MC, tau, ln(10^10 A_s), n_s)
```

and derived `H_0`, `Omega_m`, and `Omega_Lambda`.  Flatness closes a major fibre by imposing
`Omega_Lambda = 1 - Omega_m - Omega_r`.  The acoustic-angle receiver

```text
theta_* = r_* / D_M(z_*)
```

admits a geometric degeneracy among parameter states preserving the returned angle; CMB lensing
and additional probes constrain that fibre.

[established-bounded; measured] Planck TT,TE,EE+lowE+lensing reported

```text
H_0          = 67.36 +- 0.54 km s^-1 Mpc^-1
Omega_Lambda = 0.6847 +- 0.0073
Omega_Lambda h^2 = 0.3107 +- 0.0082
Lambda       = (4.24 +- 0.11) * 10^-66 eV^2
             = (2.846 +- 0.076) * 10^-122 m_Pl^2.
```

The exact exterior decimal coordinates are, for example, `6736/100`, `6847/10000`, and
`424/100 * 10^-66`; the signs and radix depths are retained.  This makes the printed report exact
as testimony.  It does not turn the physical posterior into four exact points.

Primary sources:

- Planck cosmological parameters: <https://doi.org/10.1051/0004-6361/201833910>
- Planck likelihood construction: <https://arxiv.org/abs/1907.12875>
- Planck lensing likelihood: <https://doi.org/10.1051/0004-6361/201833886>

## 4. Type-Ia supernovae: relative distance and an exact null direction

[established-bounded; measured] Pantheon+ transports multiband light curves through a standardized
supernova relation and compares the returned distance modulus with

```text
mu_model(z) = 5 log_10[d_L(z)/(10 pc)]
d_L(z)      = (1+z)c integral_0^z dz'/H(z')
```

through the full statistical-plus-systematic covariance.  The observable is therefore an
integral of the expansion history over each supernova's redshift interval.

[proved-standard] Without an absolute luminosity calibration, the paired change

```text
H_0 -> s H_0
M   -> M - 5 log_10(s)
```

leaves the supernova Hubble diagram unchanged.  Supernovae alone constrain relative distances and
the shape of the expansion history; they do not return dimensional `H_0` or dimensional `Lambda`.

[established-bounded; measured] Under flat `Lambda`CDM, Pantheon+ supernovae alone reported

```text
Omega_m = 0.334 +- 0.018,
```

so the imposed flat chart returns `Omega_Lambda = 0.666 +- 0.018`.  Adding the SH0ES absolute
calibration returned `H_0 = 73.6 +- 1.1 km s^-1 Mpc^-1` in that joint inference.

Primary source: <https://arxiv.org/abs/2202.04077>

[established-bounded; measured] The original high-redshift supernova analyses already returned
elongated joint parameter regions rather than a direct `Lambda` point.  Perlmutter et al. described
their region approximately by

```text
0.8 Omega_m - 0.6 Omega_Lambda = -0.2 +- 0.1,
```

with the contour direction depending on the redshift distribution.

Primary discovery analyses:

- Riess et al.: <https://arxiv.org/abs/astro-ph/9805201>
- Perlmutter et al.: <https://arxiv.org/abs/astro-ph/9812133>

## 5. BAO: transverse/radial distance ratios and the sound-ruler fibre

[established-bounded; measured] BAO analyses begin with galaxy, quasar, or Lyman-alpha two-point
clustering and return combinations such as

```text
D_M(z)/r_d,
D_H(z)/r_d,       D_H(z)=c/H(z),
D_V(z)/r_d,       D_V=[z D_M^2 D_H]^(1/3).
```

The drag ruler is itself a transported model quantity,

```text
r_d = integral_(z_d)^infinity c_s(z)/H(z) dz.
```

Thus BAO alone constrains ratios.  It does not return `H_0` or dimensional `Lambda` without a
sound-horizon calibration.

[established-bounded; measured] DESI DR2 BAO alone in flat `Lambda`CDM reported

```text
Omega_m = 0.2975 +- 0.0086
h r_d   = (101.54 +- 0.73) Mpc
correlation = -0.92.
```

Adding a BBN ruler calibration returned `H_0 = 68.51 +- 0.58`; adding CMB returned
`Omega_m = 0.3027 +- 0.0036` and `H_0 = 68.17 +- 0.28`, with correlation `-0.975` in the named
coordinate pair.  These large correlations are direct evidence that transforming separately
printed marginal centres and widths is not the same operation as pushing the joint population
through the `Lambda` receiver.

Primary sources and released chains:

- DESI DR2 cosmology: <https://arxiv.org/abs/2503.14738>
- Published version: <https://doi.org/10.1103/tr6y-kpc6>
- DESI DR2 paper data: <https://data.desi.lbl.gov/doc/papers/dr2/>

## 6. Lensing, growth, and local distance receivers

[established-bounded; measured] Weak-lensing and galaxy-clustering analyses first project a
three-dimensional matter spectrum through redshift kernels into angular correlation functions.
The lensing kernel contains the typed coefficient

```text
3 Omega_m H_0^2 / (2 c^2),
```

when the paper's common `c=1` chart is unfolded.  DES Y3's combined three-two-point analysis
reported most directly

```text
S_8 = sigma_8 sqrt(Omega_m/0.3) = 0.776 +- 0.017
Omega_m = 0.339^(+0.032)_(-0.031).
```

Under flatness the second coordinate induces an `Omega_Lambda` coordinate, but the analysis did
not thereby become a dimensional `Lambda` measurement.

Primary source: <https://doi.org/10.1103/PhysRevD.105.023520>

[established-bounded; measured] SH0ES performs one generalized least-squares fit across geometric
anchors, Cepheid relations, supernovae in Cepheid hosts, and Hubble-flow supernovae:

```text
chi^2 = (y-Lq)^T C^-1 (y-Lq)
q_best = (L^T C^-1 L)^-1 L^T C^-1 y.
```

It reported `H_0 = 73.04 +- 1.04 km s^-1 Mpc^-1`.  This is a local expansion-rate inference, not
a `Lambda` inference.  A later `Lambda` coordinate additionally imports `Omega_Lambda` and a
constant-dark-energy model from another passage.

Primary source: <https://arxiv.org/abs/2112.04510>

[established-bounded; measured] Strong-lens time-delay cosmography returns a time-delay distance
proportional to `H_0^-1`; the lens mass-sheet transform is an explicit reconstruction fibre.
TDCOSMO-2025 reports `H_0=72.1^(+4.0)_(-3.7)` in flat `Lambda`CDM after combining its lens passage
with a Pantheon+ `Omega_m` constraint.

Primary source: <https://arxiv.org/abs/2506.03023>

## 7. Why values differ: six distinct mechanisms

[proved-standard] **Unit rebase.** `m^-2`, `Mpc^-2`, `eV^2` in natural units, and Planck-area
coordinates are not the same written coordinate.  A lawful fixed unit transport is invertible and
cannot by itself create a physical disagreement.

[proved-standard] **Derived-coordinate change.** `Omega_Lambda` is a ratio receiver involving the
critical density.  Inverting it requires the same `H_0` and epoch state.  This is not a fixed unit
conversion.  Likewise `Lambda -> rho_Lambda` requires the gravitational coupling.

[established-bounded] **Different occurrence windows.** CMB compresses recombination-scale acoustic
and lensing information across a long light cone; supernovae integrate luminosity distance over
their redshift distribution; BAO returns transverse/radial ruler ratios in bins; lensing mixes
geometry and growth; the distance ladder returns the near-zero-redshift intercept.  Their null
directions are geometrically different.

[proved-standard] **Different model quotients.** Flatness, constant `w=-1`, neutrino content,
gravity law, recombination physics, ruler calibration, and nuisance priors close different fibres.
Releasing one of these directions can move a one-dimensional marginal even when the detector
occurrences are unchanged.

[proved-standard] **Marginalization geometry.** Mean, median, mode, and maximum joint likelihood are
different receivers.  Integrating over a curved or multimodal fibre changes volume weights; a
covariance ellipse is itself only a second-order receiver and need not reconstruct that fibre.

[conditional] **Genuine failure of a constant section.** If the physical dark sector or gravity law
varies with epoch or environment, then forcing different redshift kernels through constant
`Lambda`CDM can return distinct effective constants.  This is a scientifically valuable remainder,
but it can be called physical only after unit, calibration, shared-data, nuisance, and model
transports have been audited.

[established-bounded; measured] DESI DR2 makes the last distinction concrete without resolving it.
For

```text
w(a)=w_0+w_a(1-a),
LambdaCDM = (w_0,w_a)=(-1,0),
```

DESI+CMB combined with Pantheon+, Union3, and DESY5 supernova compilations returned different joint
`(w_0,w_a)` regions and preferences over the nested constant model of 2.8, 3.8, and 4.2 standard
deviations respectively.  The collaboration emphasizes that distances, not `w(z)`, are the direct
observables.  These are plural projections onto one chosen dynamical model surface, not three
direct local detections of three cosmological constants.

Primary source: <https://arxiv.org/abs/2503.14738>

## 8. Exact comparison and gluing

[definition] Two reports may be compared only after the following square is supplied:

```text
source observable/chart/model fibre -----> common joint parameter chart
             |                                      |
             v                                      v
       source Lambda face -------------> common Lambda quantity line.
```

The top passage must retain dataset overlap, covariance, calibration, prior, nuisance population,
redshift window, and model lineage.  The bottom passage alone is insufficient.

[proved-derived; formal-checked] The Lean owner defines `returnedLambdaDefect` for a family of
window readings and proves

```text
the family glues to one constant
iff
every addressed pair has exactly zero returned defect.
```

This is the exact local-to-global law for the constant section.  A nonzero defect is not relabeled
as random error.  It is retained until a chart transition, model enlargement, calibration passage,
or genuine nonconstant source law accounts for it.

## 9. Next empirical/formal squeeze

[definition] The first source-specific reproduction target is Planck's released joint chain:

1. mount each sample with its dataset, likelihood, unit chart, and base-`Lambda`CDM lineage;
2. represent every printed decimal input as an exact rational coordinate and every irrational unit
   cast symbolically or by a certified exact enclosure;
3. push each joint `(H_0,Omega_Lambda,...)` occurrence through
   `Lambda=3 Omega_Lambda H_0^2/c^2`;
4. verify the complete pushed weight and reproduce the collaboration's declared summary receiver;
5. reopen curvature and then `(w_0,w_a)` while retaining the new reconstruction fibres;
6. return the shortest observable/redshift separator responsible for any non-gluing.

[open] The present Lean module proves the exact receiver algebra, finite weight conservation,
noninjectivity, difference decomposition, typed dimension, and constant-section gluing theorem.  It
does not yet parse Planck/DESI chains, formalize a continuous likelihood measure, certify the
collaborations' numerical solvers, or prove that current cross-probe remainders require dynamical
dark energy.

[interpretation] This is the holonic gain: the decimal is not rejected, but demoted to the final
face it actually is.  The object of study becomes the complete transport that made it, the fibre it
collapsed, and the exact condition under which plural local cosmological receivers return one
global curvature section.

## 10. Dark matter and dark energy meet on the focusing receiver

[proved-standard] For a timelike congruence with tangent `u`, the geometric split of
`nabla_mu u_nu` contains expansion, shear, vorticity, and acceleration.  In four spacetime
dimensions the Raychaudhuri receiver, with one standard sign convention, is

```text
dTheta/dtau
  = -Theta^2/3
    - sigma_(mu nu) sigma^(mu nu)
    + omega_(mu nu) omega^(mu nu)
    - R_(mu nu) u^mu u^nu
    + nabla_mu a^mu.
```

`Theta > 0` and `Theta < 0` distinguish local volume expansion and contraction of the chosen
world-line family.  Shear and vorticity remain different oriented faces; contraction is not the
same object as curl, and a gravitational field need not be a rotating vortex.

Primary review: <https://arxiv.org/abs/gr-qc/0611123>

[proved-standard] For a perfect field sector in geometric units, Einstein's equation gives

```text
R_(mu nu) u^mu u^nu
  = (kappa/2) (rho + 3p) - Lambda.
```

Consequently its contribution to the expansion derivative is

```text
matter sector:       -(kappa/2)(rho+3p)
geometric Lambda:    +Lambda.
```

Pressureless positive density therefore focuses a geodesic congruence.  A vacuum field with
`p=-rho` contributes `+kappa rho`; after the declared chart relation `Lambda=kappa rho`, this is
exactly the geometric cosmological-constant contribution.

[proved-derived; formal-checked] `HolonicFieldTheoryPassage.lean` proves these two source-chart
calculations over exact rationals and proves that moving a vacuum contribution from the matter
side to the geometric `Lambda` side preserves the returned expansion contribution.

[interpretation] This is the precise common axis behind the proposed stretching/contraction
intuition.  It is not a one-to-one naming of dark matter as contraction and dark energy as
stretching.  It is one receiver on which pressureless clustered density commonly returns focusing,
while a positive cosmological constant or sufficiently negative-pressure sector returns
defocusing.  Shear, rotation, acceleration, boundary conditions, and spatial inhomogeneity remain
in the complete fibre.

## 11. What dark matter is in the inference passage

[proved-standard] In `Lambda`CDM, cold dark matter is modeled as a gravitating, effectively
pressureless, weakly collisional component on cosmological scales.  It clusters and contributes to
the stress--energy source, the gravitational potentials, CMB acoustic evolution, lensing, and
structure growth.  The model name does not determine its microscopic particle identity.

[established-bounded; measured] The Bullet Cluster supplies a particularly geometric separation.
X-ray plasma traces the dominant visible baryonic component after the collision, while weak-lensing
mass peaks are displaced toward the approximately collisionless galaxy components.  The observed
potential therefore does not reconstruct from the plasma distribution alone.

Primary source: <https://arxiv.org/abs/astro-ph/0608407>

[interpretation] Holonically, “dark matter” first names a source-reconstruction remainder:

```text
visible baryonic occurrences
  -> declared gravity/geometry transport
  -> predicted lensing/dynamics/growth receiver

observed receiver - predicted receiver = nonzero source defect.
```

The defect must then be tested against an added matter field, a changed gravity law, calibration,
selection, and other source models.  A successful dark-matter realization owes a field/particle
carrier, its stress--energy, interactions, initial conditions, scale passage, and simultaneous
factorization of the admitted receiver family.  One rotation curve or one lens map does not by
itself reconstruct that carrier.

[interpretation] The phrase “gravity well is a vortex of action transport” becomes exact only
after choosing a congruence and returning all of its kinematic pieces.  Negative expansion reads
convergence; vorticity reads local rotational failure of hypersurface orthogonality; shear reads
shape change at fixed infinitesimal volume.  Frame dragging may carry a curl-like gravitomagnetic
receiver, but a static nonrotating mass can focus trajectories with zero congruence vorticity.

## 12. What dark energy is in the inference passage

[proved-standard] A cosmological constant is the simplest dark-energy model and has exactly
`p=-rho` with constant density.  A dynamical scalar field is a different field theory.  For a
homogeneous canonical scalar in a standard convention,

```text
rho_phi = (1/2) dot(phi)^2 + V(phi)
p_phi   = (1/2) dot(phi)^2 - V(phi).
```

Potential domination returns `p_phi approximately -rho_phi`; kinetic evolution supplies a
different equation of state and perturbation law.  Modified gravity can reproduce an effective
dark-energy receiver without adding the same matter field.

Primary reviews:

- Peebles and Ratra: <https://doi.org/10.1103/RevModPhys.75.559>
- Particle Data Group dark-energy review: <https://pdg.lbl.gov/2025/reviews/rpp2025-rev-dark-energy.pdf>

[proved-standard] Cosmic acceleration follows the active gravitational combination rather than
positive energy density alone.  In an FLRW chart,

```text
ddot(a)/a = -(4 pi G/3)(rho + 3p/c^2) + Lambda c^2/3.
```

Thus `rho+3p/c^2 < 0` can defocus the congruence and accelerate the scale factor.

[interpretation] “The universe is leaking” has two exact possible lifts.  If it means exchange
between dark, baryonic, radiation, or thermal sectors, use paired source currents whose sum
cancels.  If it means action crosses the exterior cosmological boundary, that boundary and current
must be declared and the total FLRW conservation law changes.  Expansion and dilution alone are
not an exterior leak.

[proved-derived; formal-checked] `HolonicFieldTheoryPassage.lean` defines a finite sector balance

```text
density difference + expansion work = admitted exchange
```

and proves that opposite exchange currents cancel in the glued two-sector balance.  A nonzero
exterior remainder cannot disappear into terminology.

## 13. Heat, entropy, and gravity are one coupled field history

[proved-standard] The complete material stress--energy tensor contains energy density, pressure,
momentum density, heat/energy flux, viscous stress, radiation, electromagnetic field energy, and
other constituted sectors.  Einstein's equation receives the complete tensor, not an isolated
temperature scalar:

```text
G_(mu nu) + Lambda g_(mu nu) = (8 pi G/c^4) T_total_(mu nu).
```

The metric and connection then determine the causal paths, volume form, covariant gradients,
expansion, and divergence along which the same material currents evolve.

[proved-standard] Relative to a selected material velocity `u`, a dissipative fluid may be split
as

```text
T^(mu nu)
  = epsilon u^mu u^nu
    + (p+Pi) Delta^(mu nu)
    + 2 u^(mu q^(nu))
    + pi^(mu nu).
```

Projecting `nabla_mu T^(mu nu)=0` along and orthogonal to `u` returns the coupled energy and
momentum balances.  Expansion performs pressure work; shear and bulk viscosity deposit internal
energy; the divergence of `q` transports energy; electromagnetic work and radiation exchange enter
through their addressed source currents.

[proved-standard] Entropy is carried by its own current, for example

```text
nabla_mu s^mu >= 0
```

under a declared irreversible constitutive theory.  Temperature is the integrating/intensive
field relating energy and entropy changes in that material chart.  Gravity changes the transport
geometry and receives the resulting stress--energy; thermal and dissipative motion changes the
source which curves that geometry.

[interpretation] The correct holonic identification is therefore positive and typed: heat,
entropy, matter motion, radiation, and gravity are mutually constituted faces of one field
history.  They are not independent subjects.  Retaining distinct receiver types prevents the
unification from deleting the exact map by which temperature/entropy current becomes
stress--energy and by which geometry feeds back into transport.

The prior detailed source record remains:
`2026-07-17_HEAT_IS_THE_INEXACT_BOUNDARY_CURRENT_TEMPERATURE_IS_THE_INTEGRATING_FRAME.md`.

## 14. The general field-theory holonic lift

[definition] A classical field theory is lifted by the following addressed composition:

```text
base events/cells M
  -> field section phi of a typed bundle E -> M
  -> local jet / covariant derivative D phi
  -> curvature and interaction incidence
  -> local Lagrangian top-form L(phi,Dphi,F,g,...)
  -> finite/continuous action over an admitted region
  -> variation current and Euler--Lagrange return
  -> boundary symplectic/current term
  -> stress--energy from metric variation
  -> Noether/Bianchi conservation under declared symmetry
  -> observable receiver and complete reconstruction fibre.
```

[definition] The internal fibre must remain distinct from the spacetime/base fibre.  Electromagnetic
`U(1)`, electroweak/Higgs, strong `SU(3)`, spinor matter, scalar dark energy, candidate dark matter,
and frame/gravity sectors may share base events while carrying different representations,
connections, actions, and constitutive laws.

[proved-derived; formal-checked] `HolonicFieldTheoryPassage.lean` constructs the finite action
owner abstractly from a local jet and local Lagrangian.  It proves that actions on disjoint regions
glue exactly, that returned action differences glue exactly, and that every additive receiver
commutes with the returned difference.  This is the finite local-to-global core used before a
continuum variation theorem is supplied.

[interpretation] The swing enters three times without metaphorical substitution:

1. a field variation is an oriented source-to-receiver difference of sections;
2. a connection transports one local fibre against another around an addressed pivot;
3. curvature is the non-return of a closed infinitesimal transport word.

Repeated swings form the local jet, action difference, holonomy, and ultimately the propagated
field history.  Particles are localized/excitation receivers of those field sections; mass is a
sector-specific invariant of their propagation and interaction law, not one universal scalar
cabinet.

[open] The new finite owner does not yet construct Lorentzian bundles, continuum variational
derivatives, quantization, renormalization, a Standard Model instance, a microscopic dark-matter
field, or a dynamical-dark-energy solution.  It supplies the common exact carrier on which those
source-specific laws can be composed and falsified.
