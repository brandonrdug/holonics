# Boundary flux couples active interiors; tolerance is receiver-relative

[project-postulate] Brandon's September 8 continuation asks for the divergence theorem,
moving interior/exterior relation, physical impulse, entropy/action currents, Einstein/force
work, receiver tolerance and repeated spectral transport to be articulated together. This
continues the [generator/tube construction](2026-09-08_FRACTAL_GENERATORS_AND_LATENT_REASONING.md)
inside the active AC0–AC5 goal; it does not replace the native construction with a new campaign.

## What crosses a moving boundary

[proved-derived] Let a smooth content density a and flux j satisfy `a_t+div j=s` on a region
whose boundary moves with velocity w. Reynolds transport and the divergence theorem give

```text
d/dt integral_(V(t)) a
  = -integral_(boundary V(t)) (j-a*w).n + integral_(V(t)) s.
```

The proof adds the boundary-sweep term `integral a*w.n` to `integral a_t` and substitutes the
local balance. Thus crossing between interior and exterior depends on relative motion as well
as the field flux. A moving boundary is not merely a different label on two static images.
The bulk source stays explicit; divergence does not say every environmental influence enters
only through the drawn surface.

[definition] For mechanical momentum, take density `rho*v`, transport tensor `rho*v tensor v`
and Cauchy stress sigma. The corresponding moving-volume balance is

```text
d/dt integral_(V(t)) rho*v
 = -integral_(boundary V(t)) rho*v*((v-w).n)
   +integral_(boundary V(t)) sigma*n + integral_(V(t)) f_body.
```

Here `f_body` is force per volume; time-integrated force is impulse, with momentum units.
Traction `sigma*n` couples a surface to interior material through its constitutive law. Across
an interface with opposite normals, tractions balance only after accounting for any interface
momentum, applied force and storage. Empty interface storage is a hypothesis, not a geometric fact.

[definition] Two separated holons can additionally have an active mediating field between
their boundaries. Its momentum, energy, propagation delay and source are another part of the
composition. Integrating a divergence or eliminating an interior does not erase that standing.
The boundary operator therefore carries the effects of both interiors and the intervening
field, with their boundary conditions and chronology.

## A finite mechanical instance with two active interiors

[proved-derived] Consider two masses `m_A,m_B>0` with velocities v_A,v_B, coupled by a linear
drag force `-g*(v_A-v_B)` on A and its opposite on B, g>0. An external impulse I applied to A
gives `v_A(0+)=v_A(0-)+I/m_A`. Thereafter

```text
m_A*v_A'=-g*(v_A-v_B),      m_B*v_B'=g*(v_A-v_B),
P=m_A*v_A+m_B*v_B is constant,
d(t)=(v_A-v_B)(t)=exp(-g*(1/m_A+1/m_B)*t)*d(0+).
```

Adding the equations proves momentum conservation after the impulse; subtracting their mass
normalizations gives the scalar decay generator. With reduced mass
`mu=m_A*m_B/(m_A+m_B)`, relative kinetic energy is `mu*|d|^2/2` and its derivative is
`-g*|d|^2`. The internal relation changes in both masses; the centre-of-mass mode survives while
the relative mode decays. This is a declared lumped mechanical constitutive instance, not an
assertion of instantaneous interaction between arbitrarily distant bodies.

[definition] The same operator structure underlies capacity/conductance diffusion, after its
own quantity map is supplied. `diffusion.rs` retains both local storage and signed branch
current. Its Schur boundary response also retains the interior source. The folded-memory
derivation in the [complex-fluid record](2026-09-08_COMPLEX_FLUID_CHARTS_RETAIN_THE_FOLDED_CURRENT_AND_THE_RECEIVER_BOUND.md)
explains how an eliminated interior remains dynamically active through a generator and kernel.

## The already-owned divergence, entropy and force mathematics

[established-bounded; source-inspected] `HolonicPeriodicBoxDivergence.lean` derives paired-face
cancellation from the divergence theorem in every declared finite dimension.
`NavierStokesLocalEnergyFlux.lean` retains actual pressure/viscous flux and moving-frame terms;
`NavierStokesLambCurrentEvolution.lean` and `NavierStokesLambCurrentCell.lean` retain the
oriented velocity–vorticity source and its cell boundary return. These owners supply the
interior/boundary calculation; they do not authorize replacing local flux by a global cancellation.

[established-bounded; source-inspected] `HolonicEntropyActionInduction.lean` retains
`S_next-S+outwardFlux=production`, with monotonicity conditional on the declared flux and
production law. Its thermal receiver separates symmetric stretch from antisymmetric turn.
`HolonicTorusEntropyParametronEquivalence.lean` identifies the winding-current construction
with its actual realized image and carries the transverse two-current exactly.

[definition] Keep the participating entropy receivers typed. The oriented cross-current
`J_i*K_j-J_j*K_i`, statistical cross-entropy `-sum q_i log p_i`, and thermal entropy balance
are different constructions with possible explicit realization maps. The normalized receiver
currently has dimensionless material potentials. A physical map supplies the relevant energy,
temperature, charge or momentum scale; a name or scalar equality supplies none of those units.

[proved-derived] One concrete electrical realization uses conductances
`G_ij=G0*p_i*p_j` on an unordered complete node-pair family, with G0 in conductance units.
At node voltages v, the resistive power is

```text
Power = G0*sum_(i<j) p_i*p_j*(v_i-v_j)^2
      = G0*v^T*(diag(p)-p*p^T)*v.
```

Expand the square and use `sum p_i=1` to obtain the identity. This physically realizes the
finite normalized Laplacian's quadratic form under the stated network law; it does not identify
every computational cross-entropy value with physical heat or force.

[established-bounded; source-inspected] `HolonicCurvedArcEinstein.lean` retains addressed arc
transport, route curvature return, a flat Minkowski instance and the explicit counterexample
to a universal nonzero coupling equal to `4*arc/differential` for every arc. The local calibrated
formula has its own scope. `HolonicFourForceSectorCarrier.lean` retains the six alternating
planes of a rank-four interaction and dependent force-sector connections; its physical
representations, actions, sources and calibration remain separately stated obligations.

[proved-derived] The covariant energy-momentum boundary has the same discipline. Given a
symmetric stress tensor with `nabla_mu T^(mu nu)=0`, define `J^mu=T^(mu nu)*xi_nu`. Then
`nabla_mu J^mu=T^(mu nu)*nabla_mu xi_nu`, which vanishes when xi is Killing, because its
symmetrized derivative vanishes. Integrating this current requires the actual oriented
spacetime region and boundary. The derivative/connection cannot be dropped when comparing
velocities, accelerations or higher rates in changing frames. See the background construction
in [Carroll's GR notes](https://arxiv.org/abs/gr-qc/9712019); no new Einstein endpoint is claimed here.

## Tolerance is a bound at an actual receiver

[conditional] If a propagated tail satisfies `||e(r,t)||<=A(r,t)` and receiver rho has an
admitted bound `|rho(e)|<=L_rho*||e||`, then `L_rho*A(r,t)` bounds that receiver's response.
When the complete bound stays within one declared output face, that face is settled at that
scope while the tail and its generator remain. Different receivers can have different effective
ranges. Diffusive tails need not have compact support, and reflection, focusing, resonance or
new coupling can make a previously weak component consequential.

[proved-derived] Individual attenuation is not sufficient to omit a whole branching population.
For branch contributions e_j, `|rho(sum_j e_j)|<=sum_j |rho(e_j)|`. If level n has at most B^n
contributions bounded by A*q^n, its absolute total is bounded by `A*(B*q)^n`. This majorant
decays only when B*q<1. Coherent phases can improve the bound, but their cancellation must be
carried rather than assumed. Fractal branching, population growth and decay therefore belong
in one return calculation. Counts alone do not establish energy or physical amplification.

[definition] Tolerance is not a universal amplitude cutoff or a test that the complete causal
fibre is a singleton. Nor is it, by itself, a quantum-to-classical transition. It describes
what the declared receiver and future conduct can distinguish. The quantum phase/interference
carriers remain available behind that reading, as in the tube record's coherent/mixed-state
example. Native exact series and current balls already retain a tail rather than equate it to zero.

## Repeated lattices and modular spectral placement

[proved-standard] In a linear medium with discrete translation symmetry, the wave operator
commutes with lattice translations and admits Bloch-Floquet organization. Wavevectors differing
by a reciprocal-lattice vector define the same translation character. Repeated cells thus
supply reusable spectral transport, with actual wavelength, polarization, incidence and medium
parameters retained. [Johnson's wave-equation notes](https://ocw.mit.edu/courses/18-369-mathematical-methods-in-nanophotonics-spring-2008/e9165ee281f6db686e9dbdc1a556e045_wave_equations.pdf)
develop the operator, symmetry and conservation construction.

[proved-derived] For a cyclic translation chart of N cells, its characters are
`chi_m(j)=exp(2*pi*i*m*j/N)`, indexed modulo N. At prime N the index arithmetic is in the
corresponding prime field. This is an explicit modular spectral coordinate, not a rule assigning
primes to colors. In a homogeneous isotropic lossless exterior with finite real refractive index, a full-rank
periodic surface's fixed-frequency
order G propagates only if `|k_parallel+G|<=n_medium*omega/c`; finitely many reciprocal vectors
satisfy this bounded condition. The remaining orders are evanescent and can still participate
in near-field coupling. Nonperiodic finite apertures can have continuous angular scattering.

[definition] A repeated prepared incident state through the same realized lattice has the same
scattering law. That law may return several coherent outgoing channels; a wavelength label alone
does not specify the entire incident state or force a unique photon outcome. Ordered cell
transport, phase and permitted channels are the reusable generator material for Holonics.

## A concrete implication for the active field

[proved-derived] The paired junction has `D` as contact-column map and, at fixed D with zero
external input, internal update

```text
b_next=H*b,       H=2*D^*(I+D*D^*)^(-1)*D-I.
```

On `ker D`, H=-I: those modes alternate and do not decay. On a nonzero singular direction
with singular value sigma, the multiplier is `(sigma^2-1)/(sigma^2+1)`, of magnitude below
one. The outgoing port carries the complementary current. Thus a fixed passive junction does
not make every internal distinction dissipate. The existing common-drive mode generator is
consistent with this exact structure.

[interpretation] If the material receiver distinguishes a mode that the junction alone does
not radiate, its returned reaction must reach the participating interior for that coupling to
develop. The new normalized receiver already returns its complete discrepancy and two metric
faces; it has not yet applied that return through the producer. This locates the next AC1
attachment more precisely than a generic claim of missing learning theory. The source maps,
receiver and actual producing morphology are explicit; a missing/nonmatching interior return
or changed future consequence falsifies the proposed coupling. No claim that this alone explains
all failed language behavior or establishes physical force units for the current prototype follows.

[definition] Continue the native return into the same ecology, keeping interior standing,
outward flux, bulk/source terms, phase and chronological transport together. Locality and reuse
must come from that conduct and its receiver bounds, not a manually assigned neighborhood radius,
discarded low-amplitude current or a fractal picture. The AC goal remains active.
