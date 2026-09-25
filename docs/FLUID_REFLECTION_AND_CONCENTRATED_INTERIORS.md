# Lightning, fluid reflection and concentrated interiors

[project-postulate] This source guide develops Brandon's September 13 connection between
lightning leaders and return strokes, torus/friction mechanics, stellar collisions, concentrated
interiors, predictive release and HNN. The requested singularity is a receiver-visible
concentration whose interior has dynamics at another scale. The physical source and its
interior remain part of the construction. [THE_REBUILD](plans/THE_REBUILD.md) orders construction.

[definition] The [Swing-to-fluid derivation](HOLONIC_FLUID_CONSTRUCTION.md) now joins these
sources into one construction: constitutive graph reflection, material-action Euler, stress and
relativistic projections, Hodge pressure elimination, microscopic feedback and boundary
memory, then an energy-balanced internal-field stress/diffusion extension. It retains the
complex-Euler/MHD sign distinction and the source-qualified Hodge/RH/BSD connections.

## Physical source and receiver

[definition] A useful common state contains mass density rho, velocity u, internal energy,
composition/ionization, electric and magnetic fields, constitutive coefficients and boundary
geometry. A star, channel or vortex is a situated evolving region of this state. A point mass,
thin channel or exterior field is a receiver/representation of that region, with a stated domain
and retained moments or interior response. Long observation time alone does not choose a fluid
law: relaxation time, mean free path, density, geometry and the requested receiver determine it.

[proved-standard] A compressible conducting-fluid source can use

```text
rho_t + div(rho u) = 0,
(rho u)_t + div(rho u tensor u + p I - tau)
  = -rho grad(Phi) + rho_e E + J_total cross B + f_rad,
div(B)=0,   B_t=-curl(E),
rho_e,t + div(J_total)=0.
```

Here tau is viscous stress, rho_e is charge density, J_total includes the charge transport
appropriate to the chosen frame, and pressure, conductivity and radiative terms need constitutive
closure. For Newtonian self-gravity, `Delta Phi=4 pi G rho`; strong-gravity applications instead
use their spacetime metric and covariant stress-energy equations. Maxwell energy satisfies
`u_EM,t + div(S)=-J_total dot E`. Mechanical work, heat, ionization and radiation must partition
that exchange consistently. [Existing energy/source account](MASS_ENERGY_AND_CAUSAL_TRANSPORT.md).

[proved-derived] Integrating conservative momentum over a fixed volume V and time interval
gives the collision impulse

`P(t1)-P(t0) = -integral_dt integral_boundaryV Pi n + integral_dt integral_V f_external`.

Pi is the complete chosen momentum-flux tensor, including advection and stress. If EM momentum
is included in P, its stress belongs in Pi as well. This follows from the divergence theorem;
the impulse is a boundary/current exchange, not an unexplained velocity reset. The existing
release law `v_plus=v+I/m`, `Delta K=v dot I+|I|²/(2m)` applies to its stated fixed-mass receiver.
Mass loss, accretion and radiation require the corresponding open-system balance.

[proved-derived] Across a moving idealized interface, the same conservation law gives the
Rankine-Hugoniot condition `v_front [U]=[F(U) dot n]`. A resolved viscous or ionizing layer has
an interior profile; its thin-layer limit can expose a jump or concentrated source at a coarser
receiver. A collision/front therefore has both a boundary jump law and an interior realization.

## Leaders form a conducting medium; return strokes use and change it

[historical] The recovered
[leader/return record](../research/records/2026-07-17_THE_LEADER_GROWS_THE_CHANNEL_THE_RETURN_TRAVELS_THE_FOUND_PATH.md)
and laboratory `src/soma/FORMULA.md` sections CX/CXXVIII retain the sequence: field difference,
ionization/front growth, branching, changed conductive/thermal channel, attachment, a finite
return-current wave, heating/radiation/expansion and altered later transport. A later return
travels through material changed by the earlier traversal. It is not the temporal inverse of
leader growth.

[proved-standard] Streamers are ionization fronts with field enhancement at their tips.
A fluid approximation to their electron transport has the form

```text
electron_flux = n_e u - mu_e n_e E - D_e grad(n_e),
n_e,t + div(electron_flux) = S_ion + S_photo - S_attach - S_recombine,
div(E)=rho_e/epsilon_0,       E=-grad(phi)
```

in its electrostatic regime. Electron/ion/neutral transport, photoionization and energy closure
set the source; an atmospheric leader additionally involves channel heating and conductivity
development. [Nijdam, Teunissen and Ebert, streamer physics](https://arxiv.org/abs/2005.14588).

[proved-derived] A local planar leading-edge linearization
`n_t+v_d n_x=D n_xx+r n`, with D,r positive, admits
`n=exp[-lambda(x-c t)]` when `c=v_d+D lambda+r/lambda`.
The marginal spreading branch satisfies `D-r/lambda²=0`, giving
`lambda=sqrt(r/D)` and `c=v_d+2 sqrt(D r)`. This is a source-qualified front calculation under
the stated linearization and front-selection assumptions. It is not a universal lightning
speed or a scan over possible routes. Self-consistent field change and branching still belong
to the coupled source equations.

[established-bounded; source-inspected] da Silva et al. model conductivity through electron
density and mobility, coupled to thermal evolution, ionization/attachment and changing channel
radii. Their reduced channel sections take current as input; the paper also relates them to
radially resolved radiation-hydrodynamic models of expansion and shock formation. This makes
conductivity a returned state, rather than a fixed edge weight.
[Plasma nature and nonlinear channel resistance](https://agupubs.onlinelibrary.wiley.com/doi/10.1029/2019JD030693).

[established-bounded; source-inspected] Borovsky's electrodynamic model treats return strokes
and dart leaders as guided Maxwell waves on conducting cylindrical channels. Energy reaches
and enters the channel through Poynting flux; the wavefront and transported charges have
different roles. This supports a finite propagation/boundary construction, rather than
instantaneous traversal of an entire channel.
[Guided channel waves](https://agupubs.onlinelibrary.wiley.com/doi/abs/10.1029/94JD00407).

## A reduced channel retains inductance, capacitance and heat

[definition] Let s measure channel length. With voltage V, current I, inductance L and
capacitance C per length, series resistance R and shunt conductance G, a conservative local
line model is

```text
V_s = -partial_t(L I) - R I + e_source,
I_s = -partial_t(C V) - G V + i_source.
```

This reduction requires its electromagnetic geometry and frequency range. For constant L,C
and no losses, it gives `I_tt=(LC)^(-1) I_ss`; signal speed is `1/sqrt(LC)` in that model.
For a branched changing channel, boundary conditions, reflected waves and material evolution
are part of the solution. The local line reduction does not replace the tip's ionization model.

[proved-derived] Multiplying the two equations by I and V respectively gives

```text
e = (L I² + C V²)/2,
e_t + (VI)_s = e_source I + i_source V - R I² - G V²
              - (L_t I² + C_t V²)/2.
```

The last term is exchange with changing geometry/material storage; it cannot be discarded by
calling L and C weights. R I² and G V² become nonnegative dissipation for nonnegative R,G.
Their thermalized fraction feeds temperature and then conductivity. This composes the existing
[port-energy law](../lean/Holonics/Physics/PortEnergyHeat.lean)
and [scattering/heat law](../lean/Holonics/Physics/ScatteringWaveHeat.lean)
with an explicit propagation source. It is a reduced physical equation, not a calibrated full
lightning simulation.

## Integration by reflection: the dynamic return is essential

### Continuing plates couple the matter and electromagnetic fields

[definition] The [continuing membrane](RECEIVER_HOLARCHY.md#a-displayed-body-is-a-cut-its-plates-can-be-continuing-bodies)
is an active boundary subsystem of the same source: its charge, tangential current, material
and motion affect the adjacent fields. Maxwell's differential-form equations can be written
`dF=0`, `dG=J`, where the excitation G is determined by the metric and the actual material
constitutive relation to F. This formulation carries changing electric/magnetic receiving
faces without assuming fixed perpendicular plates or a single global I/O direction.

[proved-standard] In a nonrelativistic moving conductor with a declared scalar conductivity,
the conduction law includes `j_cond=σ(E+u×B)`. Faraday's moving-loop EMF is
`∮(E+w×B)·dl=−d/dt∫_(Σ(t))B·n`. The momentum equation receives `ρ_e E+j×B`
and the Maxwell traction; current heating changes thermal state and therefore conductivity.
The curl of the induction law transports and stretches magnetic flux through the fluid.
Fluid vorticity and electric current are coupled fields, not interchangeable operands.
[Induction and Lorentz force](https://www.feynmanlectures.caltech.edu/II_17.html),
[electrodynamics](https://www.damtp.cam.ac.uk/user/tong/justem.html).

[definition] The common construction includes conduction, displacement/polarization current,
radiation and material momentum transport with their respective constitutive laws. Vacuum
electromagnetic propagation does not require a stream of conducting electrons. A biological
membrane additionally supplies its ionic/electrochemical transport and channel kinetics.
The leader/channel equations above already couple charge transport, ionization, conductivity,
heat and changed geometry; the continuum Euler/NS and Maxwell stress account describes their
fluid response at the declared approximation. This is the reusable feedback the HNN's
context/attention interfaces retain.

### Elimination retains the boundary's dynamical memory

[proved-derived] The existing diffusion/Schur construction solves the interior row and
substitutes it at the boundary:

`S=M_bb-M_bi M_ii^-1 M_ib`,
`S phi_b=f_b-M_bi M_ii^-1 f_i`,
`phi_i=M_ii^-1(f_i-M_ib phi_b)`.

This preserves an actual source and reconstruction. In time-dependent conduct the source
includes retained interior standing. Eliminating the interior of
`x_dot=A x+B z+f`, `z_dot=C x+D z+g` gives, for constant D,

`z(t)=exp(Dt) z(0)+integral_0^t exp(D(t-s))(C x(s)+g(s)) ds`.

The boundary therefore receives an initial-state term and the memory kernel `B exp(D(t-s)) C`.
Changing coefficients use their evolution operator instead of a fixed exponential. This is
the dynamic content to retain when a channel, fluid region or HNN constituent is condensed.
It need not be implemented by saving every earlier event; a closed state realization can carry it.

[proved-derived; formal-checked] For the candidate interior chart `z=K x+r`, the
[reflected-boundary owner](../lean/Holonics/Physics/ReflectedBoundaryMemory.lean)
derives the complete return:

```text
r_dot = (D-KB)r + (C+DK-KA-KBK-K_dot)x + g-Kf.
```

The file also derives the product rule along an actual differentiable trajectory and the
discrete changing-chart version

`r_next=(D-K_next B)r+(C+DK-K_next A-K_next B K)x+g-K_next f`.

Thus a static Schur identity is not a dynamic closure certificate. The chart's Riccati defect,
forcing mismatch and retained residual decide the return. If the defect and forcing mismatch
vanish, the residual evolves through the displayed homogeneous operator; decay still depends
on that operator and the chosen norm/source domain.

[counterexample; formal-checked] The passive system `x_dot=-z`, `z_dot=x-z` loses energy at
rate `-z²`. Static interior equilibrium gives K=1. Nevertheless at x=z=1, r=0 and r_dot=1.
An interior that currently agrees with its boundary chart can become distinguishable
immediately. Dissipation does not justify deleting its oscillatory or delayed contribution.

## Tori, friction and colliding waves in the fluid source

[definition] Toroidal flow and field structures carry circulation, flux, winding and their
boundary conditions. Their geometry alone does not determine a force. Viscous stress, resistive
electric fields, pressure and Maxwell stress provide the constitutive interaction. Magnetic
or vortex reconnection additionally requires the non-ideal terms and its domain; conserved
ideal winding cannot be silently reused through a reconnection event.

[proved-derived] A declared sliding-contact law makes the torus/friction link explicit.
For relative tangential velocity w at an interface, let traction on body 1 be `t=-kappa w`
and on body 2 be -t, with kappa nonnegative. The summed mechanical power is
`t dot (u1-u2)=-kappa |w|²`; the complementary heat is positive. Rotation enters through
`u_i=V_i+Omega_i cross r_i`, and torque is the surface integral of `r_i cross t_i`.
For a Newtonian shear layer of thickness d, `kappa=mu/d` is the corresponding planar
approximation. Torus geometry changes the contact, moment arm and relative velocity; the
material law supplies friction. Fluid and magnetic tori use their distributed viscous or
Maxwell stresses with the same momentum/energy accounting.

[proved-derived] Friction and reactive turning are different parts of a constitutive operator.
In a complex port chart `Z=R+iX` with R and X Hermitian, the real power is
`Re(J* Z J)=J* R J`. The reactive part can change phase and store/return energy without being
Joule heat. In generalized Ohm transport, `J dot (J cross B)=0` similarly separates a Hall
deflection from resistive heating. The chosen material and collision regime determine which
terms are present; the word friction does not supply their coefficients.

[definition] On a constant-density incompressible MHD chart, normalize magnetic field as
`b=B/sqrt(mu_0 rho)` and use the projected advection `Bop(v,w)=P[(v.grad)w]`:

```text
u_t = nu Delta u - Bop(u,u) + Bop(b,b),
b_t = eta_m Delta b - Bop(u,b) + Bop(b,u).
```

Here eta_m is magnetic diffusivity, not electrical resistivity. A physical Fourier realization
also retains divergence-free/reality conditions and a compatible carrier/aperture.

[proved-derived; formal-checked] The existing finite Galerkin operators now satisfy the
following Elsasser identities. With `z_plus=u+b`,
`z_minus=u-b`, and `nu_plus=(nu+eta_m)/2`, `nu_minus=(nu-eta_m)/2`, expansion gives

```text
z_plus,t  = -Bop(z_minus,z_plus) + nu_plus Delta z_plus + nu_minus Delta z_minus,
z_minus,t = -Bop(z_plus,z_minus) + nu_plus Delta z_minus + nu_minus Delta z_plus.
```

These are the counterpropagating-field interactions of this source. A constant background
magnetic field supplies the usual oppositely directed Alfven transport terms. Density fronts,
radiation and ionization require the larger compressible source; this reduction is not used
unchanged for an entire stepped leader or stellar collision.

[proved-derived] With equal diffusivities and z_minus=0, the nonlinear term in the z_plus
equation vanishes. A nonzero opposite component introduces the cross-advection return;
co-presence still matters through spatial gradients and the projected interaction. In the
Fourier chart the product couples source modes through the actual triad incidence `p+q=k`.
This is a concrete colliding-wave mechanism and a reusable pattern for local HNN composition:
common transport and a newly interacting difference have different consequences because of
the operation, rather than a relevance score attached to their labels.

[proved-derived] The complex-bilinear Euler/NS pair already studied in the repository instead
has imaginary evolution `nu Delta b-Bop(u,b)-Bop(b,u)`. Its difference from equal-diffusivity
MHD induction is `-2 Bop(b,u)`. Its real receiver retains the force `Bop(b,b)`.
The sign of the stretching term matters physically. Complex Fourier amplitudes for one real
field and the additional pair (u,b) are distinct charts. A common imaginary symbol does not
identify their operations. The finite Galerkin implementation of this algebra is
[ConductiveFluidReflection](../lean/Holonics/Physics/ConductiveFluidReflection.lean).

[proved-derived] Conjugation of the added field pair sends (u,b) to (u,-b). Its fixed part is u,
but projecting to that fixed part before the quadratic operation loses `Bop(b,b)`. This is a
precise Galois/involution connection: averaging a symmetry is linear and need not preserve
nonlinear products. The existing
[fluid receiver closure](../lean/Holonics/Physics/FluidReceiverClosure.lean)
retains `Bop(U,r)+Bop(r,U)+Bop(r,r)` and the changing receiver term. Hodge projection removes
the appropriate pressure component; it does not remove arbitrary circulation or hidden feedback.

## Concentrated interiors and the meaning of a singular receiver

[definition] For a normalized profile f on R^d, a scale epsilon(t)>0 and moving centre X(t),
consider `rho_epsilon(x,t)=M epsilon^(-d) f((x-X)/epsilon)`. The rescaled interior density is
`epsilon^d rho_epsilon(X+epsilon y,t)=M f(y)`. Its mass remains M. The field
`u=X_dot+(epsilon_dot/epsilon)(x-X)` satisfies the continuity equation with this density by
the chain rule. Momentum and energy still require the force/stress law: internal acceleration
is `X_ddot+(epsilon_ddot/epsilon)(x-X)`. The concentrated object is not supported for free.

[proved-derived] For radial f, adding `Omega cross (x-X)` preserves that continuity equation:
the rotational field is divergence-free and tangent to density shells. Its acceleration adds
`(Omega_dot+2(epsilon_dot/epsilon)Omega) cross (x-X)` and
`Omega cross (Omega cross (x-X))`. This explicitly retains turning, dilation and centripetal
stress inside a concentrated exterior face. At fixed angular momentum, shrinking the moment
of inertia increases rotational kinetic energy; the energy/force source must account for it.
The density normalization is a conserved-mass fluid chart, while relativistic composite mass
also includes the changing internal and binding energy at its specified receiver.

[conditional] If a receiver kernel K_l varies little across epsilon, its measured density
approaches `M K_l(x-X)` while the resolved interior retains f and its dynamics. A point-like
face therefore need not be an empty or structureless source. A finite pulse of small epsilon
can enter and leave that receiver's resolution. A diverging physical norm at an endpoint needs
its own scale/clock and regularity analysis; changing coordinates alone does not prove it bounded.

[established-bounded; source-inspected] The existing
[dynamic rescaling](../lean/HolonicsResearch/Fluid/NavierStokesDynamicRescaling.lean)
uses moving centre, scale, amplitude and physical time together. It retains the scale drift,
centre velocity, amplitude rate, viscosity conversion and forcing. The endpoint owners retain
conditions under which a nonvanishing normalized value or gradient obstructs smooth extension.
This gives the requested interior/exterior account an actual source map, rather than negating
the interior at the point where an exterior chart becomes inadequate.

[definition] A thin channel supplies the corresponding line/point example. At fixed channel
current I and radius a, its average axial current density is `I/(pi a²)` and resistive power per
length is `I²/(sigma pi a²)` in the stated uniform-section chart. A receiver resolving the length
but not the radius sees a line current; a more distant receiver may see only its current/charge
moments. The plasma interior still controls conductivity, heating and the later field. Shrinking
a at fixed I and sigma raises the required power, so a sustained concentration requires an
energy source or changed material/current—not a free, eternal singular object.

[definition] For black-hole work, retain four separate receivers: unresolved concentration,
coordinate-chart degeneration, causal trapping/horizon, and curvature or geodesic completeness.
They answer different source questions. The requested scale-dependent concentration is used
here in its own right. A Lorentz change of observer and a change of resolution are also different
maps, both of which belong in the comparison. No conclusion about an actual GR interior follows
solely from a point-like exterior image.

[proved-standard] Acoustic horizons give a concrete fluid counterpart to the waterfall
intuition: the outward characteristic speed can vanish when an inward flow matches local sound
speed. The fluid can remain regular there while the chosen outgoing-wave receiver loses access
to its interior. A cliff by itself need not be a sonic horizon; release from its surface to a
falling trajectory instead changes the contact/boundary law.
[Unruh's acoustic-horizon construction](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.46.1351).

[definition] Mass in this account uses retained energy and momentum, including interior
circulation, pressure and boundary exchange: `M² c⁴=E²-c²|P|²` at its admitted composite receiver.
Zero net outward flux need not mean zero interior energy. A vortex can carry energy, momentum
and an exterior response, but winding alone does not specify its mass. The existing
[mass-energy source maps](MASS_ENERGY_AND_CAUSAL_TRANSPORT.md) connect these quantities to their
Maxwell, matter and stress-energy owners.

## Stellar collisions are a demanding application of this distinction

[established-bounded; source-inspected] A 2026 study of white-dwarf/main-sequence collisions
uses hydrodynamics, radiation pressure and a nuclear reaction network. It starts the approach
with point-mass orbits, then resolves fluid stars before contact to capture tides and shocks.
Head-on and off-axis encounters produce different shock and ejecta structures. This is an
explicit source-dependent change of representation, with stated stellar-model approximations.
[High-velocity WD-MS collisions](https://academic.oup.com/mnras/article/546/4/stag302/8483904).

[established-bounded; source-inspected] A comparison of grid and particle hydrodynamics for
main-sequence stellar collisions found agreement in gross remnant profiles and mass loss,
but differences in internal mixing. Equal coarse outcomes did not certify identical interiors.
[Hydrodynamic-method comparison](https://arxiv.org/abs/astro-ph/0605753).

[established-bounded; source-inspected] Binary neutron-star merger simulations combine
relativistic hydrodynamics with finite-temperature equations of state and neutrino cooling/
heating approximations. Shocks, composition and mass ejection connect the interior dynamics
to observables. The physical source becomes GR radiation hydrodynamics at that scale.
[Relativistic merger study](https://arxiv.org/abs/1502.06660).

## Selective prediction, settling and HNN

[proved-standard] Many-body prediction already uses structured approximations: fast multipole
methods aggregate separated gravitational/Coulomb sources through controlled expansions.
Resolving close interactions and retaining multipoles are different work from evaluating every
pair identically. The source distribution, accuracy and force receiver determine the expansion.
[Greengard and Rokhlin](https://www.sciencedirect.com/science/article/pii/0021999187901409).

[definition] Fractal/sphere packing supplies spatial restrictions and separation geometry for
such work, not a universal interaction law. A separated region can be represented by its
boundary response or controlled multipoles; a collision, new front or changed receiver can
require reopening its interior. Quasi-static gravitational/Coulomb kernels and retarded wave
propagation have different time domains. Their approximation and source-clock maps remain
explicit when choosing an economical traversal.

[conditional] On a Hilbert-space complement with positive self-adjoint generator G satisfying
`G >= lambda I`, lambda>0, the equation `r_dot=-G r+f` has unforced norm bounded by
`exp(-lambda t) ||r(0)||`; forcing contributes its semigroup convolution. A spectral location
alone does not give that bound for a general nonnormal operator. Oscillatory, harmonic,
conserved or newly coupled modes need not decay. This makes settling into an environment a
specific dynamical question: which differences relax, which remain driven, and which later
receivers can distinguish them? Common motion can be quotiented only through its admitted
future family, or with a declared error bound. Instant agreement alone is insufficient.

[proved-standard] Positive relaxation modes have the Mellin identity
`integral_0^infinity t^(s-1) exp(-lambda t) dt = Gamma(s) lambda^(-s)` for Re(s)>0, lambda>0.
A spectral zeta construction sums such modes only on its convergence/continuation domain;
zero modes and tails remain separate. Hodge harmonic modes make that zero-mode issue concrete.
For the repository's RH work, the xi heat source and `Lambda_std=4 Lambda_DN` are the actual
bridge. Fluid settling or a finite gap pattern does not establish the remaining global
xi-zero/threshold inequality; it supplies operators and receiver questions to instantiate there.

[project-postulate] HNN should be developed as an interacting field/body system with formative
constitutive geometry. Its source currents, phases, incidence, local reaction and return are
the machinery; particle, mesh, mode and navigator representations are chosen by their lawful
receivers and costs. A physical realization supplies units and its constitutive law. A statistical
fit can estimate a local relation within this system; it cannot substitute for the missing
current, coupling, clock or interior state. Model labels and generic ML terminology decide none
of those operations.

[definition] The concrete implementation consequences are to preserve producing conditions,
distinguish source changes from coefficient changes, keep reactive/oscillatory complements,
and carry the full mixed return when condensing an interior. Prediction release is the outgoing
face of that prepared transport. The new boundary-memory equation supplies a closure defect
for the HNN encoding work; the conductive-fluid equations supply a physical source family.
Neither requires storing every event or treating every holon as an individually simulated atom.

[definition] A physical performance report therefore includes the simulated-time advance per
wall-time, resolved region/modes, constitutive model and error/closure bounds. Receiver frames
and local updates can additionally be counted as FPS/TPS-like rates using the
[measurement conventions](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/DEVELOPMENT.md#performance-and-information-measurements). An
HNN epoch (a division of an aeon at a receiver's section) is not a physical timestep until its
clock map is supplied.
