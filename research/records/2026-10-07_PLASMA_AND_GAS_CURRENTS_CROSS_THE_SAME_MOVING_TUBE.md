# Plasma and gas currents cross the same moving tube

October 7. Refs #62, #63, #73, #20. [project-postulate] Brandon's stellar-collision examples
concern plasma dynamics across aeons, including gas and Fermi-gas emulation. [proved-derived;
source-inspected] for the transport identities below under their hypotheses. No new simulation,
native owner or kernel acceptance. The proper-clock and curvature join below states how this inertial realization sits inside
a covariant receiver. The dedicated public review owns the actual item362
relativistic Vlasov–Maxwell paper and item376 computation; those review conclusions are not
assumed here.

The existing guide `FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS` already couples conducting-fluid
momentum, charge, Faraday, Lorentz work, heat, ionization and radiation. `ConductiveFluidReflection`
owns the finite incompressible MHD/Elsasser composition; `Fluid/ComplexFluid` proves its induction
sign differs from complex NS and cancels the ideal cross-power exchange. `HolonicDiscreteMaxwellOperator`
owns incidence, constitutive co-curl and midpoint boundary/source-work balance; `MaxwellEnergyCone`
owns the local field flux bound. These are the existing operators to join. Long elapsed aeons
do not supply collision, pressure, conductivity or radiation closure.
The incompressible physical chart uses `b=B/sqrt(mu_0 rho_0)` at constant density; its finite
Galerkin identities do not supply the normalization, reality slice or continuum limit for
an arbitrary stellar source.

## The actual moving induction receiver

Let `X(t,xi)` be a sufficiently smooth orientation-preserving spatial diffeomorphism on the
regular interior, with `F=D_xi X`, `J=det F>0`, and `w composed with X=partial_t X`. Assume
`div B=0` and `partial_t B=-curl E`. In differential forms put `beta=i_B dV` and `e=E_flat`.
Faraday is `partial_t beta=-d e`. Cartan's formula and `i_w beta=-(w cross B)_flat` give

```text
partial_t(X^* beta) = -d X^*[(E+w cross B)_flat],
B_hat = J F^-1(B composed with X),
E_hat = F^T[(E+w cross B) composed with X],
partial_t B_hat = -curl_xi E_hat.                              (1)
```

Thus the magnetic flux uses the Piola density and the loop EMF uses the covector pullback.
Their common source is the actual Faraday law. If `div B` is not zero, (1) additionally returns
`X^*[i_w(d beta)]`; it cannot be omitted as a gauge choice. At a degenerate sweep cap, the
cofactor/form pullback stays meaningful, while inverse-F and moving-volume use require a
regular cap chart or an admitted limit. The accepted FrameTransport source gives the actual
sweep differential, cofactor section and Jacobian clock, not this full continuum theorem.

For material velocity `u`, declare the actual nonideal Ohm return `R=E+u cross B`. Then
`E_hat=F^T[(R+(w-u) cross B) composed with X]`. Ideal material flux conservation is the case
`R=0,w=u` with a regular flow map. Resistive MHD has `R=eta_res j`, with electrical resistivity
`eta_res`; constant permeability gives magnetic diffusivity `eta_m=eta_res/mu_0`. Hall, electron
pressure/inertia, anisotropic conductivity, collisions and radiation retain their own closures.
`j dot (j cross B)=0` makes Hall deflection different from Joule heat. A spatial or frame rechart
does not establish reconnection or a material change.

For an ideal material flow `Phi_t` with `Phi_0=id`, (1) gives the Cauchy transport formula
`B(t,Phi_t(a))=J_t(a)^-1 D Phi_t(a) B_0(a)`. Incompressibility gives `J_t=1` and therefore
the parent-announced item376 relation `B(Phi(a))=D Phi(a)B_0(a)`. This composes the actual
sweep derivative and the initial magnetic flux. A prescribed incompressible velocity supplies
kinematic induction; determining that velocity from Lorentz stress, energy and the particle/fluid
response still owes self-consistent back-reaction. Smooth invertible flow is a load-bearing
hypothesis, not a consequence of local conservation alone.

For a swept label chart whose initial map is not the identity, keep its initial cofactor:
`B(t,X_t(xi))=J_t^-1 F_t [J_0 F_0^-1 B(0,X_0(xi))]`. On the regular admitted domain the
material flow is `Phi_t=X_t composed with X_0^-1`, so `D Phi_t=F_t F_0^-1` and its volume
ratio is `J_t/J_0`. Item376's deformation gradient is this relative derivative, not the
bare derivative of a dimensioned initial section chart. This is the exact initial-frame
operand required when the accepted tube/egg differential consumes that induction relation.

For a declared vector potential `B=curl A`, `E=-partial_t A-grad phi`, magnetic helicity has

```text
h=A dot B,   j_h=phi B+E cross A,
partial_t h+div j_h=-2 E dot B,
h_hat=J(h composed with X),
j_h_hat=JF^-1[(j_h-h w) composed with X].                      (2)
```

The complete cap/side flux remains. `A->A+grad chi` changes the helicity integral by
`integral_boundary chi B dot n`; gauge independence needs its declared boundary conditions
or relative-helicity construction. Multiply connected regions also retain magnetic fluxes,
potential periods and cut choices. Matching reference normal flux does not silently select
those harmonic data. Helicity conservation alone is weaker than field-line topology preservation.

## The kinetic/field bridge supplies the physical finite-c current

In a declared inertial Minkowski chart, take nonnegative species distributions `f_s(t,x,p)`,
positive mass, and sufficient decay to make the momentum-tail flux vanish. A finite momentum
cut retains its additional boundary sources in both moment equations below. Put
`epsilon_s(p)^2=m_s^2 c^4+c^2|p|^2`, with the positive energy branch and `c>0`, and
`v_s=c^2 p/epsilon_s`. Relativistic Vlasov transport with a declared collision/reaction operator is

```text
partial_t f_s+v_s dot grad_x f_s
  +q_s(E+v_s cross B) dot grad_p f_s = C_s,
rho_e=sum_s q_s integral f_s dp,
j=sum_s q_s integral v_s f_s dp.
```

Multiplying by `epsilon_s`, integrating in momentum, and using
`grad_p epsilon_s=v_s` gives `partial_t e_kin+div S_kin=j dot E+Q_C`, where
`e_kin=sum integral epsilon_s f_s dp`, `S_kin=sum integral epsilon_s v_s f_s dp`, and
`Q_C=sum integral epsilon_s C_s dp`. Rest energy is included. With fixed vacuum coefficients
and all plasma currents included, Maxwell has `e_EM=(epsilon_0|E|^2+|B|^2/mu_0)/2`,
`S_EM=E cross B/mu_0` and the complementary `partial_t e_EM+div S_EM=-j dot E`.
The total therefore keeps `Q_C` and all external/radiative/reaction
exchange. Collisions conserve total energy only when their actual operator says so.
Dispersive or changing material excitation carries its own stored energy and constitutive work.

The same calculation with `p` gives the signed material impulse source
`rho_e E+j cross B+sum integral p C_s dp` and momentum flux `sum integral p tensor v_s f_s dp`.
Adding field momentum requires Maxwell stress. These are the collision impulse operands;
an arbitrary velocity reset or scalar phase reading is not that impulse.

Since `|v_s|<=c`, positivity gives `|S_kin|<=c e_kin`. The existing Maxwell energy cone gives
`|S_EM|<=c e_EM`, hence `|S_total|<=c e_total`. A causal-domain conclusion additionally uses
the local balance, source support, initial/boundary data and sufficient solution/trace regularity.
The algebraic flux bound alone is not that conclusion. Strong gravity instead carries the
spacetime metric, covariant kinetic equation and total stress-energy balance.
Quasistatic resistive MHD and its parabolic magnetic diffusion are different admitted limits;
the shared pullback does not transfer Maxwell's finite-c domain to that diffusion law.

Every actual scalar balance `partial_t e+div S=s` uses the same swept receiver:
`e_hat=J(e composed with X)`, `S_hat=JF^-1[(S-e w) composed with X]`, source `J(s composed with X)`.
In fixed physical momentum components its tensor analogue is
`Pi_hat=(Pi-P tensor w)cof F`. A further moving/coarse read returns its own chart-rate and
intertwining defect. The physical speed cone is also carried: a reference characteristic obeys
`|F xi_dot+w|<=c`, not a flat reference-chart speed bound obtained by dropping metric and shift.

## Gas, occupation, interactions and emulation remain one operator question

Targeted laboratory recovery distinguishes the source passages. `THEORY/59_THE_IDEAL_GAS_LAW`
opens with Brandon's particle-count/coarse-grain lens; its subsequent word-gas identifications
are model interpretations, not a physical gas equation of state or simulator certificate.
`FORMULA` at its heat/stress-energy passage retains the actual plasma/EM exchange
`F^(nu lambda)J_lambda` and their total stress-energy. The direct old simulation request was
checked privately; none of the private log output is copied into this record or sent to peers.
The public August 31 many-body record and September 12 Fermi-gas-emulation section supply the
recoverable physical-simulator scope and the Van Houcke et al. interacting-gas reference.

Current `HolonicFermionicOccupation` has the finite addressed occupation carrier and CAR;
`HolonicFermiHubbard` has link hopping plus returned adjoint, on-site interaction, Hermiticity,
number sectors and a bond-current receiver. Those are real microscopic operator constraints.
They do not implement a continuum unitary gas or certify a quantum runtime. `HolonicSimulationCertificate`
keeps the Hamiltonian, observable, cutoff, method and decomposed error/assurance; the emulator
still owes its actual dynamics/clock/receiving maps and calibration.

A kinetic occupation per single fermionic mode has its own normalization and range `0<=n<=1`.
Fermi–Dirac equilibrium and Pauli-blocked collision factors require the actual statistics and
interaction law; classical Vlasov by itself is not a many-body quantum emulator. Taking density,
momentum, stress or energy moments leaves higher moments and correlations. An NS/MHD gas closure
must account for them through its admitted collision/scale/constitutive limit and residual.
The common join is therefore microscopic transport -> declared coarse receiver -> residual
feedback -> contemporary material response, with `q_dot` and `qA-A_c q` retained. Shape, a long
aeon, a shared complex notation or a word-particle analogy does not discharge that operator join.

## The announced public families attach by actual operators and their remainders

[open] The parent supplied these catalogue scopes; this lane has not
checked their manuscripts. Each arrow below requires that source's actual regime, interval,
partition and bound. It is a consuming map, not a new common physics law.

Family364's Newtonian particle -> Boltzmann/fluctuation passage takes an empirical or marginal
receiver of the particle current. Two-particle correlation and the fluctuation field survive
the one-particle face. Its regular kinetic interval and scaling are part of the source; the
Boltzmann collision operator is not obtained by discarding that residue on a long clock.
The resulting kinetic current then enters the momentum/energy receivers above.

Family275's spin exchange -> localized fermion hopping -> continuum Coulomb-energy compiler
joins the existing occupation, link Hamiltonian and bond-current owners through a declared
sector map. For a finite admitted isometry `V`, the exact compressed Hamiltonian and omitted
passage are `H_eff=V* H_micro V` and
`H_micro V-V H_eff=(I-VV*)H_micro V`. The latter must vanish or have its actual bound before
that compression preserves dynamics. The continuum compiler additionally keeps its regulator,
interaction and omitted-mode energy budget; equality of a finite energy face is not that limit.

Family228's tetrahedral cluster interactions -> macroscopic free-energy corner provides a
geometric configuration receiver coupled to its actual interaction/thermal measure. A corner
keeps one-sided or plural effort readings and the eliminated configuration fibre; a single
smooth derivative must not replace it. Geometry alone does not supply the free energy.

Family267's Bose coherence through a common bath carries the joint state and shared interaction.
If its actual evolution generator is `L`, the local receiver `q=Tr_other` returns
`q L(rho)-L_local(q rho)`, including cross-correlations and bath closure. The occupation
algebra is its Bose algebra; the fermionic CAR owner is not substituted for it.

Family363's announced rough kinetic nonuniqueness despite conservation and entropy marks the
admission boundary of (1): those faces alone do not select a unique smooth invertible flow.
Retain the admitted solution/closure fibre; do not manufacture a unique `Phi` by taking a
conserved scalar as complete state. In a differentiable admitted chart the complete common
receiver defect is `partial_t q(x)+Dq(x)A(x)-A_coarse(q(x))`; outside that chart its weak or
plural relation must be supplied by the source.

The parent-supplied [Feynman 1982 simulator reference](https://doi.org/10.1007/BF02650179) and
[modern Fermi–Hubbard simulator reference](https://www.nature.com/articles/s41586-025-09112-w)
ground the physical emulator question; their article-specific results remain with the public
review. The exact emulation obligation is an actual target/apparatus dynamics intertwiner,
clock and observable decoder, or its complete bounded residual. This attaches directly to
`HolonicSimulationCertificate` and the existing Hamiltonian/current owners, without claiming
a runtime simulator or transplanting an authored physical answer into HNN learning.

## Proper clocks and curvature across grains

October 7 follow-on. [project-postulate; direct-source recovered] The latest directly read
Claude messages ask for Lorentz dilation and graining, receiver axes of time, singularities,
continuing space-time fabric and lightning. The parent then supplied Brandon's direct correction:
the target includes real curvature of microscopic separation, motion and exchange, compared
across grains with celestial collisions over aeons/epochs. Reducing that target to a force-magnitude
comparison loses the intended question. Private source text stays outside this record.
[agent-inferred] The consuming correction is to carry the physical metric and proper clock into
the same moving current, then state the maps to material, configuration and phase geometry.
Microscopic size alone is not an approximation hypothesis.

The existing source owners are `Physics/Spacetime/{Boost,NonClosedClock,StressEnergy,Einstein}`,
`ObserverBoundaryCurrent`, `Geometry/{Motion,HolonicClockedPantographicSwing}`,
`Aeon/Clock/{Reading,Epoch}`, and `Transport/{WorldTube,ChangingReceiver}`.
The exact Rust mirror is `physics/spacetime`.
`Boost` already proves relative inertial clock readings and their undivided rate;
`NonClosedClock` proves finite redshift and Sagnac returns. `ObserverBoundaryCurrent` and
`StressEnergy` retain receiver deformation work. The pantographic proper-time edge retains a
metric/frame witness; that witness is supplied, not constructed by its invariance theorem.
`Einstein` explicitly leaves a nontrivial continuum metric/connection/source realization open.
The July 19 separation/Jacobi record and September 28 loop-curvature record already distinguish
physical curvature, branch transport and shape/phase connections. This join consumes those
owners rather than proposing another geometry library. The failure it prevents is carrying a
located missing metric, clock or closure term unrepaired into the next consumer.

### The full spacetime sweep supplies the proper clock

[proved-derived under the stated smoothness, timelike and chart hypotheses; no new kernel claim]
Let the actual spacetime have Lorentzian metric `g`, signature `(-,+,+,+)`, and use the regular
sweep `Y(t,xi)=(t,X(t,xi))`. Write `F=D_xi X`, `J=det F>0`, `w=X_t`, with physical fields evaluated
at `Y`. The full pulled metric `G=Y* g` is

```text
G_tt = g_tt+2 g_ti w^i+g_ij w^i w^j,
G_ta = (g_ti+g_ij w^j) F^i_a,
G_ab = F^i_a g_ij F^j_b,
sqrt|det G| = J (sqrt|det g| composed with Y).                 (3)
```

The spatial block alone omits the swept clock and time-space coupling. In the admitted
lapse/shift chart `ds^2=-N^2 c^2 dt^2+h_ij(dx^i+beta^i dt)(dx^j+beta^j dt)`, a path with
reference rate `xi_dot` has physical velocity `v=w+F xi_dot` and

```text
alpha=d tau/dt=sqrt[N^2-h(v+beta,v+beta)/c^2] > 0.             (4)
```

Thus both shift and relative motion enter the clock. This is a physical timelike condition,
not a chosen positive program tick. Under a monotone relabeling `t=t(lambda)`, `d tau/dlambda`
acquires `dt/dlambda` and the integral of proper time is unchanged. A Lorentz frame action
carries the metric, normalized velocity and event together, as `Boost.clockReading_boost`
already requires. Distinct physical paths can instead have different accumulated proper times.
Comparing separated receivers needs their actual signal/transport correspondence; simultaneous
coordinate labels do not supply it. Acceleration changes the path and receiver congruence;
spacetime curvature is the Riemann tensor of the declared connection.

The owner's actual null-frame boost is `(u,v)->(k u,k^-1 v)` for positive Doppler ratio `k`.
It preserves `u v`; `chi=log k` is its rapidity, while the inertial elapsed-clock reading uses
`gamma=(k+k^-1)/2=cosh chi`. A positive amplitude ratio can label that one-parameter
representation through a declared decoder. Its bare logarithm or an arbitrary tick-rate ratio
does not thereby supply the normalized observer or the elapsed-clock factor `gamma`.

For example, the Rindler metric with `N=1+a x/c^2>0`, `h=I`, `beta=0` is flat, while the static
clock form has `d(N dt)=(a/c^2) dx wedge dt`. Its nonclosed clock and relative rate are real
receiver geometry even though `R(g)=0`. The finite `NonClosedClock.static_reading/redshift_rate`
read that form; they do not by themselves construct a spacetime Riemann tensor.
`Aeon/Clock/Reading.Clock` is a closed cochain, the hypothesis permitting descent through
homotopy/homology. A nonclosed physical clock instead keeps the boundary/production return
through `NonClosedClock` and `Aeon/Production/HodgeTime`. `Epoch.ring_count_is_flux` reads actual
section arrivals and the retained winding/phase; its owner-crossing identification requires
the stated transversality. A duration label or program iteration does not supply that section.
Two forms with `omega_R wedge omega_R' != 0` give independent covector directions. Identifying
them with local coordinate differentials needs exactness, or declared integrating factors and
their integrability conditions; independence alone does not construct a two-parameter clock chart.
Epoch crossing flux pairs the actual section-dual cochain with the passage. Its identification
with a surface integral of `d omega_R` would need an additional specific law; that curvature flux
can vanish while section crossings accumulate.
At a null path
`alpha=0`, massive proper-time division is unavailable. At a pinched spatial chart `J=0`,
(3)'s inverse-chart use is unavailable. Curvature divergence or geodesic incompleteness requires
its actual invariant/path analysis; neither degeneration alone proves it.

### The same current now carries covariant receiver work

Use `c=1` for tensor contractions in this paragraph, so a physical receiver is future timelike
with `g(U_R,U_R)=-1`. Take a symmetric total stress-energy `T` with actual balance
`nabla_mu T^(mu nu)=f^nu`. Its energy reading is `T^(mu nu) U_R,mu U_R,nu` and its current is
`K_R^mu=-T^(mu nu) U_R,nu`. The complete receiver source is

```text
s_R=div_g K_R=-f^nu U_R,nu-T^(mu nu) nabla_(mu U_R,nu),
partial_t(sqrt|g| K_R^t)+partial_i(sqrt|g| K_R^i)=sqrt|g| s_R,
rho_hat=J [(sqrt|g| K_R^t) composed with Y],
k_hat=J F^-1[(sqrt|g| (K_R^space-w K_R^t)) composed with Y],
partial_t rho_hat+div_xi k_hat=J[(sqrt|g| s_R) composed with Y]. (5)
```

The density on a slice is the current contracted with that slice's normal; it equals the
receiver's energy density only with the corresponding observer/normal identification. In the
flat inertial energy chart (5) reduces to the earlier `J e` and `JF^-1(S-e w)` equation. A
conserved total `T` still leaves the observer deformation term; a Killing receiver removes it.
This is precisely the existing `ObserverBoundaryCurrent` contraction and `StressEnergy` heat/
pressure-work consumer, with the covariant derivative supplied by an actual geometric realization.
Its finite source theorem does not prove this continuum integral transport. Domain, trace,
regularity, caps and collision/radiation returns remain required. In particular it adds no
signed NS work bound and removes none of the local pressure or mean/volume returns.
A complex NS/Fourier carrier needs its actual real physical observer/decoder before it supplies
`U_R`. The positive spatial metric used in its Hodge/curl read and the full Lorentzian metric in
(3) have different tensor roles; their declared slice/observer map connects them.

The electromagnetic join can be stated without a flat component shortcut. With the actual
field two-form `F_EM` and excitation `H_EM`, Maxwell has `dF_EM=0` and `dH_EM=J_charge`.
Pull `F_EM`, `H_EM` and the charge three-form by `Y`; `d` commutes with that pullback. Vacuum
excitation uses the Hodge star of `g`, and its pullback uses that of `G`. Material excitation
uses the actual constitutive operator instead. Equation (1)'s flux/EMF operands are the
flat-slice components of this form transport. A curved kinetic realization likewise keeps the
mass shell, invariant momentum measure and geodesic/EM force on that shell. With `c=1` and
proper parameter `sigma=tau/m`, its characteristics are
`dx^mu/dsigma=p^mu`,
`dp^mu/dsigma=-Gamma^mu_ab p^a p^b+q F_EM^mu_nu p^nu`,
`g(p,p)=-m^2`, plus the declared collision operator. Omitting `Gamma` is a controlled flat
realization or approximation, not a consequence of particle size.

### Separation, material response and phase have actual connecting maps

Fix `R(A,B)C=nabla_A nabla_B C-nabla_B nabla_A C-nabla_[A,B] C`. For an admitted smooth
family with commuting tangent `U` and variation `xi`, whose paths obey `nabla_U U=a_force`,
variation gives the actual nearby-motion equation

```text
D_tau^2 xi=-R(xi,U)U+nabla_xi a_force.                        (6)
```

Here `nabla_xi a_force` is the total covariant variation along the family. For `a_force(x,U)`,
write it explicitly as `(nabla_xi^x a_force)|_U+(D_U a_force)[D_tau xi]` with the horizontal
derivative taken using the same connection. For `a_force=(q/m)F_EM^sharp U`, it is
`(q/m)[(nabla_xi F_EM^sharp)U+F_EM^sharp D_tau xi]`. Equation (6) connects physical curvature,
separation and exchanged force at the same locus. Gravitational coupling additionally requires
the actual `G_Einstein+Lambda g=kappa T` source/connection realization; EM stress contributes
to `T`, while an EM force is not itself a Riemann tensor. Weyl tidal curvature can survive a
vanishing local Ricci/source face. Relative-path linearization retains it.
Equation (6) keeps the longitudinal separation component. On a family parametrized by each
path's proper time with `g(U,U)=-c^2`, `g(U,D_tau xi)=0` and
`d_tau g(U,xi)=g(a_force,xi)`. An orthogonal projection `P=I+c^-2 U tensor U_flat` therefore
adds its actual `D_tau P` terms for accelerated paths. A transverse-only reading cannot
silently discard this clock/acceleration coupling.

A nondegenerate material surface's induced curvature is connected to ambient curvature by the
Gauss equation, using `R_abcd=g(R(e_a,e_b)e_d,e_c)` and orthonormal normals of signs `epsilon_normal`:
`R_surface=R_ambient restricted+sum_normal epsilon_normal (II_ac II_bd-II_ad II_bc)`.
Its second fundamental form therefore contributes even in flat ambient spacetime. On a regular
full-dimensional Euclidean rechart the pulled spatial metric `F^T F` is intrinsically flat;
a curved section/boundary and a bent centreline still have their own geometry. Time-changing
constitution separately retains `G_dot` work through `Motion.energy_rate_moving_metric`.

For an autonomous conservative mechanical configuration metric `M`, potential `V`, and fixed
energy `E>V`, the Jacobi metric `M_J=2(E-V)M` makes the same unparameterized mechanical paths
geodesics, with `ds_J/dt=2(E-V)`. This is a concrete force-to-configuration-geometry map under
those hypotheses. It changes the metric and clock of that configuration problem; it does not
identify its curvature with physical `R(g)`. At `E=V` this chart degenerates and the actual
mechanical path must be retained. Dissipative or pumped material owes its extended law rather
than silently satisfying the conservative hypotheses.

The existing loop-curvature record supplies the stationary isotropic Fermat metric `n^2 h`.
Its covariant nondispersive instance is another physical map: a locally isotropic medium with
rest index `n>0` and unit timelike `U` has, in `c=1` units and its geometric-optics regime, inverse
optical metric `g_opt^(mu nu)=g^(mu nu)+(1-n^2)U^mu U^nu`; the eikonal obeys
`g_opt^(mu nu) k_mu k_nu=0`. Material gradients can give real optical curvature in flat
spacetime. Dispersion, plasma anisotropy and changing excitation require their actual
frequency-dependent characteristic relation; one nondispersive optical metric is not that
closure. Proper clocks use `g`, and optical phase/group/front readings keep their own operators.

Quantum transport consumes those clocks and connections. For an admitted unitary proper-time
Hamiltonian and moving unitary basis `W(lambda)`, its carried generator is
`H_lambda=(d tau/dlambda) W* H W-i hbar W* W_dot`. A rest eigenbranch has phase
`-mc^2 tau/hbar`; an internal transition reads its energy difference, and a common phase may
cancel at the receiver. Berry curvature belongs to the actual projected eigenbundle, with its
gap and adiabatic regime. If a spacetime spin structure and spin connection are supplied,
`[nabla_mu^spin,nabla_nu^spin]=(1/4)R_mu nu ab gamma^a gamma^b` connects spacetime curvature
to spin transport; EM coupling adds its own field-curvature term. Finite CAR/Hubbard owners
alone do not instantiate this covariant field theory. These are concrete connecting equations
with declared operands; no universal equality of the curvatures has been supplied.

### A grain comparison must preserve dynamics or carry its remainder

The discrete-to-physical connection map can be stated in the existing
`Foundation/ConnectionLineage.RouteScalePassage`. For the two actual complete route transports,
let `Phi T_left=T'_left Phi` and `Phi T_right=T'_right Phi`. In that owner's target-based
order `R_f=T_right T_left^-1`, `R_c=T'_right T'_left^-1`, its proved consumer is

```text
Phi R_f = R_c Phi.                                           (9)
```

No inverse of `Phi` is used. An injective `Phi` transfers coarse flatness to fine flatness;
a surjective `Phi` transfers fine flatness to the whole coarse receiver; a bijective `Phi`
makes flatness equivalent. `HolonicComposition.boolToUnitRouteScale` is the actual counterexample
where a quotient erases a nontrivial fine return. `ContinuingTube.flat_near_curved_far` instead
compares different admitted near/far circuits; it does not prove one circuit changes physical
Riemann curvature under an invertible rechart. `Holon/Complex.block_cell_curvature` supplies the
connection-incidence face `(hol-I)phi` even for noninvertible block transports; using inverse-route
holonomy requires its separate invertibility hypotheses.

To identify an HNN/configuration return with physical parallel transport, `Phi` must intertwine
the actual physical frame connection along the corresponding paths; a form-preserving frame map,
clock correspondence, boundary/loop admission and the appropriate smooth small-loop realization
are additional operands. Without them (9) is a real connection law with an uninstantiated physical
decoder. In an additive receiving chart the complete defect `Phi R_f-R_c Phi` remains at the
consumer when the intertwining fails; a general receiving fibre retains the two actual route faces.

Let an actual correspondence pair source and receiver clocks and admit
`a_R=d tau_f/d tau_R>0`. For source dynamics `dx/dtau_f=A_f(x)` and moving read
`y=q(tau_R,x)`, the complete target-clock defect is

```text
dy/dtau_R=A_coarse(y)+epsilon_R,
epsilon_R=partial_tau_R q+a_R Dq A_f-A_coarse(qx).            (7)
```

This consumes `ChangingReceiver.actual_moving_chart_clock_action` and `moving_receiver_rate`;
`FluidReceiverClosure` retains the unresolved bilinear interactions at that read. Physical
curvature, kinetic moments, phase and clock do not disappear when a coarse face is chosen.
An exact ratio of clock ticks is lawful; its physical Lorentz identification needs the metric/
velocity/interval witness. Higher clock jets follow the same chain rule, including rate derivatives.

For fixed scale units `xi=L zeta`, `tau=T s` in a carried frame, (6) reads
`D_s^2 zeta=-T^2 R(zeta,U)U+(T^2/L) delta a_force`. Similarity of nearby motion therefore
compares the complete scaled operators, not only the apparent shape. Among its required groups
are `T^2 ||R(.,U)U||`, `||R|| L^2`, force-gradient/response rates times `T^2`, and `v/c`.
These norms use the declared observer tetrad and material/phase norm; an indefinite bilinear
square is not a positive norm bound.
A particle/plasma/fluid limit also carries its actual `Kn`, Reynolds and magnetic Reynolds
ratios, screening/collision scales and quantum action ratio `hbar/(P L)` where admitted.
Transport of these groups through the actual `Phi` is a necessary comparison. Equal group values
alone do not supply (9), preserve holonomy, or control a fibre erased by `Phi`. Global/boundary
data and nonlinear operator equivalence or controlled residual still owe their own check. Classical stellar fluid
and quantum microscopic material need not preserve them under a spatial rescaling. Uniform
rescaling of a complete metric can preserve geometric structure while changing proper lengths
and clocks; holding physical units/material constants fixed makes it a physical scaling question.

A flat-clock approximation can have an exact receiver error budget. Along the same admitted
path `gamma(lambda)`, put `V_gamma=d gamma/dlambda`, the full spacetime tangent. Let
`alpha=sqrt[-g(V_gamma,V_gamma)]/c` and `alpha_0=sqrt[-g_0(V_gamma,V_gamma)]/c` both be at least
`alpha_*>0`. If `r(lambda)>=|(g-g_0)(V_gamma,V_gamma)|/c^2`, then

```text
|alpha-alpha_0|=|(g-g_0)(V_gamma,V_gamma)|/[c^2(alpha+alpha_0)]
             <=r/(2 alpha_*),
|tau-tau_0|<=integral r/(2 alpha_*) dlambda.                   (8)
```

This bound is for the declared common path, not a replacement for controlling path deviation
through (6), collision/closure error or spin/field transport. For a constant energy branch its
phase error is at most `|E_branch|/hbar` times that clock bound; an interferometric path or internal
transition keeps the corresponding relative action and cancellations. Small spatial metric error
can still accumulate on a long clock or a sensitive phase receiver. A controlled approximation
must bound the relevant errors at that grain. Equation (8) supplies a concrete obligation rather
than assuming either that GR dominates every microscopic read or that it disappears there.

[open] Brandon's proposed cross-grain common organization is a productive geometry/transport
hypothesis. Equations (3)–(9), the constitutive and phase maps, and their actual defects state what
must commute or be bounded for a particular instance. They do not provide a new continuum
Einstein solution, quantum-gravity completion, or universal star-to-particle similarity theorem.

## Contemporary concentration, Ricci necks and resonant response

[source-recovered] Brandon's recent remarks give a precise context for this join. On October 7
at 04:54:33 UTC he allowed singular events to destroy existing structure and behaviour; at
21:00:26 UTC he asked to understand singularities through dilation and graining beyond an
absolute point picture. His October 5, 20:23:57 UTC remark explicitly connects curvature between
modes, singularities, music and spectra. The October 7, 22:12:39 UTC clarification supplied by
the delegator makes the positive proposal contemporary concentrating regions guiding local
curvature and resonant interaction. These are authored paraphrases; no private log output is
retained here. They support finite persistent concentration as well as destructive blow-up.

The recovered July 19 record `THE_RICCI_TRACE_CHANGES_THE_RECEIVER_THE_SINGULAR_NECK_REBASES_THE_BODY`
already joins `Ric(u,u)=sum_a h(R(e_a,u)u,e_a)`, actual Ricci metric evolution,
blow-up/rebase and controlled neck surgery. Its historical vocabulary does not change the
current elementary objects. Its concrete distinction survives: smooth metric evolution keeps
the topology; surgery requires its actual gluing and cap law. The current `Geometry/Ricci`
owner supplies exact rational three-cell diffusion, with its aperture and collapse defect;
the atlas correctly limits its Ricci interpretation to a shadow with no continuum metric or
Ricci tensor constructed.

[agent-inferred; conditional join] The strongest existing-law reading of the music proposal is
an actual tube/receiver geometry `h` and constitution `Theta` determining incidence and material
forms `C(h,Theta),K(h,Theta)`, hence modes `K phi=omega^2 C phi`. Their motion carries port work
and material covectors that can reshape the contemporary geometry and constitution.
`Compression/Core/Resonance.mem_modeSpace_iff_response`, `resonant_drive_rides` and
`motion_work_ledger` already consume the actual incidence forms. Zero holding effort for an
existing harmonic mode is a sustained-motion statement; founding that motion from rest still
needs its work. A phase, force, pump and damping law are actual operands of continuing resonance.

On a fixed reference material chart, let differentiable real symmetric `C>0`, `K>=0`, `D>=0`
on the admitted finite mode space, and let the actual motion satisfy

```text
z_dot=v=C^-1 p,   p_dot=-K z-D v+f,
E_mode=(1/2)p^T C^-1 p+(1/2)z^T K z,
E_mode_dot=v^T f-v^T D v-(1/2)v^T C_dot v+(1/2)z^T K_dot z.  (10)
```

[proved-derived; source-inspected specialization, no new kernel check] The identity follows by
differentiating `C^-1`, cancelling `v^T K z`, and consuming the changing-storage term of
`Holon/Element.PortHolon.energy_balance` with `Q=diag(K,C^-1)`. Its geometry contribution at
fixed `(z,p)` is the covector
`delta_h E_mode[h_dot]=-(1/2)v^T(D_h C[h_dot])v+(1/2)z^T(D_h K[h_dot])z`.
An actual feedback law must pair this covector with the geometry motion and account for the
opposite work, dissipation and sources. The total `C_dot,K_dot` also retain actual material,
pump and incidence changes. A moving mode restriction keeps its connection and projector-rate
returns. Deposition remains change from the comparison covectors that reached that locus.

A possible metric-feedback hypothesis is `h_dot=-2 kappa Ric(h)+Lie_V h+S_modes/material`,
with the clock coefficient `kappa` and symmetric tensor `S` supplied by that actual material/
port relation. Its pure Ricci-flow identification requires the full tensor residual
`epsilon_RF=h_dot-Lie_V h+2(ds/dtau_R)Ric(h)` to vanish on the corresponding receiver clock;
with `kappa=ds/dtau_R`, the displayed hypothesis returns `epsilon_RF=S`.
Equation (10) specifies a work obligation, not a proof that physical stress follows Ricci flow.

The public reader reports that item351's [bounded-scalar blow-up manuscript][ricci351] treats
`S^2 x S^(q+1)`, `q>=10`, with outer scale `ell_out=sqrt(T-t)` and a smaller cap scale
`ell_in=(T-t)^sigma`. These remain manuscript claims, not independently checked here.
When `ell_in/ell_out -> 0`, an outer-scale read alone cannot bound the inner cap's full
curvature or modal work; a uniform cross-scale bound or retained return is needed.
`NavierStokesDynamicRescaling.hasDerivAt_rescaledVelocity` and `rescaled_momentum` already
keep centre, length, amplitude and clock jets in an actual fluid rescaling. Equations (1),
(7), (10) and `ReflectedBoundaryMemory.reflectedResidual_rate` keep relative flux, changing
read, work and interior return. Thus a Ricci-flow singularity can be a precise instance of
Brandon's broader concentration picture. Pure Ricci flow supplies no resonant phase law, and
a finite concentrating region need not already be a finite-time curvature blow-up.

[ricci351]: https://github.com/openai/math/blob/main/preprints/A-closed-Ricci-flow-with-bounded-scalar-curvature-and-finite-time-curvature-blowup-September-24-2026/paper.pdf

### The adjoint, harmonic sector and metric gradient stay declared

[source-inspected reconciliation] For a real factor `F:E->V` between declared inner-product
spaces, at fixed metrics for this variation, put `C=F F*` and define the material covector by
`D ell_C[delta C]=<G,delta C>_HS`. Then
`delta C=delta F F*+F delta F*` gives the factor pullback
`D ell_F[delta F]=<(G+G*)F,delta F>_HS=<2 S F,delta F>_HS`, `S=(G+G*)/2`.
The native `ratio/linear/vector.IntegralMatrix.symmetric_times` actually computes
`(G+G^T)F` in its rational coordinate pairing. `hnn/reference.compose_contact` supplies its
actual producing pulls `C_bar=sum 2 r_bar(w-omega)^T`,
`K_bar=-h sum r_bar(u+h omega/2)^T`, `D_bar=-h sum r_bar omega^T`.
A generic `sum lambda w_dot^T` cannot replace those operands or their signs. With metrics
`M_E,M_V`, the adjoint is `F*=M_E^-1 F^T M_V`; a bare transpose needs its coordinate-pairing
witness. This is a comparison covector pullback. Identifying it with physical stress also
requires the actual strain/metric variation and its power relation; the analogy alone does
not supply Einstein's equation. `ConstitutiveModulation.potential_strain_first_variation`
and `stress_strain_rate_return` are the actual derivative consumers.

`Foundation/HodgeReceiver` declares positive cell weights and their weighted adjoints, and
proves `laplacian_quadratic` and `finrank_harmonic_metric_free`: on fixed incidence, changing
positive weights moves representatives without changing the harmonic dimension. A proposed
Bochner decomposition must first identify this same operator and boundary domain as
`Delta_1=rough+Rcurv`, with `rough>=0` and `Rcurv>=kappa I`, `kappa>0`, in that same metric.
Only then does `<Delta_1 a,a> >= kappa <a,a>` exclude nonzero harmonic `a`. An arbitrary curvature
sign does not supply those inequalities; flat or negative curvature does not guarantee a
harmonic mode. No Forman decomposition is provided by the inspected Hodge owner.

[proved-standard; continuum hypotheses, not a new Lean theorem] On a closed smooth Riemannian
manifold, Perelman's normalized measure is
`dm=(4 pi tau)^(-n/2) exp(-f)dV`, `integral dm=1`, and
`W=integral [tau(R+|grad f|^2)+f-n]dm`. Along
`g_t=-2 Ric`, `tau_t=-1`, `f_t=-Delta f+|grad f|^2-R+n/(2 tau)`, `tau>0`, `Delta=tr Hess`,
its identity is
`W_t=2 tau integral |Ric+Hess f-g/(2 tau)|^2 dm>=0`.
A gradient interpretation must carry the weighted variation, coupled measure, diffeomorphism
gauge and scale normalization; its displayed tensor contains both Hessian and normalization
terms. A task comparison alone does not instantiate this geometric functional.

`NavigatorTraceFaces.unipotentTwo_pow` gives `H^k=I+k N`, `N^2=0`, with unchanged trace and
transfer determinant but a separating source/receiver face. `H-I` detects nonidentity;
rank and Jordan type survive conjugacy. Its raw norm needs the actual receiver metric, carried
under regauging. A shear monodromy is a precise information-loss analogue of a scalar read
hiding growing action; it supplies no Riemann-curvature blow-up or useful-learning verdict.

## Coupled loops retain induction, changing material and work

[project-postulate] Brandon's October 7, 22:34:26 UTC clarification joins a closed current
path to its induced surrounding flux and contemporary medium, then joins winding loops to
helices, knots and tori. The closed spatial path is one part of the participating Holon.
Its currents, fluxes, constitution, field/interior state and clocks participate in the transport.
Brandon's 22:38:03 UTC correction makes the distinction explicit: the structure can close while
particles and energy pass through it. Structural closure imposes no return requirement on each
carrier or reset requirement on the whole coupled state.

The actual existing `HolonicDiscreteInduction.axisFluxLinkage` is `lambda=M I`; its
`inducedAxisEmf_eq_sum_currentDifferences` proves `emf=-M delta I` with fixed coupling and
coordinated orientation covariance. The torus incidence owner's zero pairing of a closed chain
with an exact nodal drop does not set an induced, nonexact EMF to zero. Equations (1) and the
finite Maxwell `PositiveCellHodge.poynting_balance` retain moving-loop flux, source work and
boundary power. The fluid guide already keeps `partial_t(L I)` and `partial_t(C V)` in its
changing channel, including their material-work terms.

[agent-inferred; conditional magnetoquasistatic illustration] In a common declared receiver
clock after actual port/frame transport, admit reciprocal linear reversible magnetic material
and a differentiable symmetric positive definite inductance `L(q,m)`. Here `q` is geometry
and `m` actual material variables; neglecting radiation, propagation delay and hysteresis is
part of this reduction. With current `I`, linked flux `lambda`, driving voltage `V` and
resistance `R>=0`, and all linked source currents in the modeled family, the relation and work are

```text
lambda=L(q,m)I,   lambda_dot=V-R I,
emf_induced=-lambda_dot=-L I_dot-L_dot I,
E_mag=(1/2)lambda^T L^-1 lambda=(1/2)I^T L I,
E_mag_dot=I^T V-I^T R I-(1/2)I^T L_dot I.                  (11)
```

Current produces linkage through the constitutive/field solution; its changing linkage induces
EMF. `ChangingReceiver.moving_receiver_rate` consumes the full product rule, and
`PortHolon.energy_balance` consumes (11) with storage `Q=L^-1`. In this reversible reduction,
geometry receives magnetic force covector `(1/2)I^T(D_q L)I`; its work cancels the geometry
part of the last term in the joined energy balance. Material modulation retains its own
opposite work, storage, heat and sources. A hysteretic or dispersive medium keeps its actual
internal state and response instead of being represented by instantaneous `L(q,m)` alone.
An externally supplied linked flux is a further port: `lambda=L I+lambda_ext` keeps
`psi=lambda-lambda_ext` as the internal linkage, and contributes
`-I^T lambda_ext_dot` to `E_mag_dot` with `E_mag=(1/2)psi^T L^-1 psi`.

For two identical loops with matrix `[[L,M],[M,L]]`, `L>|M|`, equal currents and no drive,
put `ell=L+M`. Each loop satisfies `(ell I)_dot+r I=0`. If `ell(T)=ell(0)`, then
`I(T)=I(0) exp[-integral_0^T r/ell d tau]`: a geometry/material return can leave a different
current, with heat and modulation work accounted by (11). A driven circulation can persist
with through-flow and its explicit balance; a persistent key need not reset the global state.

The helix owner keeps axial carry, and its toroidal material chart requires an actual period or
carry-commutation relation. Closing and embedding winding strands, their gluing and material
frame give the knot/link; shape alone supplies no coupling coefficient. Unlinked coaxial rings
can have nonzero mutual inductance. The finite `HelicityAsLinking` owner reads a declared
crossing population, with physical embedding, normalization and framing owed. A magnetic
decoder on separated thin closed flux tubes instead reads
`H=sum_i SL_i Phi_i^2+2 sum_(i<j) Lk_ij Phi_i Phi_j`, with actual fluxes `Phi_i` and
self-linking data. Gauge-invariant `integral A dot B dV` requires its boundary/gauge conditions
(for example `B dot n=0`); open tubes keep a relative-helicity reference and boundary return.
Ideal conservation and reconnection retain their actual material/field hypotheses.

For aqueous conduction, plasma or vacuum propagation, the fluid guide's actual charge, total
current, Maxwell field, mechanical/thermal and constitutive state supplies the fuller object.
Permittivity, permeability, conduction and collision response belong to that material and its
frequency/clock regime. The port and moving-tube balances continue to apply without collapsing
those distinct responses to the illustrated inductance matrix.

### Through-flow on persistent winding structure can mark epochs

[agent-inferred; exact conditional section read] On a locally admitted annular section with
unit axial normal `n`, transverse position `r`, material velocity `w=Omega n cross r` and
fluid velocity `u=U n+omega n cross r`, the mass-current read is
`(rho u-rho w) dot n=rho U`. The rotating structure and swirl coexist with axial passage;
a particle need not finish a turn before leaving. The actual pressure, momentum, material
and field laws determine `U,omega,Omega`. This consumes the same relative section current
`j-rho w` of FrameTransport and (1), with their actual area/cofactor and clock conversion.
Energy uses its own stress/Poynting/thermal current; particle count its number current; action
its declared action or phase transport with energy-times-time units.

The screw owner supplies rotational plus axial motion and the frame connection reorients
its directions; the changing mode basis keeps the connection term already displayed above.
Material rotation, orbital motion, a parametron phase and intrinsic particle spin each keep
their own state, angular-momentum/torque or phase law. Their coupling requires the actual
material/field relation. The persistent organizing region can guide through-flow, modes and
induction without being a closed carrier orbit or a curvature blow-up.

The existing `Aeon/Clock/Epoch` owner cuts an aeon at the actual receiver's section, certifies
the partition and requires transversality for its crossing count. Thus formation, splitting,
reconnection or a detected stability change can mark an epoch when admitted as that receiver's
section/occurrence; recurrent crossings can also mark epochs while one concentrating region
persists. On a smooth configuration section `c_R(tau,z)=0`, the actual crossing rate is
`partial_tau c_R+D_z c_R z_dot`; a nonzero rate is the local transversality witness.
A topology-changing occurrence additionally keeps its gluing, material and flux returns.
An aeon remains a causal span between occurrences; its elapsed reading belongs to its clock.
One organizing region may persist across many epochs or aeons, and changes elsewhere may cut
them. There is no one-to-one identification of singularity, epoch and aeon, nor a prescribed
rotation or program-selected duration required by this construction.

### The continuing native wave crosses material and frame changes

[source-inspected] `hnn/word/continuation.ContactCut::continue_deposited` is an actual consumer:
it opens `Word::continuing` on the reached `EndChange` with zero new injection and the carried
`next_tick`. Storage/arriving waves, contact states and resonator states continue; pump phase
uses that clock. `ContinuationReceipt` separates same-state deposition work from the opening
difference. The consumer admits contact-factor changes in the same coordinates and verifies
that ring, pump, surface and geometric coupling declarations are preserved. It does not yet
instantiate a changed frame, source map or receiving map. The inspected test consumer checks
state/clock continuity and balance, and separates an unresolved coordinate reading from actual
material change; no new test run is claimed here.

[proved-derived; finite conditional consumer identity] At one event let `z` be the full reached
wave/mode state and let an admitted invertible `R` carry it to a complete successor chart. A physical
decoder must witness `D_new R=D_old` for a rechart of that same field. For symmetric storage
forms `Q_old,Q_new`, the exact storage change at that event is

```text
z_new=R z,
W_commit=E_new(R z)-E_old(z)
 =(1/2)z^T(R^T Q_new R-Q_old)z.                            (12)
```

The current consumer is `R=I`; `HNN/Ring.ring_material_commit_work` owns its capacity/stiffness
specialization. A pure rechart has `Q_new=R^-T Q_old R^-1`, hence zero work; a real material or
geometry change keeps the full difference in (12) when this state/chart is complete. This
instantaneous storage difference does not include power crossing ports during a nonzero passage.
If a carried chart returns `R z+epsilon`,
its additional opening difference is `(R z)^T Q_new epsilon+(1/2)epsilon^T Q_new epsilon`.
It remains separate from material work, as in the current receipt. The actual `R` acts on each
typed field/port component, preserving the effort-flow pairing; the tube's density/cofactor
and covector transformations cannot be replaced by one arbitrary common matrix.

There is a concrete basis construction at a common admitted fine-field cut. For positive receiver
metric `M` and full-column-rank successor decoder `D_new`, put
`G_new=D_new^T M D_new`, `A_new=G_new^-1 D_new^T M`, `R=A_new D_old`.
Then `A_new D_new=I` and the complete field is
`D_old z=D_new R z+h`, `h=(I-D_new A_new)D_old z`.
`Holon/Element.KineticFace.energy_split` consumes precisely this metric projection: its
horizontal lift is `D_new`, its face metric is `G_new`, and its hidden field is `h`.
With equal decoder images `h=0`; otherwise this vector field/mode contribution keeps its actual
propagation and phase. It is not the remainder of a rounded material coefficient. A changed
physical domain first requires its actual typed field transport before this basis read.

[proved-derived; source-scope correction, October 8] A projection metric does not automatically
equal the physical storage form. Let `W_old,W_new` be the actual symmetric ambient storage
forms, `Q_old=D_old^T W_old D_old`, `Q_new=D_new^T W_new D_new`, and
`y=D_new R z`. Here the old decoder represents the complete old field; after an admitted typed
field transport `S`, use `R=A_new S D_old` and `h=(I-D_new A_new)S D_old z`.
At a common unchanged fine-field cut `S=I`; in either case the complete successor field is
`y+h`. Expanding its actual storage gives

```text
E_new(y+h)-E_old(D_old z)
 = (1/2)z^T(R^T Q_new R-Q_old)z
   + y^T W_new h + (1/2)h^T W_new h.                       (12a)
```

The cross term has ambient operands `y,h`, not a modal vector paired directly with `W_new`.
For the projection just constructed, `D_new^T M h=0`. Only an additional identification
`W_new=M`, or a proved `W_new`-orthogonality relation, removes the actual storage cross term.
When `W_new=M`, the existing `KineticFace.energy_split` already supplies the full modal plus
hidden energy, and `hidden_energy_nonneg` supplies its sign. A different or signed storage
form keeps both terms in (12a). If the old field also has a retained hidden part, its old
cross and hidden energies must likewise be subtracted. The projection's `R` need not be
invertible; retaining `h` is what makes this field identity complete.

Thus (12) applies to a complete transported state or to its represented contribution; (12a)
is the complete projected-field receipt. The inspected native `continue_deposited` reads the
same full `EndChange` through both `PowerForm`s and checks their whole storage difference.
There is no source evidence that this native same-coordinate consumer discards `h`; the
additional obligation is at a prospective change of decoder or geometry.

On a regular passage, `Holon/Element.PortHolon.energy_balance` requires the actual admitted
motion and gives `E_dot=P_ports+P_active-D+(1/2)Psi^T W_dot Psi` for the full state. Its
integral, with the storage changes at actual material commits and the separate executed
opening/chart/split terms, supplies the full passage receipt. At a moving spatial receiver
the boundary port is read from the actual local law as
`P_boundary=-integral_boundary (j_E-e w) dot n`; its pullback is
`JF^-1[(j_E-e w) composed with X]`. All side and cap returns remain. The abstract port pairing
and this relative-flux expression are realizations of the same boundary power, to be matched
rather than added twice. In particular, a receiver-metric derivative cannot be declared
material pumping without its actual motion/constitution balance. The existing Maxwell
`poynting_balance` retains both its co-curl boundary power and the electric-current work;
`boundaryPower_materialCoCurl_eq_zero` closes that port only under its declared closed-carrier
adjoint relation. Metric projection alone closes no through-flow or pressure-work port.

For a smooth invertible chart `z_R=R(t)z`, the producing linear law `z_dot=A z+B u` becomes
`z_R_dot=(R A R^-1+R_dot R^-1)z_R+R B u`. This is the connection term consumed by
`ChangingReceiver.moving_receiver_rate`, with actual clock-rate conversion where required.
An actual receiving map has derivative `P_dot z+P z_dot`; an unchanged physical read obeys
`P_new R=P_old`, while a genuinely moving read retains its difference.

For the same admitted linear constitutive passage, a retained phase contribution `delta z`
in a complete successor chart reaches a later receiver as `P_k T_(k-1)...T_0 R delta z`.
For a projected chart the complete read is instead
`P_k U_(k<-0)(D_new R delta z+h_delta)` on the ambient field, including the hidden contribution
and its coupling back into represented modes. Present silence does not remove this future
contribution. Contributions superpose before the receiver's nonlinear face; the medium
and phase/clocks belong to the actual `T_j`. `Wave/Radiation.response_cone` supplies the spatial
arrival in its LC realization, and `Aeon/Clock/Epoch` supplies the epoch containing that arrival
from its certified receiver section. Neither a numerical coefficient remainder nor an arbitrary
tick interval supplies these maps. The precise remaining geometry join at this native caller is
the actual component transport, its decoder/read witnesses, and the applicable full storage
and port balance in its existing receipt.

### An actual material perturbation produces a contact response

[source-inspected; proved-derived, October 8] The producer is already concrete at
`hnn/propagation.{contact_operator,transit_solve,transit_update}` and
`HNN/Propagation.{transitOperator,TransitSolves,arriveG,arriveH}`. Fix the actual reached
displacement/rate `(u,w)`, full incident waves `(o_g,o_h)` with channel reads
`alpha_g=iota_g^T o_g`, `alpha_h=iota_h^T o_h`, embeddings `iota_g,iota_h`,
positive clock increment `h` and conductance `G`; fix `K,D`. In this section `h` is the clock
increment, not the hidden vector in (12a). For two actual storage forms `C_-,C_+`, write

```text
M_i=2C_i+(2h/G)I+hD+(h^2/2)K,
r_i=h(alpha_g-alpha_h)+2C_i w-hK u,
M_i omega_i=r_i,
deltaC=C_+-C_-,   eta=omega_+-omega_-.

M_+ eta = 2 deltaC (w-omega_-),                            (13)
M_- eta = 2 deltaC (w-omega_+).                            (14)
```

Both identities follow by subtracting the two actual descriptor equations:
`M_+ eta=r_+-r_--(M_+-M_-)omega_-`. The material-dependent right-hand side returns
`r_+-r_-=2 deltaC w`. The fixed-right-hand-side identity `-deltaM omega` would omit that
load-bearing term here. No inverse or positivity is needed for this algebra; a unique
produced correction additionally needs the successor's actual solve certificate. The native
normalization is `m_i=(G/2h)M_i`, `m_i zeta_i=r_i`, `omega_i=(G/2h)zeta_i`.
Therefore `delta zeta=(2h/G)eta`; identifying `zeta` with `omega` would change the returned
port amplitudes.

The producing decoder is the existing two-port update, at the same incident waves:

```text
delta u_next=h eta,       delta w_next=2 eta,
delta arrive_g=-(2/G)iota_g eta,
delta arrive_h= +(2/G)iota_h eta.                          (15)
```

The untouched off-channel waves still reflect. The actual incident state, material difference
and solve thus determine the response, including its direction and phase carried by the
wave/clock realization. A gradient, an energy difference or an unresolved coefficient alone
does not supply those operands. For a genuine complex realization the same linear subtraction
keeps the complex incident field; the inspected native owner remains its declared real
coordinate realization. These are conditional finite identities derived from the existing
owner, not newly kernel-checked Lean theorems or a new source-injection implementation.

The infinitesimal counterpart is already consumed: `hnn/reference.compose_contact` uses
`Cbar=sum 2 rbar (w-omega)^T`; `HNN/Ring.loaded_material_rate_tangent` and
`loaded_tick_material_variation` prove the descriptor differentiation and its adjoint pairing
for the loaded-ring realization. That ring has its own port coefficient and output law; (15)
uses the contact's embeddings and `G`, not the loaded ring's `Y`. The current native
continuation rebuilds the changed contact operands and solves them directly with zero new
injection. It does not implement a second forcing consumer alongside the changed material.
Only this storage-form join is asserted; existing `K,D` validation is unchanged.

For an executed solve define the actual equation defect `epsilon_i=M_i omega_i-r_i`.
The exact finite comparison becomes
`M_+ eta=2 deltaC(w-omega_-)+epsilon_+-epsilon_-`. Since `M_i omega_i=m_i zeta_i`,
this matches the residual operand in native `transit_defect`; its paired power is
`omega_i dot epsilon_i`. Later state and returned-wave splits keep their separate energy
returns. These numerical defects are not silently reclassified as a physical material
perturbation. For an exact correction `eta_*` solving (13), an approximate correction `q`
has residual `rho=M_+ q-2 deltaC(w-omega_-)` and, when an actual inverse bound `chi` is
certified in a declared positive receiver norm,
`norm(q-eta_*)<=chi norm(rho)`. A signed storage form alone is no such norm or inverse bound.
The solve, certificate and their resource cost remain necessary.

[agent-inferred; port obstruction] Equation (14) can express changed material as equivalent
forcing under the old operator, but its forcing depends on the changed response. It is a
feedback equation until solved, not a free feed-forward producer. To realize that forcing
through an admitted source port `B`, the actual source must witness
`B a=2 deltaC(w-omega_+)`. At a contact's incoming-wave ports this requires
`h(delta alpha_g-delta alpha_h)` to equal that vector. Their output also has direct
feedthrough: changing `o_g,o_h` adds `delta o_g,delta o_h` to the returned waves. Thus matching
the solve input alone does not reproduce (15); the complete source/output port law must match
those extra returns as well. The field's gluing and causal incident-wave law constrain any
such choices. A preimage can be plural, absent or coupled to the rest of the field.

At fixed actual symmetric storage `W`, an admitted state-source increment `Psi->Psi+B a`
would require signed midpoint work
`Delta E=a^T B^T W(Psi+(1/2)B a)`. Its source/storage port must fund that work; a negative
reading requires an actual receiving or absorbing channel. This identity neither selects
`a` nor establishes port admissibility. The equivalent forcing is a re-expression of the
material response; counting it as additional injected energy on top of the same material
work would double-count the passage. An unrealized coefficient increment is not yet an
actual `deltaC` or such a funded source. Its realization, phase-bearing port preimage and
complete power/decoder balance are the precise remaining obligations.

The finite loaded-span consumer is already stated conditionally by
`Holon/Deposition.station_tick_gain`: it assumes, for each actual arrival at a station,
`norm(Phi_(j<-tau) v)^2<=G_(j,tau) norm(v)^2`. For an admitted linear or tangent passage,
the contact response supplies the input map `S_tau`: solve (13) and decode (15) into the full
field. The station map is `Phi_(j<-tau)=P_j T_(j-1)...T_(tau+1) S_tau`, where the `T_k`
are the actual loaded-field maps with their participating ports, joint material and clocks.
Their field includes the returned waves and retained hidden components, not just a resonator's
displacement/rate. The input map includes the inverse/solve cost; a bare material coefficient
increment is not an energy-normalized input.

One sufficient finite certificate, in real coordinates, is a positive field metric `H_k` and
nonnegative exact bounds `gamma_k,b_tau,p_j` satisfying

```text
T_k^T H_(k+1) T_k <= gamma_k H_k,
S_tau^T H_(tau+1) S_tau <= b_tau I,
P_j^T P_j <= p_j H_j.

G_(j,tau)=p_j b_tau product_(tau+1<=k<j) gamma_k.           (16)
```

Successively applying these quadratic inequalities proves precisely the assumed span bound;
the empty product is one. Actual complex coordinate realizations use the Hermitian adjoints
and positive Hermitian metrics. In a projected chart the lifted metric must include the full
`D a+h` state and its actual cross term; discarding `h` changes the map being certified. A
sealed local ring Floquet certificate remains valid for its unchanged operands, but provides
this whole-field bound only through an actual factorization or port/gain argument including
the loaded return feedback. `span_transport_compose` assumes bounds on both composed maps;
it does not derive those bounds from the ring certificate. Native `PowerForm` may have signed
stiffness, so substituting it for positive `H_k` requires an additional coercivity proof.
For executed lattice passages the chart and split residuals remain additional carried inputs
in the finite variation-of-constants read and in their existing power receipt. Equation (16)
is a source-specific sufficient certificate for the separately owned finite-span obligation,
not a newly validated gain or a requirement of global stability.

The source-only reconciliation receipt is
`receipts/2026-10-08-full-field-work-and-contact-scattering/SOURCE_PINS.v1.json`, with
`SOURCE_CHECK.v1.json` checking the pinned operands and the unchanged accepted geometry/queue
sources. No build, simulation, precision change or renewed acceptance run is claimed.

### The phase-sensitive learner and the continuing field still owe one producing join

[source-inspected at the earlier root source `b34c8777`; bounded goal-alignment check,
October 8] The intended useful coupling is a
change of constitution that changes an actual admitted future reception through continuing
propagation. A phase alignment, coefficient-gradient decrease or larger growth alone does not
establish that consequence. The smallest already declared physical carrier is two native rings,
one contact and one loaded resonator, with the full wave/contact/resonator state and actual pump
clock carried across its material commit. A later port observation supplies a comparison in the
same encoding, transported frame and clock; its covector reaches that contact; the changed
material then meets the continuing field and a further received input. The comparison is between
actual participating currents, not an authored answer routine or an arbitrary added scalar.

Parts of that process already have actual consumers. `compare_contact_storage` constructs its
ratio and producing adjoint internally, returns the reached full `ContactCut`, and retains the
storage-factor return from `compose_contact`. `continue_deposited` commits that return and keeps
the full state/clock with separate material and opening work. Thus the local material response
and continuing wave are real source relations. The current caller search, however, finds this
API only in `hnn/reference/continuation.rs`'s finite fixtures; their target sequence is supplied
as `(i+1) modulo alphabet`. They do not establish acquisition of a useful phase coupling from
actual later boundary arrivals. The current source/current binding is deliberately preserved
by the cut; admitting a new source passage needs its actual once-only input and clock relation.
The same fixture also checks the zero-map obstruction: a receiving map `R=0` returns
`R^T g=0` to the passage, hence no contact storage covector, even when the face's covector is
nonzero. A changed coefficient or a local phase relation cannot supply a receiver that never
read it; the actual nonzero receiving/adjoint path is an operand of acquisition.

The ordinary `Reference::expose_from` path does compare against the actual subsequent input
window before ingesting it. Such an observed comparand is different from a task's authored
output target, and does not hand the machine a solution routine. Its `PendingRatio` reads the
contemporary constitution from source moments; it does not call the new continuing-cut API.
An observation-backed comparison therefore exists, but not yet as this continuing state/port
consumer. No result from the finite fixture establishes that missing composition.

The earlier root bytes inspected here contained an `hnn/executed` consumer of
`ReceivingBank::read_turn_covector` and `bank_release`, returning the executed lock comparison
through `E` and `rho`. **That is a historical consumer, not the current sealed HNN consumer.**
The later clean source `eed88d0a` explicitly retires that optimizer under S2; it must not be
restored or cited as evidence that the present bank growth reading supplies an observed
comparison. `E` remains a constitution/source-port owner. The current-source correction below
supersedes this review's earlier use of “current” for the older root consumer and its API scope.

The narrower missing square is visible in the actual producing call: `BankPlacement::of` and
`storage_over` form the candidate amplitudes directly from phase-carried source moments,
source-port images, pair-port images and transport weights. This placement is not the propagated
`Word`, `ContactCut` or reached native contact/resonator state. Conversely, the continuing contact
comparison does not read the phase bank's growth covector. The historical lock-comparison
consumer and the present observed-comparison return must not be treated as one instantiated
shared morphodynamic-field consumer.

[agent-inferred; one source-level next step] Make the existing bank candidate reader consume
the actual continuing word's receiver amplitude, and return that exact read's cotangent through
the same native contact. The producer/consumer relation to establish, on its admitted linear
or tangent passage with actual branch and clock, is

```text
Psi_j = Phi_Theta(j<-now) Psi_now + actual admitted port inputs,
z_(j,x) = C_j Psi_(j,x),
lambda_now = Phi_Theta(j<-now)^* C_j^* lambda_ratio,
contact material pairing = <rbar, 2 deltaC (w-omega)>.
```

Here `Psi_now` is the full reached state, including retained hidden motion; candidates enter
through the actual admitted port/decoder and combine with that continuing state. The source
moment keeps its existing quotient role and supplies newly admitted input exactly once.
Here `lambda_ratio` is supplied by the actual observed Holon comparison, not by a bare growth
derivative. A bank operand can bear that same name only after its comparison/read conformance is
declared and established. The comparison's second current must be an actual later received observation, encoded and
transported through the same owner, not a manually selected output class. This joins existing
owners and their observation-backed comparison; it is not a new targetless optimization law.
The forward read and its pullback must agree before another coefficient repair is counted as
realizing this mechanism. Admission of the observation's new input exactly once, with its work
and clock, is part of that single producing join. No source change or new test is made here.

Synchronization remains a declared material property. `HelicalPairInteraction` gives zero
contact power iff the attainable slip is in the material kernel; definiteness removes that
kernel, while neither case proves attraction or periodic closure. `PhaseContactPassage` mixes
two actual complex port values with declared unit connection `u`, keeps their transported sum
and returns the lost positive energy through heat. It does not infer `u` or deposit a useful
material relation; a frustrated circuit may admit only a zero parallel section. Such laws
supply actual interaction operands, not an automatic learning result.

Admissible field states, candidate inputs and material changes keep their own constraints and
typed refusals. A coherent sum of amplitudes is different from a receiver mixture of alternative
states: `interpolation_intensity_defect` retains the phase variance that averaging would lose.
Present silence still permits delayed reception; `ModeQuotient` requires transport, drive,
read, costate, storage and material variation all to descend, and the accepted future-read owner
tests actual composed future receivers. Through-flow is supplied by the boundary inputs and
relative side/cap returns, not by assuming one closed carrier orbit. These conditions do not
require immediate emission of numerical remainders or invulnerable retention.

This bounded check is source-bound by
`receipts/2026-10-08-native-phase-learning-alignment/SOURCE_PINS.v1.json` and
`SOURCE_CHECK.v1.json`. It proposes the one missing consumer relation above; it reports no
learning acceptance, implementation campaign, simulation or change to sealed inputs.

### The existing decoder and reverse map give the shared-reader equality

[source-inspected at the earlier root source `b34c8777`; manually derived at held operands,
October 8; current-source correction below] No new coordinate library is
needed. `hnn/ring.turn` packs a realified ring vector into its section-crossing order:
`T(a)_t=a_(2(d-1-t))+i a_(2(d-1-t)+1)`. `MemberCovector::storage` reverses the same order
for the resolved member's coordinate-covector enclosures. If `g_t=g_Re,t+i g_Im,t`, define
`k_(2n)=g_Re,(d-1-n)`, `k_(2n+1)=g_Im,(d-1-n)`. The exact real cotangent pairing is

```text
Re sum_t conjugate(g_t) T(a)_t = k^T a.                    (17)
```

There is no additional half factor. This is the real part of the Hermitian pairing, not a
complex bilinear quadrance. The bank's actual `MemberCovector` already stores derivatives in
the two real crossing coordinates; its `storage()` supplies `k` with its enclosures, before
any separately declared comparison combines active members and candidate weights. This packing
does not turn a growth covector into an observed-comparison covector. A refusal or unresolved
active member keeps the existing branch/certificate obligation; (17) does not choose one.

Both `SourceMoment::open_parts/open_storage` and `BankPlacement::of/storage` use the ring's
realified node chart and apply the source lift. The existing test
`the_bank_placement_is_the_sections_injection` identifies placement with the continued moment's
opening storage at modulus one and the same material/lift. Its dissipative companion states the
one-sided condition under which that equality still holds; later placed stations use two-sided
weights. These inspected tests are not rerun here. Thus a common injection decoder exists.
After a native passage a producing equality is still required. With a declared map `D_j` from
the actual word receiver to the bank's storage chart, keep
`r_j=BankPlacement.storage(j,cells)-D_j a_e`. Equation (17) carries this complete difference as
`T(r_j)`; it is not automatically zero or merely a rounding error.

The native ports have distinct timing. `Word::anchor(e,R)` is the carried junction participation
`a_e`, before that step's element, loaded return and contact transit. `Word::change().storage[R]`
is the storage output after its last full tick. An anchor read and a terminal-storage read are
different actual consumers. At exact fixed junction weights the anchor map `A_e` reads the full
start state as `(Y s+sum G arrivals)/(Y+sum G)`; chart/split execution retains its own difference.
For the declared bank storage `D_j a_e`, (17) gives the anchor covector `D_j^T k`. If `D_j` is
`Ring::rotate` by `ell`, this is rotation by `-ell`. The new consumer must declare that frame
choice once. `ReceivingPhases::read` instead reads `R_map P^tau a_e` into `2|alphabet|` logits;
this map is not the bank's `2d` amplitude decoder. Recovering the full bank amplitude from those
logits requires a supplied factorization `B=L R_map P^tau`, hence kernel compatibility. For
an invertible full-amplitude decoder `B`, `R_map` must be injective; the zero receiving map fails.
No such factorization is implied by the current receiving declaration.

`Word::pull_back_continuing` is the existing reverse consumer for the raw amplitude read. Its
`anchors[e]` accepts the width-`2d` covector `D_j^T k` on that actual recorded junction step;
`reverse_core` then handles the junction, contact and loaded return. For a terminal-storage read,
the new contribution instead belongs in `ChangeCovector.storage[R]`. Its arrivals, contact
states and resonator states must preserve any existing future terminal cotangents. The returned
full opening `ChangeCovector`, not just `WordReturn.opening`'s storage component, carries that
future dependence into a preceding word. A newly zero contribution is different from discarding
a pre-existing terminal contribution.

Let `Phi_e` be the full fixed-operand word map to the start of step `e`, `A_e` its anchor map,
`Phi_N` its terminal map, and `mu_N` a full terminal cotangent. At fixed inputs, chart, frame,
clock/read binding and exact linear execution,

```text
mu_0 = sum_e Phi_e^T A_e^T D_e^T k_e + Phi_N^T mu_N,
sum_e k_e^T D_e A_e Phi_e deltaPsi_0
  + mu_N^T Phi_N deltaPsi_0 = mu_0^T deltaPsi_0.             (18)
```

This is the relation the existing continuing reverse can consume; the bank's native caller
must supply its actually produced cotangent, not construct a `RatioCovector` from a bare vector.
Coordinate cotangents use transposes directly. If one instead supplies metric-gradient vectors,
their representing covectors and the actual source/receiver metrics are required first.
The existing contact reverse solves the normalized producing chart's transpose after
`zeta_bar=(G/h)w_bar_next+(G/2)u_bar_next+(a_bar_h-a_bar_g)/h`; `compose_contact` contracts its
result with `2 deltaC(w-omega)`. For changing input or material, their additional reached tangent
terms join (18); (18) alone is the fixed-input, fixed-material state pullback.

`HNN/LatticeWord.executed_adjoint_pairing` and `executed_adjoint_unique` already own the matrix
transpose identity for the executed linear chart. Its `exact_adjoint_pairing_defect` keeps the
operator mismatch explicitly. In one stacked read let the carried forward result be
`y_hat=L_hat x+epsilon_f` and the carried reverse result be
`mu_hat=L_hat^T k+epsilon_b`. Then the complete pairing residual is

```text
k^T y_hat-mu_hat^T x = k^T epsilon_f-epsilon_b^T x.
k^T y_hat-(L^T k+epsilon_b)^T x
 = k^T[(L_hat-L)x+epsilon_f]-epsilon_b^T x.                 (19)
```

The second line compares an exact operator's adjoint with a different executed operator. Forward
and reverse transient releases retain their actual signs and bounds. It is not an assertion
that a quantizer's cell jumps have this smooth derivative. Source placement, propagated state,
chart execution and carried cotangent errors remain distinct operands.

[proved-derived; moving-reader scope] Equations (17)-(18) hold their decoder/frame/read epoch
fixed. For `q_j=C_j(tau_j,Theta)Psi_j(tau_j,Theta)` before the fixed `turn` packing, a smooth
variation on one crossing branch instead gives

```text
delta q_j = C_j deltaPsi_j|fixed_tau
  + (delta_Theta C_j|fixed_tau) Psi_j
  + (partial_tau C_j Psi_j+C_j f_j) delta tau_j.            (20)
```

Each direct decoder, receiver-state, frame and clock term is paired with `k_j` as well.
`ChangingReceiver/Defect.moving_receiver_rate` owns `chart_dot Psi+chart Psi_dot` and its
complete rate defect; `ChangingReceiver.actual_moving_chart_clock_action` adds the actual
clock-rate factor and hidden action; `Holarchy/Reception.moving_receiver_rate` keeps both
participating states and explicit chart motion. They are the existing owners for this scope.
For a smooth section `chi(tau,Psi,Theta)=0` with nonzero actual crossing rate,
implicit differentiation conditionally gives
`delta tau=-(D_Psi chi deltaPsi|fixed_tau+D_Theta chi deltaTheta)/(partial_tau chi+D_Psi chi f)`.
This analytic event formula is not a newly kernel-checked section theorem. At a change of native
discrete epoch or branch, rebind/re-read the actual crossing; do not differentiate its integer
index as a fixed smooth clock. A held contact-storage partial can hold these reads fixed because
the current continuation preserves its geometry/port/pump declarations; broader changes owe (20).

`PumpSchedule::placed` starts each bank turn at its declared crossing zero, while the continuing
word carries `opened_at`, `next_tick` and its resonator form phases. The producer must witness
the bank crossing's clock/origin against that actual read; a common node chart supplies no
automatic pump-clock alignment. The observation supplies comparison data. Its physical input
enters through the admitted forward port once, and is not reinjected by the read or cotangent.
Any source/target encoding or receiving map that also changes keeps its own direct variation.
Finally, `Phi_e` and `mu_N` carry the full retained hidden field: `C_j h=0` today does not remove
`C_j Phi h` or a later material-variation read.

The supporting source-only pins are
`receipts/2026-10-08-shared-reader-decoder-adjoint/SOURCE_PINS.v1.json` and
`SOURCE_CHECK.v1.json`. This is a producing-law review for the existing HNN owner; no HNN
consumer, sealed input, compiler or numerical precision is changed.

### The sealed source supplies the observed ratio, not an undeclared growth objective

[source-inspected; correction, October 8] The HNN owner's clean current source is
`eed88d0a31e4ceb5b823dbe734180a2a0bfbedfe`, inspected in its
`hnn-continuing-bank-01a1030c` worktree together with
its `SOURCE_CONTRACT_FINDING.v1.json`, copied byte-for-byte into this section's receipts as
`HNN_SOURCE_CONTRACT_FINDING.v1.json`. The two preceding source
reviews used the earlier root checkout's exact working bytes, pinned there at `b34c8777`.
Their coordinate and held-reader equations remain conditional algebra; their E/rho optimizer
claim is historical on this sealed branch. `executed.rs` lines 16-28 and the S2 retirement
record explicitly retire that consumer. Neither an optimizer restoration nor a substituted
growth objective is authorized by the shared-reader relation.

The current observed comparison has the actual producing owners already:

| Actual operand or operation | Current owner and symbol |
|---|---|
| Full carried wave, arrivals, contact and resonator state; absolute opening tick | `word.rs::EndChange` (368), `Word::opened_at` (2295), `change` (2317), `anchor` (2422) |
| Declared anchor carrier and complex receiving chart `R P_R^tau` | `receiving.rs::ReceivingPhases::read/read_carrier` (2093/2113) |
| The actual word's faces, admitted observed `Encoded` target and partition | `word/continuation.rs::contact_faces` (184), `compare_contacts` (194) |
| Target lift/branch in the same cut; actual ratio and odometer covector | `ratio.rs::target_phases` (275), `HolonRatio::compare_partition` (362), `covector` (467) |
| Anchor covector and optional full ending covector returned through the same word | `port.rs::Word::pull_back_continuing` (899), `ChangeCovector` (820) |
| Observation compared before its window's ingestion | `reference.rs::expose_continuing` (4376) |
| Pump-modulated monodromy and its growth differential | `ring.rs::ReceivingBank::read_turn_covector` (3550), `MemberCovector::storage` (3019) |

The receiving map `R` is therefore not absent. `read_carrier` checks that the actual carrier is
the declared one; an anchor cannot silently replace a source-observer carrier. With that
anchor declaration, let `Psi_j` denote the actual full state at its junction, `A_j` its anchor
map, and `P_R^tau` the producing lift read by `ReceivingPhases`. The current existing law is

```text
f_j = R P_R^tau A_j Psi_j,
ratio = HolonRatio::compare_partition(actual Faces(f), observed classes,
          target_phases(field, actual lift, R_ring, observed Encoded), compared),
g_j = ratio.covector().logits()[j],
k_j = P_R^(-tau) R^T g_j.                                (21)
```

At a compared station with observed target `t_j`, the exact current odometer-chart entries are
`g_(j,2c)=p_tilde_(j,c)-1_(c=t_j)` and
`g_(j,2t_j+1)=-(phi^T_j-phi^H_(j,t_j))/2`, with the other imaginary entries zero.
The actual grain fibre, target winding branch and uncompared zero entries remain in the ratio.
This is the owner's declared comparison covector; it is not a derivative of a quantized cell
jump or a proof of finite score decrease. `compare_contacts` already pulls it through the
producing word and composes reached C/K/D contact-factor returns. The exact physical material
and comparison gates remain those owners' obligations.

[proved-derived; held-reader state pairing] At fixed admitted inputs, receiving map/carrier,
source lift, clock and material, let `Phi_j` map the full opening state to that actual junction
and `Phi_N` to the full terminal change. On an exact linear passage, or its correctly declared
actual differential, the complete read return is

```text
mu_now = sum_(j in compared) Phi_j^T A_j^T P_R^(-tau) R^T g_j
         + Phi_N^T mu_N,
sum_(j in compared) g_j^T R P_R^tau A_j Phi_j deltaPsi_now
  + mu_N^T Phi_N deltaPsi_now = mu_now^T deltaPsi_now.      (22)
```

The supplied anchor slot contains `k_j`; the word reverse performs `A_j^T` itself. The full
`ChangeCovector` retains arrivals, contact and resonator costates; its storage-only projection
is not a sufficient future return. `SourceReceiverReturn.sourceReturnAt_pairing` and
`partitionReturn_pairing` own the generic source-bound linear paired square; their native
instantiation and validation status are not enlarged here. Equation (19) still supplies the
explicit residual if a different chart or carried split is used. For a learned decoder or
actual moving section/clock, (20) supplies the direct `deltaC Psi` and clock/event terms, and
ChangingReceiver owns their scope. A target encoding or target clock variation also keeps its
own direct term; native class/epoch/branch changes require an actual new comparison.

This law is already target-bearing. `Reference::expose_continuing` reads the actual subsequent
window in the comparison before its ingestion. That supplies observation provenance for this
exposure, not proof that it calls the new contact-return consumer. A blind prediction must
precede the observation; the observed consequence supplies comparison data and is admitted
later through its physical input port once, with its actual work/clock. It is not placed in
blind candidate state or injected again by a cotangent read.

[proved-derived; the source formulas bar the growth substitution] At fixed supplied bank
amplitudes, `read_turn_covector` returns derivatives of `log|mu|`, independent of the observed
target. Choose two admitted different targets `t` and `s` at one compared station with the
same produced face. Equation (21)'s real covectors differ by `e_s-e_t`, which is nonzero,
while the bank growth reading and its active-member covectors are unchanged. Thus a bare growth
covector cannot supply both actual observed-comparison covectors. Active-member branches and
enclosures do not repair this missing target operand. If a declared observed comparison really
factors through bank growth, its own target-dependent derivative must weight those growth
covectors, and any omitted complex phase read must still return. No such comparison is declared
in this current source. `MemberCovector::storage` remains the correct coordinate transpose
for its growth functional, not a constructor or substitute for `RatioCovector`.

[agent-inferred; exact unresolved bank declaration] The ontology settles that reception uses
the actual participating Holons and the covector of their declared ratio. It does not identify
this independent bank's supplied pump-modulation amplitudes with the existing receiver's
physical waves or logarithmic logits. The missing question is: **which admitted bank input port
and output/receiver chart, with units and actual source/receiver/pump section, period and clock
origin, make the bank a participant in this same observed complex comparison?** Its declaration
must provide the actual map `B_j` from the reached full word state to the bank turn, and the
bank's read back to (21), or retain their complete difference as a receipt. No extra authored
decoder or scalar objective is inferred merely because both coordinates can be packed as
complex numbers. The bank's crossing-zero schedule and a word's carried absolute pump phase
are distinct until this physical binding is witnessed.

If an actual bank read supplies the same linear/tangent receiving map, that is a conformance
equation between the complete producing maps, not equality of source-image storage and a
later propagated anchor. In particular, a proposed factorization of the native comparison
read through bank amplitudes must annihilate every difference those amplitudes annihilate;
an omitted harmonic/hidden or through-flow state which a future native receiver distinguishes
is not a lawful quotient. Candidate port openings must use the native admission and work
receipt, rather than a storage-only surrogate `BankPlacement`. This is the precise missing
composition; the existing observed ratio and its return do not require a new comparison law.

Current-source pins and the bounded source-only check are in
`receipts/2026-10-08-current-shared-reception-contract/SOURCE_PINS.v1.json` and
`SOURCE_CHECK.v1.json`. This corrects the version and states the intended law on current owners;
it makes no HNN consumer edit, optimizer restoration, new compile request or scientific run.

### A later word's full opening costate pairs with the earlier material tangent

[source-inspected; manually derived, October 8; bounded two-passage law] A bank is not needed
to state delayed material credit. Fix one parameter identity: contact `a`, its C/K/D factor
family, factor chart and stiffness signature, on one producing constitution. Hold that same
identity and parameter value across two actual word passages. Fix their admitted source data,
lift/reference and pump clocks, receiving map and partition. The first supported domain is an
exact unsplit linear word, with no resonator saturation, contact parting or changing discrete
event, no intervening deposition/release and `Absorption::Nothing`. The declared contact solve
is nonsingular. C itself need not be invertible in the identity crossing below. A nonlinear
passage instead owes its actual differential at the producing trajectory.

This law is pinned at `e5a476a1748743257b01bf3fbce7593656c2b79b`. The first source-binding check
stopped when the HNN worktree advanced from `eed88d0a`; inspection found a matched test
ownership fix and its owner's records/receipts, with all fourteen preceding producing owners
byte-identical. No prior acceptance is assigned to this new tangent consumer.

The existing full state carrier is `word.rs::EndChange` (368); its dual is
`port.rs::ChangeCovector` (820), with `pairing` (829) and `pull_back_continuing` (899).
`prediction.rs::physical_signed_tick` (2291) already advances one signed full-state response
through the same junctions, loaded resonators and contacts. It is not yet a contact-material
forcing consumer. `PhysicalSourcePairing` (3554) handles the distinct applied source/E direction
on a fixed word; it neither supplies nor replaces the earlier C/K/D tangent. No parallel
state or covector shape is needed for the proposed consumer.

For one exact factor direction `H`, use the full signed state `chi=J_a H`. At each first-word
tick let `T_k` be its fixed-operand full state map and let `b_(a,k)` be the reached material
forcing. At the actual producing contact state the existing transit solve/update gives

```text
M = 2C+(2h/G)I+hD+(h^2/2)K,
M omega = h(alpha_g-alpha_h)+2Cw-hKu,
M eta = 2 deltaC(w-omega)-h deltaD omega
        -h deltaK(u+h omega/2),
b_u=h eta, b_w=2 eta,
b_arrive_g=-(2/G)iota_g eta, b_arrive_h=(2/G)iota_h eta.   (23)
```

All other same-tick components of this local forcing are zero; the same full `T_k` carries its
later influence into storage and resonators. `propagation.rs::transit_solve/transit_update`
(1333/1359) own these operands. For factors, `deltaC=H F_C^T+F_C H^T`, D is analogous, and
`deltaK=H Sigma F_K^T+F_K Sigma H^T` with the fixed actual signature. These are differential
terms; the finite factor movement's `H Sigma H^T` is not inserted into a tangent. Thus

```text
chi_(k+1) = T_k chi_k+b_(a,k),
chi_0 = the declared opening-state derivative.            (24)
```

A held, parameter-independent first opening has `chi_0=0`; a canonical opening whose rate is
defined through a changing C must provide its actual derivative instead. Equation (24) is
not a finite-difference equality between two nonlinear or rounded code executions. A single
declared direction can be carried with its producing parameter identity and base point and
overwritten at each passage; no prior word, event list or trajectory tape is retained.

The actual passage boundary is part of the derivative. `Word::reception_end` (2376) carries
the state arriving **before** a terminal junction when the word ended there; it carries the
current full-tick change otherwise. It does not carry that terminal junction's scattered
outgoing waves. `ReceptionCarry::crossed` (487) then transports arriving-wave references and
holds its recorded momentum, while `open_exact_received` (1801), `interior_of` (1665) and
`continuing` (2032) replace source-ring storage by the new `SourceMoment::open_storage` once.

For the same C parameter on both sides, `pi=C(theta)w(theta)` varies as
`delta pi=deltaC w+C chi_w`. Crossing back into `C(theta)` has `w_cross=w` identically;
the two `deltaC w` terms cancel, giving `chi_w_cross=chi_w`, even for singular C. Treating that
recorded momentum as constant under this common-parameter variation would add a false storage
term. The actual old/new conductances are fixed under this C/K/D direction; their reference
map multiplies each arriving wave by `2G_old/(G_old+G_new)`. Write that map as `B_ref`, and
write the source-storage-zeroing map as `Pi_int`. The second opening tangent and its earlier
material credit are exactly

```text
chi_open2 = Pi_int B_ref chi_carry + delta(source opening),
earlier material credit[H] = <mu_open2, chi_open2>.         (25)
```

The source term is zero for the held E/source/lift scope here; a changing source must supply
its own actual opening derivative. `mu_open2` is the second word's **full** returned
`ChangeCovector`, not `WordReturn.opening`'s storage projection. Its current ratio already
provides the later observation. If the same parameter appears in the second passage, add its
direct material return (the existing `compose_contact` contraction) to (25). Complete
absorption sets the inherited state tangent to zero. Keeping (25) therefore requires the
actual absorption declaration, reference map and source imposition, not an unfiltered end-state
pairing. The open source term is the missing consumption of this earlier tangent by the later
opening costate; no missing observation objective or bank growth optimization is inferred.

Chart/rounding extensions keep their own variation. For the actual normalized executed solve
`m z_hat-r=d`, a declared smooth variation satisfies
`m delta z_hat=delta r-delta m z_hat+delta d`. Its `delta d` includes the declared chart and
split variation. A bound on `d` alone does not bound that derivative. In a full recurrence an
unresolved tangent defect `xi_k` contributes `sum_k <mu_(k+1),xi_k>` and any opening defect
contributes `<mu_open2,xi_open>`; carried reverse residuals also remain as in (19).
`physical_word_is_exact` (2104) supplies only the zero-chart/split check; saturation and event
exclusions are separate. A threshold, sheet, lattice-cell, rank-selection or crossing change
is a branch change, not a smooth derivative supplied by these equations.

A deposited parameter changes this scope. For the actual held-state map
`C_plus w_plus=C_minus w_minus`, its derivative is

```text
C_plus chi_w_plus = C_minus chi_w_minus
                 + deltaC_minus w_minus-deltaC_plus w_plus. (26)
```

An invertible `C_plus` fixes this rate derivative; a singular crossing requires the declared
selected preimage-fibre/rank chart and its null-fibre term. `PowerForm::held` and
`ContactCut::continue_deposited` own that separate physical crossing. If publication is a map
`theta_plus=U(theta_minus,observation)`, the return also needs its declared derivative or branch
receipt. A historical tangent based at `theta_minus` is not a gradient at `theta_plus`; rebasing
the parameter/direction is an additional map, not an equality inferred from a retained value.

The current-source receipt is
`receipts/2026-10-08-two-word-material-credit/SOURCE_PINS.v1.json`, with its bounded
`SOURCE_CHECK.v1.json`. This states one producing law and its consuming pairing. The material
forcing, carry-tangent consumer and actual controls remain with the HNN owner; no such source
implementation or new kernel check is claimed here.
