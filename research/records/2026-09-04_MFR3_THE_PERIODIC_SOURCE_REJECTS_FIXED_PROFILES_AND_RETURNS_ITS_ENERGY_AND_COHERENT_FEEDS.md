# MFR3: the periodic source rejects fixed profiles and returns its energy and coherent feeds

**Date:** 2026-09-04. **Campaign:** MFR3, under the
[standing MFR goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
**Position:** a progress return; MFR3 remains in progress. **Grades:** per claim.
The formal returns and the subsequent written local-core derivation have separate evidence scopes.

[historical] This record retains the first MFR3 return at `4b25305e`. The
[subsequent return](2026-09-04_MFR3_THE_COHERENT_SOURCE_REACHES_A_PHYSICAL_FIELD_AND_THE_LOCAL_FRAME_RETURNS_ITS_FLUX.md)
completes the coherent population's physical reconstruction and returns the local energy flux;
its source scopes supersede the corresponding unfinished passages recorded below.

## The global stationary attempt and its obstruction

[definition] Reuse MFR1's actual periodic source and chart
`U(y,s)=q(s)u(c(s)+ell(s)y,theta(s))`, with `theta'=ell*q`. The first attempt asks for one
global function `V(y)` equal to `U(y,s)` at every `s>=0`, while
`ell(s)=ell0 exp(-beta*s)`, `ell0,beta>0`.

[proved-derived; formal-checked] The transported coordinate periods `1/ell(s)` fill a ray.
Two sufficiently large periods can differ by any prescribed signed step. Applying both period
equalities therefore makes every coordinate translation a period; the global profile is constant.
This argument needs no continuity of the profile. It uses actual source periodicity through
`NavierStokesRescalingPeriodObstruction.OpenPeriodicSolutionOn.stationaryProfile_constant_exponential`.

[proved-derived; formal-checked] A smooth periodic pressure cannot have a nonzero constant
gradient. `NavierStokesPeriodicPressureRigidity` proves this by testing the existing periodic
pressure-work cancellation with the constant gradient itself, retaining the unit-cube volume,
then transports the result to any nonzero period. In the actual rescaled unforced momentum law,
the stationary constant velocity would require

```text
grad P = (q'/q) V.
```

Thus `V=0` whenever `q` and `q'` are nonzero at an interior chart time. The final theorem
`NavierStokesStationaryRescalingExclusion.OpenPeriodicSolutionOn.exponential_stationaryProfile_eq_zero`
discharges the derivative and time hypotheses for

```text
q(s)=q0 exp(-alpha*s),
theta(s)=(ell0*q0)/(alpha+beta) (1-exp(-(alpha+beta)*s)),
T=(ell0*q0)/(alpha+beta),             ell0,q0,alpha,beta>0.
```

[definition] The rejected attempt is an exact, globally fixed normalized profile. Local
convergence on expanding cells, profiles depending on `s`, and discrete scale families do not
satisfy that hypothesis merely because they look nearly self-similar.

## Energy is integrated over the transported population

[proved-derived; formal-checked] `NavierStokesRescaledEnergy` retains
`C(c,ell)={y | c+ell*y in unitCube}` and returns, for `ell>0`,

```text
integral_C |q u(c+ell*y)|^2 dy = (q^2/ell^3) integral_unitCube |u(x)|^2 dx.
```

The source integrability and the change of variables have explicit owners. For an actual
unforced `OpenPeriodicSolutionOn` with `nu>=0`, the source integral is bounded by twice the
initial kinetic energy. Consequently, for exponential `q,ell`, an eventual strictly positive
lower bound on the normalized transported-cell energy implies `2*alpha<=3*beta`.
`exponent_condition_of_openPeriodicSolutionOn` composes that conclusion with source
integrability and the existing initial energy bound; uniform source energy is not an unproved
input port. The normalized lower bound remains an explicit condition on the supplied solution.

## A complete shear control and a coherent coefficient population

[proved-derived; formal-checked] `NavierStokesShearAnsatz` constructs

```text
u(x,t)=A(t) sin(2*pi*x0) e1,   p=0,   f=0.
div u=0,   Du[u]=0,   Delta u=-(2*pi)^2 u.
R(x,t)=[A'(t)+nu*(2*pi)^2*A(t)] sin(2*pi*x0) e1.
```

The sine Laplacian and rank-one Jacobian trace are proved from the actual spatial function.
Evaluating at `x=e0/4` recovers the amplitude, so `R=0` is equivalent to the heat amplitude
law. The explicit `A(t)=A0 exp(-nu*(2*pi)^2*t)` constructs a complete `PeriodicSolution`,
including its initial derivative and joint smoothness. For `nu,t>=0`, its amplitude is bounded
by `|A0|`. Restricting that source to any positive lifespan instantiates the actual
`CoherenceDefectAt` receiver with defect zero at every interior time and frequency.

[proved-derived; formal-checked] `NavierStokesCoherentTriadWitness` constructs the complete
coefficient population supported at `p=e0`, `q=e1`, `-p`, `-q`, with real amplitudes
`vp=(0,1,1)` at `+/-p` and `vq=(1,0,1)` at `+/-q`. All other coefficients vanish.
The population is conjugate-symmetric and divergence-free at every frequency. At `k=p+q`,
the coefficient is zero, but the full convolution has exactly two nonzero contributing feeds.
Both have third component `2*pi*i`; the Leray projection of their sum is `(0,0,4*pi*i)`.
The signed nonlinear source on the right of the velocity PDE is its negative.

[proved-derived; formal-checked] At the third output component, the complete source's squared
norm is twice the diagonal sum of all squared feed norms. Thus the coefficient inequality
`|source_2|^2 <= (1+kappa) sum_parent |feed_parent,2|^2` holds exactly when `kappa>=1`.
The null current coefficient at `k` retains a nonempty contributing population and a nonzero
next nonlinear source. It does not imply incoherence of the feeds.

[definition] This is a complete coefficient-level source calculation. It is not yet the
Fourier population of a constructed smooth physical solution slice. The shear result does have
that actual source binding. The distinction prevents a finite algebraic witness from being
promoted to a physical counterexample or to a singularity.

[established-bounded; source-inspected] The existing reconstruction chain was inspected at
`2c6c8a84`: `NavierStokesFinitePicardNativePathJoin.finiteCubeNativeH3State` and
`weightedPhysicalCoefficient_finiteCubeNativeH3State` retain every supported coefficient;
`NavierStokesWeightedFourierReconstruction.vectorSpatialFourierCoeff_reconstructedVelocity`
returns the exact real-field coefficients under the reality condition; and
`NavierStokesWeightedFourierDivergenceReconstruction.reconstructedVelocity_c1_onePeriodic_divergenceFree`
returns periodicity, incompressibility and `C1` regularity.

[open] The finite population's smooth initial-field passage should compose these owners and
prove the finite synthesis is `C-infinity`.
That higher-regularity bridge and its use in the actual solution receiver remain to be constructed.

## A localized periodic core and the next residual

[definition] The next written attempt retains the expanding cell explicitly. Fix a centre
`c`, positive reference scales `a0,ell0`, positive exponents `alpha,beta`, and a smooth compactly
supported vector potential `A(y,s)`. Assume its support lies uniformly in `B_R(0)` and
`ell0*R<1/2`. Let `V(y,s)=curl_y A(y,s)` and

```text
a(s)=a0 exp(alpha*s),    ell(s)=ell0 exp(-beta*s),
theta'(s)=ell(s)/a(s),   theta(0)=0,
z_n=y-n/ell(s),
U(y,s)=sum_(n in Z^3) V(z_n,s),
u_app(x,theta(s))=a(s) U((x-c)/ell(s),s).
```

Choose `V` nonzero when testing concentration. The sum is locally finite. For `s>=0` its
supports are disjoint, its physical period is exactly one, and its divergence vanishes.
Its physical initial field is a smooth periodic field. These are kinematic admissibility
conditions; the momentum residual is still to be tested.

[proved-derived] Define `N=(u_app . grad)u_app`. The mean-zero periodic pressure is determined
by `Delta p=-div N`: for every nonzero physical integer mode `m`, its coefficient is
`p_hat(m)=i*(m dot N_hat(m))/(2*pi*|m|^2)`, with `p_hat(0)=0`. Smoothness gives rapidly
decaying coefficients, so the differentiated series converges. Set `P(y,s)=p(c+ell*y,theta(s))/a^2`.
This includes pressure coupling between all periodic copies, even where velocity is zero.

[proved-derived] Differentiating the moving image address gives
`(z_n)_s=-beta*n/ell`. Hence its time current and the spatial dilation term combine as

```text
U_s + beta*DU[y] = sum_n [V_s(z_n,s)+beta*DV(z_n,s)[z_n]].
```

Disjoint support makes `DU[U]=sum_n DV(z_n,s)[V(z_n,s)]`; the Laplacian is also termwise.
With `mu(s)=nu/(a(s)*ell(s))`, the complete normalized momentum residual is therefore

```text
R(y,s)=sum_n [V_s + alpha*V + beta*DV[z_n] + DV[V] - mu(s)*Delta V](z_n,s)
         + grad_y P(y,s).
```

Its physical counterpart is `(a^2/ell) R`. This is a written chain-rule derivation, not a new
Lean acceptance of the periodized core construction. No cutoff derivative or pressure tail is
discarded: a cutoff introduced through `A` remains inside all derivatives of `V=curl A`.

[proved-derived] Let `E(s)=integral_R3 |V|^2` and
`D(s)=integral_R3 sum_(i,j) |partial_i V_j|^2`. Integrating the residual against `U` over
one expanding cell gives

```text
integral_cell U dot R = (1/2) E'(s) + (alpha-3*beta/2) E(s) + mu(s) D(s).
```

Indeed `integral V dot DV[y]=-3E/2` by integration by parts, advection has zero energy work,
pressure has zero work by periodic incompressibility, and `-Delta` contributes `D`. This also
follows by differentiating the physical energy `a^2*ell^3*E/2` using `theta'=ell/a`.

[proved-derived] This identity rejects a second overrestricted attempt: a nonzero fixed
compact profile `V(y)` with disjoint periodic copies cannot be an exact unforced solution for
`nu>0` and `alpha!=beta`. Exactness would require
`(alpha-3*beta/2)E+mu(s)D=0` for all `s`. Since `mu` varies, two times force `D=0`, and smooth
compact support then forces `V=0`. For `beta<alpha<3*beta/2`, even its residual has the lower
bound `liminf norm_L2(R)>= (3*beta/2-alpha)*sqrt(E)>0`, obtained from the same pairing and
Cauchy–Schwarz as `mu` tends to zero. This lower bound applies to the declared fixed family.

[open] A surviving attempt must now supply actual profile modulation, overlapping/exterior
transport, or a different scale law. For the displayed compact modulated family, exactness
requires `E'=(3*beta-2*alpha)E-2*mu*D`, together with the full vector residual above.
Solving only this scalar equation does not solve momentum. The next construction must retain
that modulation and the nonlocal pressure while evaluating its complete triad/coherence
receiver. No quantitative stability margin or nonzero limiting core has yet returned.

## Integration and verification

[definition] Six new formal owners, under
`formal/elementary-holonics/ElementaryHolonics/Millennium/`:
`NavierStokesRescalingPeriodObstruction.lean`, `NavierStokesPeriodicPressureRigidity.lean`,
`NavierStokesStationaryRescalingExclusion.lean`, `NavierStokesRescaledEnergy.lean`,
`NavierStokesShearAnsatz.lean`, and `NavierStokesCoherentTriadWitness.lean`.

[established-bounded; process-audit] Lean 4.33.0 returned these final checks from
`formal/elementary-holonics/`:

```sh
lake build ElementaryHolonics.Millennium.NavierStokesStationaryRescalingExclusion \
  ElementaryHolonics.Millennium.NavierStokesRescaledEnergy \
  ElementaryHolonics.Millennium.NavierStokesShearAnsatz \
  ElementaryHolonics.Millennium.NavierStokesCoherentTriadWitness
lake build ElementaryHolonics
```

The focused dependency closure returned 9,066 jobs; the live umbrella returned 9,860 jobs.
These are build scopes, not counts of new theorems. Decisive axiom reports from all six owners
contain only `propext`, `Classical.choice`, and `Quot.sound`. The four terminal imports and six
owner-map entries are integrated. Source review and changed-line whitespace review returned.
The written local-core construction above is outside this formal acceptance scope.

[open] MFR3's modulation and physical source passage remain. The arithmetic MFR2 source remains
available; MFR5 still owes the sign inequality. The concurrent HNP changes remain owned by that
session and are excluded from this change's commit.
