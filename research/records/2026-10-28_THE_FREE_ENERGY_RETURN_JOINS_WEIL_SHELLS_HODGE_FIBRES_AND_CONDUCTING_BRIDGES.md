# The free-energy return joins Weil shells, Hodge fibres and conducting bridges

**Date:** October 28. **Scope:** Brandon's request to apply the boundary free-energy variation to
the existing RH, Hodge, fluid/plasma/gas, relativistic-neck and local-navigation paths. The
October 26 Claude exchange was recovered from the local conversation logs and its resulting
Galois-gap and neutral-scope records; private transcript text is not reproduced. The actual
mathematics owners were read. **Grade:** [owned] is recovered; [derived] is calculated below;
[physical instance] supplies a constitutive source; [research join] names its consumer. No target
conjecture or new native capability is claimed solved by these substitutions.

## 1. The common return and its exact contact increment

[owned] The previous [contact/clock derivation](2026-10-28_THE_CONTACT_CARRIES_JOINT_PRECISION_AND_COARSE_GRAINING_CARRIES_A_CLOCK.md)
uses the boundary/interior split

```text
L = [[A,B],[B*,D]],     D ≻ 0,
E = [I;−D⁻¹B*],        S = A−BD⁻¹B*,
dF_B = ½ y*(dS)y + (θ/2) tr(D⁻¹dD),      θ=k_B T in the thermal instance.
```

These are real Gaussian coordinates, or complex modes realified with their multiplicities kept;
all frames, units, clocks and the physical reference measure are transported. The variation holds
at fixed boundary state, temperature, dimension and measure. Other varying quantities contribute
their own differentials. The conditional interior integral only needs `D>0`; positivity of `S`
is a further fact, not supplied by that integral.

[derived] Add one reached rank-one contact, `L(w)=L₀+w h h*`, on a fixed carrier. Split
`h=(h_B,h_I)` and define at `w=0`

```text
r = h_I* D₀⁻¹ h_I,        a = h_B−B₀D₀⁻¹h_I = E₀* h.
```

The determinant lemma and the inverse rank-one formula give

```text
S(w) = S₀ + [w/(1+w r)] a a*,
det D(w)/det D₀ = 1+w r,
F_B(w)−F_B(0) = w|a*y|²/[2(1+w r)] + (θ/2)log(1+w r).
```

They apply while `D(w)>0`; in particular for `w≥0`. Here `r` is the interior's susceptibility to
this contact, and `a` is the contact after the interior has responded. Differentiation gives

```text
dF_B/dw = |a*y|²/[2(1+w r)²] + θ r/[2(1+w r)].
```

The first term is the reached boundary strain; the second is the change in the interior's
conditional fluctuation volume. This is an actual insertion law, not a claim that every new
geometric crossing is already an electrical or mechanical contact. Its source must be a reached
port/incidence or an explicitly introduced constitutive relation.

### 1.1 The determinant is combinatorial potential on a contact graph

[standard; derived join] If `L=d* diag(w_e)d` is a scalar weighted graph Laplacian and the boundary
vertices are held, the all-minors matrix-tree identity gives

```text
det D = Σ_F ∏_(e∈F) w_e,
```

where `F` ranges over spanning forests with exactly one held boundary vertex in each tree.
For one held vertex these are spanning trees. Every interior component must reach a boundary,
which is exactly what makes `D` invertible. Consequently

```text
∂ log det D / ∂ log w_e = Prob_F(e∈F)
                       = w_e h_(e,I)* D⁻¹ h_(e,I).
```

Thus the trace term is the change in the weighted population of connecting structures. It is not
an unspecified information metaphor. The graph/forest interpretation is special to this scalar
Laplacian; the determinant identity survives for general forms, while their combinatorial
expansion can carry signs and complex phases. Source: [Lyons and Peres, *Probability on Trees and
Networks*](https://rdlyons.pages.iu.edu/prbtree/).

## 2. RH: substitute the actual conditioned Weil shell

### 2.1 The old path already names the right operator

[owned] The atlas rows `rh.conditioned-effective-tension`, `rh.weil-support-induction`,
`rh.prime-admission-cross-shell` and their paper owners state the following. On the old
Mellin-conditioned body and one added support shell,

```text
q(x+J̃y) = x*A_o x + 2 Re(x*C y) + y*D_s y,
A_o ≻ 0,
S_R = D_s−C*A_o⁻¹C,
q(x+J̃y) = ‖A_o^½(x+A_o⁻¹C y)‖² + y*S_R y.
```

The names in the preceding formula therefore substitute as
`D → A_o`, `A → D_s`, `B → C*`. On a finite section, the boundary variation is exactly

```text
dF_R = ½ y*(dS_R)y + (θ/2) tr(A_o⁻¹dA_o),
dS_R = dD_s−dC*A_o⁻¹C−C*A_o⁻¹dC+C*A_o⁻¹(dA_o)A_o⁻¹C.
```

For RH, `θ` is the scale of this Gaussian variational reading, not a measured physical bath.
An infinite-dimensional determinant requires its relative/regularized construction and trace
class hypotheses; finite sections do not silently supply it. The source's archimedean, prime,
polar and boundary terms remain the completed Weil form, at its fixed zero of energy.

The Hessian in the shell coordinate is `S_R`. The log-determinant term is independent of that
coordinate at fixed linear constitution, so it cannot repair a negative shell direction by an
entropy offset. The equation instead identifies the two distinct returns we must track when the
support, metric or prime population changes.

### 2.2 Prime admission acts through the compensating old face

[owned] The new shell is not detached. For the old and shell moment maps `M_o,M_s`, its
conditioned lift carries

```text
K = −M_o* (M_o M_o*)⁻¹ M_s,        J y=(K y,y).
```

The owner distinguishes this Hilbert lift from the form-domain lift when the support cut is
sharp. The formulas below use a common finite section or a valid common form-domain chart.
A newly admitted prime is a raw cross

```text
V_p = [[0,B_p],[B_p*,0]].
```

Its conditioned shell diagonal is already `K*B_p+B_p*K`. This fact is in
[conditioned support shorting](../papers/source/mathematics/theorems/conditioned-support-quotient-shorting.typ).

[derived] Let `ι` embed the conditioned old body into the raw old space, and let the *relaxed*
old component accompanying a shell direction be

```text
X = K−ι A_o⁻¹C.
```

Vary only the coefficient `α` of this raw cross, keeping the receiving moment maps fixed. Since
its old/old block is zero, `dA_o/dα=0`. By the envelope identity for the relaxed form,

```text
∂S_R/∂α = X* B_p + B_p* X,
∂F_R/∂α = Re ⟨Xy,B_p y⟩.
```

The conditional log-determinant term has zero direct variation in this particular admission.
The prime's effect is the pairing between the new cross and the old body that conditioning and
relaxation actually return. The sign of `B_p` here includes the source's explicit-formula sign.
This is the concrete derivative of the outstanding successor tension, not a new positive term
assigned independently to each prime. When the aperture or conditioning itself moves, its
additional variations return as well.

For the first nontrivial cell the existing target is
`S_(2,3)=D_(2,3)−Y_(2,3)*Y_(2,3)≥0`; the formula above tells us which source pairings determine
that tension. The global route is the same uniform conditioned successor law over the nested
support apertures, with the old radical/range condition carried if a strict gap is lost.

### 2.3 The ternary bridge is already an RH owner

[owned] In the first prime-active aperture, the finite prime term is a partial-isometry hinge

```text
T_a=V_a+V_a*,       T_a²=P_L+P_R,       spec(T_a)={−1,0,+1}.
```

The eigenfaces are the anti-aligned boundary pair, the untouched central fibre, and the aligned
boundary pair. Its coefficient and the archimedean remainder come from the zeta screw kernel;
the existing source inequality is `H_a−(log 2/√2)T_a≥0`.
[First-prime hinge](../papers/source/mathematics/lemmas/first-prime-fixed-domain-hinge.typ).
This is an exact instance of the three polarized sectors with a parameter controlling which
boundary strips can meet. The three sectors alone do not decide the completed shell sign; their
coupling to the old compensator does (§2.2).

### 2.4 The cyclotomic and zero-gas paths meet the same logarithmic derivative

[owned; derived specialization] Claude's
[Galois-gap record](2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md)
keeps two different orbit readings:

```text
Tr_(Q(ζ_n)/Q)(ζ_n)=μ(n) ∈ {−1,0,+1},
N(1−ζ_n)=Φ_n(1)=exp(Λ(n)),       n>1.
```

The first statement is the *primitive* cyclotomic trace, not every relative trace or every
Ramanujan sum. On the real primitive mode subspace of the `n`-ring, the positive gap operator has
eigenvalues `|1−ζ_n^j|²`, one for each primitive character (conjugates give two real directions).
Its determinant is `Φ_n(1)²`. Thus the conditional Gaussian contribution of this isolated gap
block, in the normalized metric, is

```text
(θ/2) log det D_n = θ log Φ_n(1) = θ Λ(n).
```

This directly inserts the cyclotomic norm into the thermal determinant face. The completed RH
comparison still weights and joins those prime-power terms at their log addresses.
Indeed the existing Euler-metric owner states

```text
∂_σ log|1−p^(−σ−it)|² = 2 log p Σ_(m≥1) p^(−mσ) cos(mt log p),    σ>0.
```

It is precisely a local logarithmic-determinant variation; its half-density face at `σ=1/2`
returns the symmetric prime-power current. Prime summation and the archimedean completion retain
their convergence/regularization laws.

On the other side, a finite zero divisor `f(z)=∏_j(z−ρ_j)` reads
`d log f=Σ_j(dz−dρ_j)/(z−ρ_j)`, the trace of a diagonal resolvent. The existing heat/Cole–Hopf
owner turns that log derivative into the zero-gas Burgers current. This is a complex log with its
branch and exterior-tail term, not a positive Gaussian integral over those complex factors.
The source-to-seam issue at time zero stays exactly where `Zeta/ZeroTube` and the
[zero-gas record](2026-09-26_THE_ZERO_GAS_IS_A_COMPLEX_BURGERS_FLOW_AND_RH_NEEDS_A_SOURCE_LAW_AT_TIME_ZERO.md)
place it. These two log-derivative faces are now joined to the same variation, without replacing
the source by a determinant assembled from an assumed zero placement.

## 3. Hodge and sheaf gluing: the zero sector stays explicit

[owned; derived application] On a declared finite Hilbert complex or cellular-sheaf cochain
complex, `d²=0`,

```text
Δ_k=d_(k−1)d_(k−1)*+d_k*d_k,
C^k=im d_(k−1) ⊕ ker Δ_k ⊕ im d_k*.
```

The owners are `Coupling/HilbertTransportChain`, `HilbertReceiverForm` and
`HilbertTransportSpectrum`; the current/overlap routes supply the actual source and gluing maps.
Apply interior elimination to the positive nonharmonic sector or to a Dirichlet interior with no
harmonic kernel. Its effective boundary form and conditional fluctuation return are precisely
`S_k` and `tr(D_k⁻¹dD_k)`. With a constant-rank harmonic kernel, the nonzero spectral factor reads

```text
d log det′ Δ_k = tr(Δ_k^+ dΔ_k).
```

The prime marks the nonzero sector; the kernel and its transported classes are retained
separately. A sheaf restriction that fails to commute with incidence or future transport returns
its gluing/continuation defect. A projected path crossing becomes a contact only through its
actual shared incidence and restriction maps.

For the Hodge conjecture, the colorless sector is the rational `(p,p)` population fixed by the
Hodge-circle action. The source question is its realization by algebraic cycles:

```text
cl: CH^p(X)_Q → H^(2p)(X,Q) ∩ H^(p,p)(X),
obstruction = coker cl.
```

This is the existing `HodgeSmoothProjectiveReceiver` and `hodge.colourless-classes-weil` route.
The determinant variation controls nonharmonic response around the class; it does not manufacture
a representative of a nonzero cycle-class cokernel. Hence the joined object must retain both the
positive response on the moving complement and the actual cycle-class map on the zero sector.
The sphere/product current owners already build concrete source classes and their receivers;
whole-family spanning and higher-codimension algebraic comparison remain the named source terms.

[derived] A neck losing its conducting contact can turn a small positive eigenvalue into an extra
harmonic direction. If one nonzero mode `λ(a)` approaches zero with all other modes regular, its
conditional contribution is

```text
F_mode=(θ/2)log λ(a),       dF_mode=(θ/2)dλ/λ.
```

The divergence identifies a mode that can no longer be integrated out. At the crossing, retain it
as a new coordinate/class, or use the actual nonlinear constitution. Continuing an ordinary
inverse or a fixed-rank determinant through that crossing would erase the very degree of freedom
the receiver has just acquired.

## 4. A bridge is a change in attainable transport

### 4.1 Conductive distance and the return clock

[derived] In the ideal open-circuit limit there is no conducting path between two terminal
regions. Their conductive effective resistance is infinite. On forming a connected path of
conductances `g_e>0`, the simple serial path has

```text
R_path=Σ_e 1/g_e,       g_path=1/R_path.
```

Parallel paths and interior loops are combined by the actual Schur reduction. For a slender
uniform channel, `g=σ A/ℓ` supplies the spatial/constitutive source of the edge weight.

Two relaxed regions with capacities `C₁,C₂` joined by conductance `g(t)` obey

```text
C₁ V̇₁=−g(V₁−V₂),      C₂ V̇₂=g(V₁−V₂),
δ̇=−λ_bridge(t)δ,        λ_bridge=g(t)(1/C₁+1/C₂),
δ(t)=δ(0) exp[−∫₀ᵗ λ_bridge(s)ds].
```

The bridge does two things at once: it makes the difference mode reachable by that transport and
sets the clock on which the two regions can equalize. Effective distance is therefore indexed by
an action, material and receiver. Spatial separation and electrostatic/capacitive coupling already
exist before a lightning channel; what is created is a new *conducting* route with its own finite
return. Real air also has leakage, so an open circuit is the idealized limit of that channel law.

### 4.2 Lightning supplies the constitutive founding law

[physical instance] A cloud-to-ground flash is not selected by globally aligning every charge.
A locally enhanced electric field creates and extends ionization fronts; channel heating and
chemistry can support leader development; connection with an upward leader permits the large
return-stroke current along the established route. The evolving channel changes the field that
steers its next growth. The repository already owns this loop as `em.streamer-drift`,
`heat.leader-breakdown`, `fluid.plasma-source` and the
[fluid/reflection guide](../../docs/FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS.md).
[Streamer physics](https://arxiv.org/abs/2005.14588) and
[observed leader development](https://doi.org/10.1029/2023JD039262) supply physical sources.

The local multiplication/attachment balance can be read in a drift-diffusion chart as

```text
∂t n_e + div Γ_e = (α_ion−α_attach)|v_d| n_e + S_photo − S_recomb,
σ ≈ e μ_e n_e,        heat input = j·E.
```

The coefficients depend on local field, density and composition; thermal transport and gas motion
enter their own equations. The field must sustain ionization and the channel's losses while the
reached material changes. No threshold derived from a Gaussian log determinant alone decides
lightning onset. The rank-one formula gives the *returned response once a contact is made*;
ionization, source work, heating and transport determine whether that contact is made and maintained.
An imposed voltage and an isolated charge require different work accounting, so the positive
fixed-boundary derivative in §1 is not by itself a growth rule for a voltage-driven channel.

The operational formulation of Brandon's bridge lens is thus: a possible adjacency is not yet an
available transport; the reached constitution founds the route and the route alters subsequent
reach. This is the same consumer required for Athena's learned contact geometry.

## 5. Necks, lenses, pinches and relativistic clocks

[derived instances] A diffusive neck of area `A` and length `ℓ` has `g=κA/ℓ` in its slender-channel
regime. As the neck closes, `g→0`, the inter-region difference mode's rate tends to zero, and its
relaxation time diverges. At a disconnection a new independent constant mode appears. The Hodge
zero sector has changed; the inverse and determinant on the old sector cannot continue unchanged.
Acoustic, electromagnetic and fluid necks carry their own frequency-dependent impedance and
storage, not just this resistive limiting face. The preceding contact/clock record supplies
`C_eff=Λ′(0)` where its low-frequency reduction applies.

For a focusing family of paths with transverse Jacobi map `J(λ)`, its cross-section changes as

```text
d log|det J|/dλ = tr(J⁻¹J̇) = expansion.
```

This is the same logarithmic-derivative algebra as the determinant term, applied to a different
operator: the geometrical path Jacobian. At a caustic a transverse direction becomes singular in
that projection. In a four-dimensional Lorentzian spacetime the affinely parameterized null
congruence obeys the Raychaudhuri relation

```text
θ̇ = −θ²/2 − σ_ab σ^ab + ω_ab ω^ab − R_ab k^a k^b.
```

The [Raychaudhuri review](https://arxiv.org/abs/gr-qc/0611123) supplies this focusing relation.
It gives the actual focusing source from shear, twist and curvature; a caustic or horizon reading
is not automatically a curvature singularity. The repository's
[singular-aeon record](2026-10-09_A_SINGULARITY_IS_READ_BY_ITS_RECEIVERS_CLOCKS_AND_MARKS_THE_EPOCHS_THAT_ACCUMULATE_AT_IT.md)
already carries the unequal clocks of horizons, neckpinches and fluid singularities. The
Lorentzian field's characteristic cone comes from its principal symbol and constitution; a
thermal determinant is taken on its declared positive fluctuation sector in a local receiving
frame, not on an indefinite spacetime metric as though that were a Gaussian covariance.

The relativistic source remains the stress–energy tensor and its flux. The kinetic source is
`f(x,v,t)` with a collision law for a gas and electromagnetic coupling for a plasma. Macroscopic
pressure, heat, charge and fluid velocity are its receiver moments. This is the existing
`fluid.kinetic-level` join, which is not replaced by naming all of them one scalar potential.
Complex Euler/NS retains its own `a+ib` exchange term; the magnetic stretch in MHD has the distinct
sign already carried by `fluid.complex-energy-exchange` and `fluid.mhd-elsasser`.

## 6. One clock with three polarized response sectors

[owned; derived synthesis] Claude's October 26 primitive trace gives `μ(n)∈{−1,0,+1}`. Its
[neutral-scope follow-up](2026-10-26_NEUTRAL_IS_A_RATIO_OF_ONE_AGAINST_WHERE_THE_RECEIVER_STANDS_AND_THE_SCOPE_DECIDES_WHAT_A_COLOUR_READS.md)
places neutrality against the receiver's existing ratios and scope. The RH hinge (§2.3) gives a
second exact ternary receiver, on a different operator.

A general Hermitian response `S` has spectral projectors

```text
P₋+P₀+P₊=I,        sign(S)=P₊−P₋,
ψ=P₋ψ+P₀ψ+P₊ψ.
```

A clock parameter together with these three oriented response sectors realizes the proposed
fourfold description at the receiver. The sectors retain their amplitudes, phases and internal
multiplicities; the three labels are their coarse face. Reversing an orientation can exchange the
two signed readings. A null response is defined relative to the receiver; it need not mean absent
motion or a globally undetermined state. A larger future family can reopen a presently null mode.

In a width-`w` binary chart, complement and arithmetic opposition keep their origin and carry:
`NOT(x)=2^w−1−x`, while `−x mod 2^w = NOT(x)+1 mod 2^w`. In a phase chart, multiplication by
`−1` is the half-turn. These are related directional operations at their respective frames;
the extra carry is part of the comparison, not a discarded detail.

[physical instance] A pumped mode near a supercritical pitchfork has the real normal form

```text
ẋ = a x − b x³ + h,       b>0,
V(x)=−a x²/2+b x⁴/4−h x.
```

At zero bias, `a<0` has a stable central state; `a>0` has stable states `±√(a/b)` and an unstable
central state. A receiver can report the two locked sheets and the central face, while the mode
still carries a continuous amplitude and its conjugate quadrature. Near `a=0` the quadratic
Gaussian description loses its gap and the quartic term must participate. This joins the
log-determinant singularity in §3 to the already-owned parametron bifurcation, rather than
integrating away the critical mode. A general pump can have other bifurcations; this specifies the
normal-form regime. Recent [coupled Kerr-parametron experiments](https://arxiv.org/abs/2504.04254)
implement related phase-state computations and demonstrate why the actual coupled mode diagram
matters.

## 7. Sisyphus: the limit is read in the accumulated spectral clock

[derived] For a fixed gap mode or a declared scalar difference obeying
`ė=−λ_R(t)e`, define the receiving clock

```text
τ_R(t)=∫₀ᵗ λ_R(s)ds,       e(t)=e(0)e^(−τ_R(t)).
```

Approach to zero occurs exactly when this clock diverges; reaching a receiver grain `δ>0` occurs
when `τ_R≥log(|e(0)|/δ)`. Infinitely many subdivisions or repetitions alone say nothing about
that integral. A decaying interaction can have finite total spectral time and leave a nonzero
residual forever. Conversely a convergent infinite series has a mathematical limit whether or
not a body can realize the interaction required to attain its face. The physical obstruction is
which continuation and receiving clock the actual system admits.

For a general linear dissipative field with a fixed metric and a gap bounded below by `λ_R(t)`
on its nonharmonic sector, the same integrated clock gives a norm bound; it is not an equality
for every mode of a changing noncommuting operator. A moving metric adds the existing rate-form
terms. A recurrent helical path with no transverse contact may preserve a nonzero mode through
every turn. Founding an actual contact changes the available generator and can move that mode;
drawing an imagined chord across the helix changes no transport. The held momentum of the
body/limbs and the boulder belongs to the continuing state, not to a token count of attempts.

Thus the limit relevant to release is a receiver's distinguishability limit reached under actual
incidence and accumulated action. The formal topological limit, the receiver grain and the time
needed to reach it remain distinct faces of the same specified passage.

## 8. Finite energy and time give a spectral geometry of reach

[standard; derived join] This makes the bounded-computation question quantitative. In a declared
linear action chart, or a stated linearization with its residual retained, let

```text
ẋ=A(t)x+B(t)u,       x(0)=0,
W_T=∫₀ᵀ Φ(T,t) B(t)B(t)* Φ(T,t)* dt,
```

with the actuator/energy metric absorbed into `B`. The least integrated quadratic control effort
needed to reach `x` at time `T` is

```text
E_min(x,T)=x* W_T^+ x,     x∈range W_T;
unreachable by these controls otherwise.
```

To derive it, take the endpoint map `A_T u=∫Φ(T,t)B(t)u(t)dt`; then
`W_T=A_T A_T*`, and the minimum-norm lift is `u=A_T*W_T^+x`.
At effort budget `E₀`, the reached region is the ellipsoid `x*W_T^+x≤E₀` on that range.
The eigenvectors are the directions available to action, and the small eigenvalues price the
directions that are expensive in the available time. This is the finite-horizon form of the
existing `Holon/Element.KineticFace` minimum-energy lift, applied to the actual input-to-state
map, rather than an unrelated scalar distance. [Boyd and Barratt](https://web.stanford.edu/~boyd/lcdbook/lcdbook.pdf)
give the controllability-Gramian geometry.

At fixed reached rank `r` and transported volume measure,

```text
Vol(reached ellipsoid)=Vol(unit ball_r) E₀^(r/2) √det′W_T,
d log Vol = ½ tr(W_T^+ dW_T) + (r/2)d log E₀.
```

This is the requested finite spatial/temporal potential in the same trace calculus. On the reached
subspace the energy metric is `D=W_T⁻¹`, so
`d log det D = −d log det W_T`. The inverse-volume contribution in the free energy is exactly the
opposite face of the expanding attainable region. A physical interpretation as energy requires
the input quadratic form to be the actual work law; otherwise it is the declared control effort.
The ideal-gas `pV=Nk_BT` is the familiar Gibbs volume instance, while this ellipsoid is a
constituted anisotropic reach volume, not an assumption that every ecology is an ideal gas.

For a problem whose admitted solution consequences form a set `Y`, its physical reach cost is
`inf_(x∈Y∩range W_T) x*W_T^+x`; finding the target and its required control remains part of the
situated computation. This separates inaccessible directions from merely expensive ones and
makes cultivation's changes in `A`, `B`, storage and incidence measurable. Chaotic sensitivity by
itself does not supply all of those directions or the controls to use them.

## 9. Cayley graphs, games and the tropical limit of path populations

[owned; derived join] On a declared move graph, a directed edge carries the actual action and its
cost. A word is a path. The [Rubik record](2026-09-19_RUBIK_FACES_LIFT_TO_TORUS_INTERSECTIONS_AND_NAVIGATION_GRAPHS.md)
already owns the quotient/lift and cost-sensitive navigation law. For positive costs define
`W_β(i,j)=Σ_(edges i→j) exp(−β c_e)`. Where `ρ(W_β)<1`,

```text
G_β=(I−W_β)⁻¹=Σ_(m≥0)W_β^m,
−log det(I−W_β)=Σ_(m≥1)tr(W_β^m)/m.
```

The resolvent sums weighted walks from a source to a receiver; the determinant sums closed
returns. For a finite graph with strictly positive edge costs and a reachable target,

```text
−β⁻¹ log G_β(i,j) → shortest action cost(i,j),       β→∞.
```

Finite `β` retains route multiplicity as well as cost. This is the tropical path limit joined to
the same inverse/determinant calculus. In a symmetric positive Gaussian realization `D=I−W_β`,
its log determinant enters §1; directed games retain their transition law rather than inheriting
that Gaussian positivity automatically. `fractal.graph-directed-words` and the existing SSM
resolvent already own the finite word-count and transfer-determinant forms.

- **Rubik:** the Cayley graph uses the declared generators. Its diameter is 20 in the face-turn
  metric and 26 in the quarter-turn metric ([primary result](https://www.cube20.org/),
  [quarter-turn result](https://www.cube20.org/qtm/)); the physical clock and energy can give further
  weighted distances on the same group. God's number is a maximum shortest-path length; an actual
  navigating policy is another carried object.
- **Chess:** the game state includes the move rights and history information required by the rules.
  Its adversarial target uses alternating choices, so the appropriate zero-temperature recurrence
  is minimax on the game graph. A single ordinary shortest-path metric does not encode an opponent.
- **Unique Games:** labels are local sections and edge permutations are transport constraints;
  frustration and loop holonomy read their incompatibility. The October 26 diffusion record already
  joins the connection spectrum, near-consistent keys and slow modes. These are the local
  problem–solution geometries to cultivate, not a universal equality of algorithm classes.

With at most `d` choices per crossing there are at most `d^m` action words of length `m`, but many
can return to the same state. The reached volume therefore depends on incidence, relations and
contractions; it need not grow exponentially with a spatial radius or a receiver's time. This is
where a culture can compress many words into a continuing relation while preserving the
consequences that its future distinguishes.

## 10. The unified consumer

[research join; agent-inferred] The same reached contact changes (i) boundary response, (ii)
interior fluctuation volume, (iii) the clock and effort of attaining a consequence, and sometimes
(iv) the retained kernel or accessible region. The formula supplies the variations of these
faces; their physical source remains the constitution and the actual boundary work.

For Athena the consumer is the contact's current joint fibre and its continuing response, with
its comparison returned through the same operands. The decisive object is not an isolated ternary
label, an unclocked scalar, or a drawn shortcut: it is the material relation whose action actually
reaches the next participant. This joins the current campaign's packet, deposition, mode retention,
news clock and action-sufficient continuation owners. No separate arithmetic solver, chess engine
or prime oracle is inserted. RH, Hodge and the fluid/singularity routes remain attached at the
specific operators above, rather than being grouped as a separate application category.

The new research results in this record are the consuming joins and the explicit contact/Weil
variations. The classical linear-algebra, spectral, control and forest identities keep their stated
hypotheses. The record contains no learning run and no claim that the unbuilt kinetic or
contact-selected-grain consumers already execute.
