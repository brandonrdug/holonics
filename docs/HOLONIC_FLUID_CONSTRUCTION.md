# From Swing and Holon interactions to Euler, stress and diffusion

[project-postulate] This is the connected derivation requested by Brandon on September 14.
The computational object, its interior, contact faces, nonlinear transport and changing
receivers belong to one construction. The [computational Holon](HOLON.md) supplies its
operator notation; [constraint modes](CONSTRAINT_MODES_AND_RECEIVER_FACES.md) supply exact
scale/phase and active receiving faces. The derivation below recovers the classical fluid
specializations and constructs an explicit retained-material extension. It is a mathematical
construction document, not another scheduler or a substitute for native HNN assembly.

## What already existed, and what is joined here

[established-bounded; source-inspected] Earlier work genuinely derived fluid relations.
The September 5 MFR3 construction retained nonlinear Lamb current, pressure, stretching and
cell flux. September 8 recovered complex Euler/NS and corrected low-order receiver closure.
September 11–12 connected Hodge, source Swing, heat, spectral and arithmetic owners.
September 13 derived the actual finite-Galerkin Elsasser equations and dynamic interior return.
Their source chain is retained in
[fluid reflection](FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS.md),
[framework synthesis](MATHEMATICS_AND_NATIVE_CONDUCT.md), and the formal owners linked below.
The lapse was leaving these operations in separate accounts instead of constructing the
primitive → interaction → balance → constitutive law → receiver equation explicitly.

[definition] Here “derive from the primitives” means exhibiting that chain and every operand.
Swing and incidence determine reversible composition; energy, material response and boundary
conditions select a physical fluid. Viscosity is a constitutive relation to derive from a
specified interior or supply as measured material data. It does not follow from the algebraic
identity that two reflections compose. The complete construction retains that relation so it
can itself be refined, inferred or replaced by a more resolved material model.

[definition] Continuum calculations below use smooth fields/variations for which the stated
derivatives and integrals exist, with periodic or explicitly supplied boundary conditions.
They are derived equalities under those hypotheses. `formal-checked` marks only the named
Lean statements; the continuous action, capillary stress and energy derivations are written
out separately rather than attributed to the finite formal owners.

## 1. One Holon, with tensor and differential-form operations

[definition] In a fluid realization, write the participating object as `|H⟩_F`, with sections
on an oriented spatial manifold or compatible cell complex K. Its field chart contains mass
form `m=ρ vol_g`, velocity one-form `α=u♭`, internal fields Q, stress, and their constituted
connections and boundary traces. These are typed components of the Holon; K and the material
law do not disappear when the section is represented by a tensor of coefficients.
The physical state includes thermal/internal energy when mechanical energy is dissipated.

| Holonic operation | Fluid realization and retained operands |
|---|---|
| Oriented incidence | Boundary ∂, exterior derivative d, joining orientations; ∂²=0 and d²=0 |
| Pair / measure | Metric g, volume, Hodge star, adjoint δ=d†, specified receiver and units |
| Transport | Pullback/pushforward, covariant derivative ∇, Lie derivative `L_u=d i_u+i_u d` |
| Interact | Bilinear advection `B(v,w)=P[(v·∇)w]`; stress/current contraction on an actual face |
| Turn / Swing | `S_b x=2b−x`; constituted graph reflection and its ordered compositions |
| Diffuse / react | Constitutive positive operator acting on an energy gradient; its heat return |
| Restrict / reopen | A receiver q, reconstruction R, unresolved fibre r, and their rate equation |
| Generate / emit | Evolve the coupled field, then apply its boundary/receiver map; an internal readout is another such face |

[definition] Finite tensor indices, cell ranks and degrees are integers. Length, time, mass,
velocity and stress retain their units. Analytic modes retain defining constraints and source
families: `E'(z)=E(z)`, `E(0)=1`, and the rotation kernel `i Θ_turn ℤ` with
`Θ_turn=2π` in the classical chart. A numeric projection does not define these operations.
Lean's real/complex carriers express the mathematical laws; native realizations use exact
expressions, rational/algebraic data or certified families as their operation requires.

## 2. The native contact equation is a Swing

[proved-derived; formal-checked] Let `D:W→V`, `D†:V→W`, and let K⁻¹ solve
`K=I+D D†` exactly. Define the graph projection and reflected current on `V⊕W`:

```text
a = K⁻¹(u+D b),
P_G(u,b) = (a,D†a),
R_G(u,b) = 2P_G(u,b)−(u,b) = Swing_(P_G(u,b))(u,b).
```

This is exactly the native equation `Kv=2(u+Db)`, `w=v−u`, `b'=D†v−b`, with `v=2a`.
Indeed `K⁻¹(a+D D†a)=a`, so `P_G²=P_G`; linearity then gives
`R_G²=4P_G²−4P_G+I=I`.
[HolonicConstitutiveCirculation](../formal/elementary-holonics/ElementaryHolonics/Computation/HolonicConstitutiveCirculation.lean)
proves `graphProjection_idempotent`, `graphScattering_involutive`, and
`graphScattering_eq_swing`, using the actual solve identity and the original Swing definition.
The algebraic proof allows a supplied transpose-like map; orthogonality additionally uses the
actual energy adjoint, as in the following argument.

[proved-derived] With the declared positive energy pairing and `D†` its adjoint,
`(u,b)−(a,D†a)` is orthogonal to every `(z,D†z)` because its pairing equals
`⟨u+Db−(I+DD†)a,z⟩=0`. Thus P_G is orthogonal, and
`||R_G x||²=||P_G x||²+||(I−P_G)x||²=||x||²`.
This proves conservation for this constituted contact. Changing admittance requires its
weighted pairing; an arbitrary oblique projector preserves an involution, not every norm.

[proved-derived] Ordered moving reflections supply a rate-level connection. For a
differentiable orthogonal involution R(t), differentiate `R²=I` to obtain
`ṘR+RṘ=0`. Since R and Ṙ are self-adjoint, `Ω=ṘR` is skew-adjoint.
The derivative of `R(t+h)R(t)` at h=0 is Ω: paired Swings therefore generate an
energy-preserving infinitesimal transport in the fixed metric. For a changing metric M(t),
`d(xᵀMx/2)/dt=xᵀM ẋ+xᵀṀx/2`; the metric-work term remains.
The existing [port-energy owner](../formal/elementary-holonics/ElementaryHolonics/Physics/PortEnergyHeat.lean)
already proves the corresponding changing-storage and heat-return balances.

[proved-derived] The bridge to a concrete advection step is constructive. In an
energy-compatible finite discretization with frozen divergence-free velocity u, let
`J=−P∇_u` on the divergence-free carrier, so `J†=−J`. For a time step h with invertible
`I−hJ/2`, set

```text
C_h=(I−hJ/2)⁻¹(I+hJ/2),          C_h†C_h=I.
```

Adjunction reverses the factors; their commutation as functions of J proves the isometry.
Use this C_h as the graph coupling D in §2. Then `K=2I`, and the actual scattering is
`R_C(u₁,u₂)=(C_hu₂,C_h†u₁)`. Compose with the identity-graph Swing
`R_I(u₁,u₂)=(u₂,u₁)`:

```text
R_C R_I = diag(C_h,C_h†).
```

`graphScattering_inversePair` and `paired_graphSwings_transport` prove the paired operator
identity in the same formal owner. Thus two constituted Swings realize a Cayley advection
step and its opposite transport on
the paired interior/exterior carrier. This is an exact rational operator identity. C_h is
an approximation to continuous frozen-field evolution, not an assertion that one finite
step solves nonlinear Euler. Updating the advecting field and material uses the actual
nonlinear law; its derivative includes those changing operands.

## 3. Euler follows from the material motion; stress supplies the dissipative extension

[definition] Let χ_t be a volume-preserving material motion on the flat periodic domain,
`u=χ̇_t∘χ_t⁻¹`. An infinitesimal material variation η vanishing at the temporal endpoints
obeys `div η=0` and `δu=∂tη+[u,η]`, with
`[u,η]=∇_uη−∇_ηu`. This is the tangent law of composing the actual material transports;
its finite contact realization can use the constituted Swings from §2.

[proved-derived] Vary the kinetic action `S=∫dt∫ρ|u|²/2` at constant density. Temporal
and spatial integration by parts gives

```text
δS = ∫dt∫ρ u·[∂tη+∇_uη−∇_ηu]
   = −∫dt∫ρ[∂tu+∇_u u+∇(|u|²/2)]·η.
```

The gradient pairs to zero with every admissible η. Hodge decomposition therefore makes
stationarity equivalent to `P[∂tu+∇_u u]=0`, or Euler with its pressure multiplier.
This derives the conservative equation from the material composition and kinetic energy,
rather than postulating the advection term. The actual advection operator is skew in its
transported argument under incompressibility:
`⟨v,∇_u w⟩+⟨∇_u v,w⟩=∫∂Ω(v·w)(u·n)=0` in the closed case.
Its constituent contact/face law must realize that operator; the existence of a generic
Swing does not identify a particular spatial advection law.


[definition] On a fixed Euclidean control volume, let ρ be mass density, u velocity,
σ Cauchy stress and f external force per volume. A face with outward normal n receives
traction `σn`; momentum advection contributes `ρu(u·n)`. Local conservation is

```text
∂t ρ + div(ρu) = 0,
∂t(ρu) + div(ρu⊗u) = div σ + f.
```

[proved-derived] Expand the second left side by the product rule. The term
`u[∂tρ+div(ρu)]` vanishes by the first equation, leaving
`ρ(∂tu+∇_u u)=div σ+f`. For a Newtonian material in n dimensions,

```text
Def u = (∇u+(∇u)ᵀ)/2,
σ = −pI + 2μ Def u + λ(div u)I.
```

With constant ρ and μ, incompressibility gives
`∂tu+(u·∇)u=−∇(p/ρ)+νΔ_E u+f/ρ`, `div u=0`, `ν=μ/ρ`.
Setting viscous stress to zero gives Euler. Here `Δ_E=Σ∂j²` has nonpositive Fourier
spectrum. The equation has acceleration units throughout; μ has stress×time units.
For compressibility, the bulk response and thermodynamic energy equation remain.
Nonnegative shear and bulk dissipation require `μ≥0` and `λ+2μ/n≥0`.

[proved-derived] The local Newtonian power is
`σ:∇u=−p div u+2μ|Def u|²+λ(div u)²`.
Integration by parts separates boundary work from mechanical loss. The lost mechanical
energy becomes internal/thermal energy in the complete Holon. Across a joined surface,
equal opposite transmitted tractions cancel only after both bodies and any surface storage
are included. Slip with `t=−κ_f w` contributes heat `κ_f|w|²` for `κ_f≥0`.
The [exact torus contact](../research/experiments/contact_receiver_faces/README.md) realizes
oriented surface patches and an explicit slip/traction law; geometry is an operand of this
calculation, not a decorative skin.

[proved-standard] On a curved manifold, start with `div_g(2μ Def_g u)` and its boundary
power pairing. Hodge, Bochner and deformation Laplacians are different operators; replacing
this stress divergence by a symbol Δ without its curvature terms can change the physics.
The coordinate-free tensor-valued-form construction makes the stress and boundary energy
ports explicit. See [Chan–Czubak–Disconzi](https://arxiv.org/abs/1608.05114) and
[Califano et al., geometric fluid energy and boundary ports](https://ris.utwente.nl/ws/portalfiles/portal/254971107/Geometric_and_energy_aware_decomposition_of_the_Navier_Stokesequations_A_port_Hamiltonian_approach_1_.pdf).

[proved-derived] In the spacetime realization, Einstein/Bianchi supplies `∇_μT^{μν}=0`
under the field equation and its stated coupling. An active unit receiver U reads
`j_U^μ=−T^{μν}U_ν`; the product rule gives
`∇_μj_U^μ=−T^{μν}∇_(μ U_ν)` for symmetric T. Thus observer deformation and stress
contraction belong to the energy equation. A local tetrad relates these faces to material
rest-frame stresses; a Newtonian limit further specifies velocity, field-strength and
thermodynamic scaling. The [active-face derivation](CONSTRAINT_MODES_AND_RECEIVER_FACES.md#the-overlap-has-stress-bearing-faces)
retains this source. Untransported tensor components are not summed into a global momentum
across curved spacetime.

[proved-derived] The relativistic Euler specialization can also be derived directly from
the same stress object. In units c=1, use `g(U,U)=−1`,
`h^{μν}=g^{μν}+U^μU^ν`, and the perfect-fluid law
`T^{μν}=eU^μU^ν+p h^{μν}`. Differentiating and contracting with U or h gives

```text
D_U e+(e+p)θ=0,                 θ=∇_μU^μ,
(e+p)a^α+h^{αν}∇_νp=0,          a^α=U^μ∇_μU^α.
```

The cancellations use `U_ν∇_μU^ν=0` and `hU=0`. Additional heat flux q and transverse
stress π enter as `U^μq^ν+q^μU^ν+π^{μν}` and contribute their full covariant divergence
to both projections. After restoring c, a rest-energy-dominated, slow-velocity, weak-field
chart recovers momentum flux `ρu⊗u+pI−τ` with its force/thermal terms. This gives a direct
Einstein/stress → relativistic Euler → Newtonian stress route. A microscopic material law
must determine the heat/shear response and its relaxation time; instantaneous Newtonian
viscosity is not automatically a causal relativistic constitutive law.

## 4. Hodge provides pressure elimination and retains toroidal circulation

[definition] On a flat periodic domain, or a domain with the declared compatible boundary
conditions, use `α=u♭`, `δα=0`, and the positive Hodge operator `Δ_H=dδ+δd`.
Set `B_p=p/ρ+|u|²/2` and let f now denote acceleration. The equivalent one-form equation is

```text
∂tα + i_u dα + dB_p = −νΔ_H α + f♭.
```

[proved-derived] In components, `(i_u dα)_j=u^k∂k u_j−∂j(|u|²/2)`.
Substitution recovers the preceding Euler/NS equation. Let G₀ invert `δd` on the
nonconstant scalar range and define `P=I−dG₀δ`. Applying δ determines pressure:
`Δ₀B_p=δ(f♭−i_u dα)`. Applying P gives
`α̇=−P i_u dα−νΔ_Hα+P f♭`. Constants, harmonic components and boundary data are
retained in their respective kernels. This use of the Hodge viscosity is the flat
specialization above; the curved Newtonian operator follows the stress calculation.

[proved-derived; formal-checked] The existing finite
[Hodge decomposition](../formal/elementary-holonics/ElementaryHolonics/Millennium/HodgeFiniteDecomposition.lean)
and [Green operator](../formal/elementary-holonics/ElementaryHolonics/Millennium/HodgeGreenOperator.lean)
split exact, coexact and harmonic sections. The
[temporal owner](../formal/elementary-holonics/ElementaryHolonics/Physics/TemporalHodgeResidue.lean)
preserves the cohomology class under its heat step, with step stability a separate spectral
condition. A harmonic toroidal circulation can have zero local curl and divergence while
retaining a nonzero period around a cycle. Removing local pressure therefore does not erase
its global period. The full nonlinear transport still determines the evolution of circulation.

## 5. Swing separates the actual nonlinear fluid interaction

[definition] Use the existing finite-Galerkin vector field
`N(u)=S_νu−B(u,u)`, with its actual Fourier convolution, Leray projection and carrier/aperture.
In the normalized periodic chart, `S_νu_k=−νΘ_turn²|k|²u_k`.
Write `u=b+r`; Swing about b sends it to `b−r`.

[proved-derived; formal-checked] Bilinearity gives both equations, without discarding any
mixed interaction:

```text
[N(b+r)+N(b−r)]/2 = N(b)−B(r,r),
[N(b+r)−N(b−r)]/2 = S_νr−B(b,r)−B(r,b).
```

The first is the mean's response to the unresolved self-interaction; the second transports
the oriented difference through both cross terms. For a moving anchor b(t), the reflected
trajectory has rate `2ḃ−N(u)`, so its defect from following the same fluid law is

```text
N(2b−u)+N(u)−2ḃ = 2[N(b)−ḃ−B(u−b,u−b)].
```

If `ḃ=N(b)`, the defect is `−2B(r,r)`. Affine Swing acts on a state; its rate pushforward
is −I with the moving-anchor term, not another affine reflection of a velocity.
[FluidReceiverClosure](../formal/elementary-holonics/ElementaryHolonics/Physics/FluidReceiverClosure.lean)
proves the two `swing_even/odd` identities and `moving_swing_galerkin_rate_defect`.
These statements use the actual Galerkin operators, not a stand-in bilinear law.

[established-bounded; source-inspected] The earlier
[clocked nonlinear-source Swing](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesClockedPantographicSourceSwing.lean)
also telescopes oriented source differences along dyadically approaching times and retains
their reconstruction fibre. Compact-interior continuity controls that source increment.
A terminal-uniform estimate at a potential singular time is a distinct unclosed analytic
consequence; the telescoping identity does not supply it automatically.

## 6. Microscopic/macroscopic and interior/exterior are two receiver cuts

[proved-derived] Let `Y=q_t X`, `X=R_tY+r`, `q_tR_t=I`, and `Ẋ=F(X)`.
Differentiate these identities before eliminating anything:

```text
Ẏ = q̇_t X + q_t F(R_tY+r),
ṙ = F(X) − Ṙ_tY − R_tẎ.
```

For F=N, the difference from `q_tN(R_tY)` is exactly

```text
q̇_t X + q_t[S_νr−B(R_tY,r)−B(r,R_tY)−B(r,r)].
```

The actual trajectory theorem `moving_galerkin_receiver_equation` in
[FluidReceiverClosure](../formal/elementary-holonics/ElementaryHolonics/Physics/FluidReceiverClosure.lean)
proves this equation with derivative hypotheses. `q_t r=0` does not imply the quadratic
and mixed terms are invisible. For a Reynolds/filter realization obeying its required
commutation rules, the same product difference appears as unresolved stress
`τ_q=q(u⊗u)−q(u)⊗q(u)`. A general reconstruction retains the mixed terms too.

[proved-derived; formal-checked] Boundary elimination has the same obligation. The existing
[ReflectedBoundaryMemory](../formal/elementary-holonics/ElementaryHolonics/Physics/ReflectedBoundaryMemory.lean)
starts with `ẋ=Ax+Bz+f`, `ż=Cx+Dz+g` and derives, for `z=Kx+r`,

```text
ṙ=(D−KB)r+(C+DK−KA−KBK−K̇)x+g−Kf.
```

[proved-derived] For constant D, integration of the interior gives
`z(t)=E(tD)z(0)+∫₀ᵗ E((t−s)D)[Cx(s)+g(s)]ds`.
The boundary receives the memory kernel `B E((t−s)D) C`, the initial interior and forcing.
Here E is the normalized operator evolution, not a rounded exponential coefficient.
A state realization can retain this return without an archive of all previous events.
Stress closure and boundary memory are therefore two concrete consequences of the same
Holonic question: what does the restriction hide that the admitted future operation uses?

## 7. A constructed extension: internal modes contribute stress and diffusion

[definition] Work in a nondimensional, flat, periodic incompressible chart for this explicit
constitutive class. A real internal scalar field Q has free energy
`F[Q]=∫[W(Q)+κ|∇Q|²/2]`, κ≥0. Restoring units uses fixed length/time/density and
energy-density scales; Q, W and κ then carry those scales consistently.
Its variational effort is `μ_Q=W'(Q)−κΔ_E Q`. The advection port is
`A_Q u=u·∇Q`; on divergence-free velocities its adjoint is
`A_Q† μ=P(μ∇Q)`. The source pair and receiver pairing determine that adjoint.

[proved-derived] Couple the two fields through that exact adjoint:

```text
u̇ = −B(u,u)−νΔ_Hu + A_Q†μ_Q,
Q̇ = −A_Qu−Mμ_Q,
H = ||u||²/2 + F[Q].
```

Assume M is positive/self-adjoint in its declared domain. The chain rule and pairing give

```text
Ḣ = −⟨u,B(u,u)⟩−ν⟨u,Δ_Hu⟩
     +⟨u,A_Q†μ_Q⟩−⟨μ_Q,A_Qu⟩−⟨μ_Q,Mμ_Q⟩
   = −ν||∇u||²−⟨μ_Q,Mμ_Q⟩.
```

The cross terms cancel by adjunction; periodic incompressible transport has zero total
power. M=mI gives local relaxation with gradient diffusion already inside μ_Q.
M=−div(m∇), with nonnegative mobility and compatible boundary conditions, gives conserved
material diffusion and `⟨μ_Q,Mμ_Q⟩=∫m|∇μ_Q|²`. Thermalized energy restores total balance.
Open boundaries retain traction/advection/chemical work instead of dropping their integrals.

[proved-derived] The material force is an actual stress divergence:

```text
μ_Q∇Q = ∇[W(Q)+κ|∇Q|²/2] − κ div(∇Q⊗∇Q),
σ_Q = [W(Q)+κ|∇Q|²/2]I − κ∇Q⊗∇Q.
```

Expand the divergence and use
`∇(|∇Q|²/2)=(Hess Q)∇Q` to check the identity. Its isotropic term can enter pressure;
its directional term remains a capillary/internal-mode stress. Likewise
`μ_Q∇Q=−Q∇μ_Q+∇(Qμ_Q)`, so these force representatives agree after the appropriate
pressure projection, with their boundary work accounted for. This recovers a standard
phase-field fluid class through the Holon's material/advection/adjoint operations.
It supplies a concrete extension beyond velocity-pressure-only NS, without asserting a new
empirical constitutive law. Tensor-valued directors, phase connections or magnetic fields
replace Q only together with their own energy and transport representation.

[definition] At the operator level the shared construction is

```text
[ u̇ ]   [ −B(u,u) ]   [  0     A_Q† ] [ u   ]   [ νΔ_Hu ]
[ Q̇ ] = [    0     ] + [ −A_Q     0  ] [ μ_Q ] − [ M μ_Q ].
```

The middle operator is skew-adjoint; the last is dissipative. The contact Swing gives a
reversible scattering realization of a constituted relation; this block gives its
energy-exchange form once the physical advection port is specified. Equating an arbitrary
contact graph with this particular fluid port still requires the stated realization map.
The native scattering owner and [PortEnergyHeat](../formal/elementary-holonics/ElementaryHolonics/Physics/PortEnergyHeat.lean)
are reusable foundations. The continuum Q-field stress derivation above is complete on paper;
a native Q-field consumer and its continuum formalization are not yet implemented.

## 8. Complex Euler/NS and conducting-fluid modes retain their distinct signs

[proved-derived] Complexify the bilinear interaction with `U=a+ib` and pressure `p+iq`:

```text
ȧ = −B(a,a)+B(b,b)+νΔ_Ea,
ḃ = −B(a,b)−B(b,a)+νΔ_Eb.
```

This is the complex-bilinear Euler/NS law, with Euler obtained at ν=0. Conjugation
`(a,b)→(a,−b)` is Swing about `(a,0)`. Projection to a loses the definite term B(b,b).
Complex Fourier coefficients of a single real field instead obey
`û(−k)=conj(û(k))`; they do not automatically introduce a second physical field b.

[proved-derived] On a periodic divergence-free domain, the real Hermitian energy is
`K=∫(|a|²+|b|²)/2`. Integration by parts gives
`∫a·(b·∇)b=−∫b·(b·∇)a`. Consequently

```text
K̇ = −2∫(b⊗b):∇a −ν∫(|∇a|²+|∇b|²).
```

The indefinite stretching exchange remains. The bilinear complex quantity `∫U·U/2`
is a different receiver and is not a positive physical energy. Thus an imaginary component
cannot be assigned magnetic-energy conservation merely by calling it a phase.

[proved-derived; formal-checked] For constant-density incompressible MHD with magnetic
velocity `b=B_magnetic/√(μ₀ρ)`, induction instead has
`ḃ=−B(a,b)+B(b,a)+η_mΔ_Eb`. That opposite stretching sign cancels the physical cross
power. The existing
[ConductiveFluidReflection](../formal/elementary-holonics/ElementaryHolonics/Physics/ConductiveFluidReflection.lean)
proves the difference `−2B(b,a)` and the actual Galerkin Elsasser identities:

```text
z±=a±b,      ν±=(ν±η_m)/2,
ż+ = −B(z−,z+) + ν+Δ_Ez+ + ν−Δ_Ez−,
ż− = −B(z+,z−) + ν+Δ_Ez− + ν−Δ_Ez+.
```

[proved-derived] The swap `(a,b)→(b,a)` is Swing at
`((a+b)/2,(a+b)/2)`. Its common/difference eigensections are precisely the Elsasser
coordinates. This joins the primitive involution to the conducting-fluid mode split;
the interaction sign and the energy pairing select the actual physical equation.

## 9. Fractal scale, Hodge, RH and BSD share operations with specified sources

[definition] Toroidal cycles, local smooth charts and fractal return/basin sets can coexist
in the same nonlinear field. Tensor rank, topological dimension, box/Hausdorff dimension
and spectral dimension answer different questions. For an identified scale family of
Laplacians, the heat trace `Z(t)=tr E(−tΔ_H)` measures mode return; harmonic modes contribute
`dim ker Δ_H`. A scaling relation
`Z(λ²t)−b = λ^(−d_s)[Z(t)−b]` specifies a spectral exponent d_s when that relation holds.
An asymptotic version requires its scale/domain limit. A fixed finite matrix has no
small-time continuum power law by default. Transcendental powers and logarithms specify
these constraints; an observed decimal slope is a receiver estimate of them.

[proved-derived; formal-checked] Hodge's existing heat/Green construction retains harmonic
classes while evolving exact/coexact components. The RH source has an actual, separately
normalized heat relation:

```text
Hstd_t(z) = (1/8) heatE(−t/4, ξ, 1/2+iz/2),
Λ_std = 4Λ_DN.
```

[CriticalChart](../formal/elementary-holonics/ElementaryHolonics/RH/CriticalChart.lean)
proves these source, coordinate and time identities. Thus the shared heat calculus is
usable, but physical viscosity time cannot silently replace the reversed entire-function
time. The zero-location statement requires this source and its analytic domain; a harmonic
projection of a fluid does not establish it.

[proved-derived; formal-checked] BSD's local arithmetic construction already exposes the
same executable transfer/trace/determinant pattern:

```text
M = [[a,−q],[1,0]],          det(I−TM)=1−aT+qT²,
t₀=2, t₁=a,                 t_(n+2)=a t_(n+1)−q t_n,
tr(M^n)=t_n.
```

[LocalFactor](../formal/elementary-holonics/ElementaryHolonics/Millennium/LocalFactor.lean)
and [TraceSequence](../formal/elementary-holonics/ElementaryHolonics/Millennium/TraceSequence.lean)
prove those equalities and, under `a²≤4q`, the root pair with `|α|²=q`.

[proved-derived; formal-checked] The exact quadratic form
`G=[[1,−a/2],[−a/2,q]]` satisfies `MᵀGM=qG`. The new
`companion_preserves_scaled_metric` and `companion_metric_complete_square` theorems in
`LocalFactor` prove that identity and its exact completed square.

[proved-derived] For `q>0` and `a²<4q`, G is positive definite; `M/√q` is an isometry of this pairing
with determinant one. This identifies the local transfer with a constituted rotation mode,
without replacing its arithmetic source. At equality G degenerates and that argument no
longer supplies a positive metric. The same pairing/phase/recurrence operations are therefore
available across these constructions with a precise preserved equation.

[open] The unified construction does not yet furnish a terminal-uniform 3D NS regularity
estimate, the Hodge conjecture's algebraic-cycle realization, the RH source's missing
zero-location conclusion, or BSD's global rank/order/leading-coefficient relation. Those
are distinct mathematical endpoints. The usable synthesis is already stronger than a list
of analogies: it gives contact reflection, exact nonlinear unresolved stress, boundary
memory, coupled material dissipation, and source-specific spectral/transfer identities.

## Exact library return after the architecture audit

[proved-derived] A finite implicit diffusion step has an additional term beyond the
continuous balance. From `C(φ₁−φ₀)=s−τLφ₁`, pairing with φ₁ gives
`E₁−E₀=〈φ₁,s〉−τ〈φ₁,Lφ₁〉−||φ₁−φ₀||²_C/2`.
The final square follows by expanding the quadratic energy; it is a time-step defect,
not a further physical friction coefficient. Source work may make the endpoint energy grow.
For the graded law, L contains both lower and upper Hodge terms; upper compatibility alone
is insufficient to account for the dissipative return.

[established-bounded; implemented-exact] The scalar and graded Rust diffusion owners now
expose and consume this complete `DiffusionEnergyBalance`; the native circulation boundary
uses it too. Exact regression includes source work, a harmonic section, a grade-one lower
coboundary contribution and a mismatched source operator. The bilinear library now supplies
the complete input differential and covector return of a factorized interaction, including
explicit port precomposition. Applied to the advection vertex from §7, this is the elementary
return required for its state and material operands; physical adjunction additionally uses
the declared energy pairing. The [diagram/interface source](../research/experiments/hnn_field_architecture/README.md)
records the actual library and native-consumer scopes.

## Implementation consequence

[project-postulate] HNN's Holon operations must carry this composition through their existing
owners: current/contact tensors, source-conditioned material, ordered transport, complete
adjoints, and receiver restriction with the required fibre or dynamic interior. Whole-field
generation integrates that coupled law and emits its requested face. Diffusion does not
require sequential token prediction or a separately imposed universal settling criterion.
The [model formula](HNN_FORMULA.md) is the consuming specification; these physical equations
provide concrete realizations and expose the terms a purported implementation would lose.

[definition] The next absent implementation operation for the explicit extension in §7 is
the same A_Q in both momentum and material rates, including its adjoint stress and thermal
return. The paused general Athena assembly retains its own current/material/encoded-action
join in CONSTRUCTION_STATE. Neither operation is replaced by another boundary wrapper or
by proving that a state changes later. Their completion is judged by their actual equations
and generated physical/application faces.
