# The Holonic Interaction is a covariant storage--flux complex, and the cusp raises difference order

**Date:** 2026-08-24  
**Kind:** exterior formal-construction and cross-domain synthesis record  
**Station:** I9 of the addressed-transport composition blueprint  
**Truth statuses used:** `definition`, `proved-derived`, `established-bounded`, `interpretation`, and
`open`, each with its evidence tag where applicable.

## 1. Return

[proved-derived; formal-checked] `HolonicInteractionExterior.lean` constructs the second exterior
power of the exact dual cusp monodromy on the geometric torus fibre. In the ordered basis
`e01,e02,e03,e12,e13,e23`, its matrix is

```text
[1 0 0 0 0 0]
[1 1 0 0 0 0]
[0 0 1 0 0 0]
[0 0 0 1 0 0]
[1 0 0 0 1 0]
[1 1 0 0 1 1].
```

[proved-derived; formal-checked] For `D=Λ²M₀-I`, Lean proves `D³=0` and `D²≠0`. The orbit of the
initial plane `e₀∧e₁` is proved at every natural time:

```text
(Λ²M₀)^n(e₀∧e₁) = e01 + n e02 + n e13 + n² e23.
```

[proved-derived; formal-checked] Its second chronological difference is exactly `2 e23`, and its
third difference is zero. The fibre-vector cusp shear is linear, while the induced flux-plane
interaction is quadratic. This is the first exact theorem in the repository in which a
square-zero source transport raises to a genuine difference-of-differences law on an emergent
geometric face.

[proved-derived; formal-checked] The order-three and order-four monodromies remain periodic on
exterior degree two, and all three dual monodromies preserve determinant-one oriented four-volume.
The lower-dimensional current and flux faces may shear even while the top transported volume is
conserved.

[proved-derived; formal-checked] For a finite return `M^m=I`, the file constructs the cyclic storage

```text
E_M(v) = sum_(j=0)^(m-1) sum_i ((M^j v)_i)².
```

It proves exact invariance `E_M(Mv)=E_M(v)` and strict positivity for `v≠0`, then instantiates the
result for the order-three and order-four monodromies.

[proved-derived; formal-checked] A separate generic theorem proves that if `N²=0` and the shear
`x↦x+Nx` preserves a bilinear form `B`, then every defect direction is null:
`B(Nx,Nx)=0`. The explicit dual cusp has a nonzero defect direction. Consequently no definite
fixed bilinear storage form can be invariant under that cusp shear.

## 2. What the rendered convergence is asking for

[established-bounded; implemented-exact] The `complex-s6-torus-transport` source carries 3,328
sampled torus germs and 16,384 declared source carriers. It applies exact rational receiver
covectors and exact depth before perspective. Raster coordinates create no source incidence, and
the current receipt creates no projection cells.

[established-bounded; implemented-exact] The family, finite-return, cusp, and exact receiver-turn
images are therefore genuine receiver faces of transported source carriers. Their visible
convergence is evidence for asking which source-level interaction law survives a receiver rebase.
The current artifact does not yet install mutual capacitance, induction, optical amplitude
interference, or a dynamical metric.

[definition] Every apparent convergence is to be lifted and classified as exactly one typed
population before it is used:

1. shared source incidence/contact;
2. a receiver caustic or equal projected face with retained depth and reconstruction fibre; or
3. a declared constitutive coupling between distinct carriers which changes later current.

[definition] The third population does not require galvanic contact. A Green response, mutual
capacitance, mutual inductance, optical cross term, or metric coupling may join depth-separated
carriers. The coupling must be a source law with an off-diagonal response term and a returned later
consequence; it cannot be minted by the raster crossing.

## 3. One constitutive closure

[definition] The common Holonic Interaction carrier is a covariant storage--flux complex:

```text
rho = C phi,
J = -W d_A phi,
d/dt rho + partial_A J = s,
L_A = d_A^dagger W d_A + C.
```

Here `phi` is a situated section, `d_A` is the connection-valued local difference, `C` is storage or
capacity, `W` is the conductive response, `J` is oriented current, `partial_A` is the declared
metric adjoint/boundary, and `s` is an exterior source. The receiver is a projection of the complete
complex and retains its reconstruction fibre. Advective current is carried separately as a typed
bilinear transport.

[proved-derived; canon] The repository already owns the exact additive balance
`q_(k+1)-q_k+Bj_k=r_k`, its telescoped boundary return, voltage closure, Stokes pairing, exact Schur
boundary condensation, addressed connection words, holonomy/route defect, receiver factorization,
and complete reconstruction fibres. I9 composes those owners and adds only the missing exterior and
constitutive consequences.

[definition] The exterior tower types the geometric carriers:

```text
Λ¹  effort, gradient and current directions
Λ²  oriented planes, curl, flux and mutual interaction
Λ³  oriented boundary-flux faces
Λ⁴  transported volume.
```

The connection acts through every `Λᵏ`; curvature is the route defect `d_A²`, or
`F_A=dA+A∧A` in a nonabelian chart. Metric/Hodge receivers convert these exterior carriers into
the vector and scalar faces used by a particular domain.

## 4. The domains are coupled instances

[definition] In a circuit, `C` is charge storage and `W` is conductance/admittance. The local
balance is Kirchhoff continuity. Eliminating an interior produces the Schur/Kron
Dirichlet-to-Neumann capacitance seen at the boundary, with the hidden-current reconstruction fibre
retained.

[definition] In heat transport, `C` is heat capacity and `W` is conductivity. Positive response
gives diffusion and energy decay. Entropy production enters when the returned deformation/current
is passed through a declared irreversible thermal relaxation law and receiver.

[definition] In optics and electromagnetism, `A` transports phase and polarization, the exterior
two-form carries field flux, and `W` is impedance or constitutive response. Poynting balance is the
same local storage/boundary-current law with electromagnetic energy and flux; `J·E` returns the work
deposited into thermal, optical, mechanical, or morphological channels.

[definition] In fluid dynamics, incompressibility is the codifferential constraint, vorticity is
the exterior derivative of velocity, viscosity is the positive Hodge/Stokes response, pressure is
the global constraint receiver, and advection is the additional nonlinear current. Kelvin return,
curl, divergence, Hodge projection, diffusion, and vortex stretching are faces of this typed
complex.

[definition] In Yang--Mills, the connection is nonabelian, `F_A=dA+A∧A` is curvature, Wilson loops
are holonomy receivers, and the missing Millennium return is a scale-uniform positive/coercive form
rather than another local route identity.

[definition] In gravity, the Lorentz metric and its compatible connection determine adjoints,
Hodge stars, null cones, Green responses, capacitance, and volume. Fluid, electromagnetic,
thermal, and dissipative currents contribute to the complete stress-energy tensor, which changes
the metric through the Einstein equation. Contracted Bianchi returns the conservation constraint.
Thus the physical closure is the feedback loop

```text
metric/connection
 -> transport, cones, Hodge/Green/capacitance
 -> currents, flux, heat, radiation and complete stress-energy
 -> Einstein/Bianchi return
 -> changed metric/connection.
```

[interpretation] This is the exact mathematical form of the requested unification program. The
same incidence, exterior transport, storage, flux, boundary, holonomy, and receiver laws are shared;
the domains differ by their typed constitutive maps and sources. The program becomes theorem-grade
one specialization and one commuting diagram at a time.

## 5. Transported capacitance is the next interaction theorem

[definition] For a seam `x --U--> y`, define the complete transported difference and energy

```text
delta_U(x,y) = y-Ux,
E_(U,C)(x,y) = <C delta_U(x,y), delta_U(x,y)>.
```

Its block response is

```text
[ U* C U   -U* C ]
[ -C U        C  ].
```

[open] Lean must prove its positivity, reciprocal symmetry under the declared form, kernel equal to
the transported graph, serial composition, closed-word/fixed-holonomy return, and positive
Schur/Kron boundary condensation. The theorem must retain endpoint storage: the mutual cross term
alone is not a passive capacitor.

[open] The next geometric owner is the complete cubical torus complex. It must construct oriented
edges, squares, cubes, and four-cells; prove `boundary²=0`, Stokes/Gauss, monodromy naturality, and
the exact/coexact/harmonic Hodge split; and bind plural receiver crossings to transported bivectors
without rewriting receiver incidence into source contact.

## 6. Immediate Navier--Stokes receiver

[proved-derived; formal-checked] The existing periodic fluid line already constructs the Fourier
Hodge multiplier, exact finite heat evolution, triple zero-padded Abel/Fubini identities, restart
supply from a uniform coordinate bound, and terminal-half continuation from critical-vorticity
integrability plus that supply.

[proved-derived; formal-checked] `NavierStokesDyadicHodgeLowScale.lean` now proves the generic crude
physical estimate

```text
dyadicHodgeJacobianKernelL1(s) ≤ 27 * (2^(s+3)-1)^3.
```

It proves the aperture counts `7,15,31` at scales zero, one and two and closes all three with the
single explicit constant `804357`.

[open] The remaining large-scale kernel theorem is:

1. reusable reciprocal finite differences through total order six;
2. all twenty-seven Leibniz faces and the inverse-cube three-axis full mixed mass;
3. the eight subset masses: empty, three singles, three pairs, and the full triple;
4. a one-circle near/far Haar estimate and its three-coordinate tensorization; and
5. an explicit `UniformDyadicHodgeJacobianKernelBound` witness.

[proved-derived; formal-checked] The exact aperture count is `2^(s+3)-1`, so the first three counts
are `7,15,31`. The existing large-scale two-axis Hodge mass is inverse-linear. The full scalar
`222` stencil has the expected inverse-cube scale, but its Hodge completion is not yet a checked
theorem.

[open] Triple Abel cannot simply be divided everywhere by
`∏_i|1-exp(2πix_i)|²`; that reciprocal is singular on the coordinate faces. Partition by which
coordinates are within order `1/2^s` of one. Use direct subset mass on near coordinates and Abel
differences on far coordinates. The mode-count factor and near-arc measure cancel, while the
inverse-scale variation and truncated reciprocal integral cancel on each far axis. This is why all
eight subset receivers are structurally necessary.

[open] After the uniform physical `L¹` kernel witness is composed with the checked restart and
continuation theorems, the remaining official Navier--Stokes obstruction is finiteness of the
critical-vorticity time integral for arbitrary smooth periodic data.

## 7. Further Millennium squeeze

[definition] Hodge, Yang--Mills, RH, and BSD now receive one shared target: construct a positive
global constitutive form whose local pieces glue through the complete receiver family and whose
null fibre contains no forbidden nonzero difference. For Hodge this is primitive positivity after
chart gluing; for Yang--Mills it is scale-uniform curvature coercivity; for RH it is the complete
Weil form and its archimedean endpoint storage; for BSD it is the global height assembled from all
local valuation currents with every bad-place remainder retained.

[open] The cusp theorem supplies a useful obstruction across these lines. Oriented volume and
incidence may remain conserved while every fixed positive lower-degree storage fails. Any claimed
global energy, entropy, coercivity, or zero-placement theorem must therefore declare whether its
metric is transported, relaxed, or genuinely invariant; conservation of a top exterior face cannot
silently supply positivity below it.

## 8. Validation

[formal-checked] From `soma/formal/elementary-holonics`:

```text
lake env lean ElementaryHolonics/Millennium/HolonicInteractionExterior.lean
lake env lean ElementaryHolonics/Millennium/NavierStokesDyadicHodgeLowScale.lean
```

returned successfully. The audited theorems report no dependency on `sorryAx`.
