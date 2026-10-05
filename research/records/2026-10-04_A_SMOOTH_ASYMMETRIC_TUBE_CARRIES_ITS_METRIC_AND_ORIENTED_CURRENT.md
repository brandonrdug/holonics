# A smooth asymmetric tube, its metric and its transported ports

**Date:** 2026-10-04. **Refs:** #62, #73, #63. **Grade:** derived geometry and power algebra; the section derivative, its coordinate columns, oriented area
and current pairing are formal-checked in complete isolated modules and the complete
patched actual FrameTransport owner. The source proposal is applied only in a pinned
snapshot, with no canonical root edit or Rust execution. Spatial
stations below are geometric coordinates; the time parameter `τ`, when used,
belongs to a declared receiving clock.

## 1. Sources, objects and the exact missing join

This is a spatial chart of a Holon's motion and receiving boundary: the tube's
longitudinal stations, helical frame, cross-sectional faces, their placement and
ports. Cell holonomy and the tower's restriction/gluing remain declared operands.
It does not identify every abstract clocked tube with a Euclidean solid.

Recovered sources and actual owners:

- [The helical guide](https://github.com/brandonrdug/holonics/blob/3a242c99/docs/HELICAL_GEOMETRY.md#a-helix-and-its-independent-collapses)
  and `Geometry/ScrewGeometry` own a screw's velocity, its helix and degenerations,
  local pair jets and the prestress term. The guide's helix curvature/torsion are
  used only on their nondegenerate domain.
- [FrameTransport](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Geometry/FrameTransport.lean)
  owns real normalized proper frames, labelled oriented volume and receiver-frame
  transport. It supplies the right existing owner for the small pointwise tube
  area-vector lemma in §9; no second frame system is proposed.
- [The September 24 egg record](https://github.com/brandonrdug/holonics/blob/3a242c99/research/records/2026-09-24_THE_EGG_IS_A_TORUS_WHOSE_SHAPE_IS_A_BOOST_AND_ITS_NECK_IS_THE_NULL_CONE.md)
  gives `(A²+W²+2Ws)y²=B²(A²−s²)`. Its
  [September 26 correction](https://github.com/brandonrdug/holonics/blob/3a242c99/research/records/2026-09-26_THE_SHADOW_IS_THE_RECEIVERS_KERNEL_AND_THE_EGG_IS_TWO_RINGS_IN_RELATIVE_MOTION.md#4-the-egg-is-the-face-of-two-rings-in-relative-motion)
  distinguishes the real oval, exterior branch and complex elliptic torus, and
  declines a physical velocity/Doppler identification without a source map.
- [HolonicTorusKnots](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Geometry/HolonicTorusKnots.lean)
  owns actual intrinsic torus loops and coprime-slope embeddings; it explicitly
  does not assert an ambient Euclidean torus isotopy.
- [ChangingReceiver](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Transport/ChangingReceiver.lean)
  derives the moving **one-dimensional affine** cell's actual continuity balance,
  including `j−ρ Xdot`. The nonlinear three-dimensional cofactor/continuity join
  below is its remaining extension, not something its present theorem proves.
- [Holon/Port](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Holon/Port.lean),
  [Holon/Dirac](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Holon/Dirac.lean)
  and [HelicalPairInteraction](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Transport/HelicalPairInteraction.lean)
  own effort/flow power, cancelling joined interface power, and the pair-rate
  pullback `Cᵀ Jᵀ D J C`. They do not currently construct this spatial tube decoder.
- [Fluid/Body](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Physics/Fluid/Body.lean)
  and native `physics::fluid::body::gauss` distinguish a bounding membrane from
  lateral tube walls that leave emission through end ports. Shape closure alone
  is not an impermeable boundary or relative completeness theorem.

Atlas, current owners and the matching pre-reset Lean operations were searched.
No existing tubular-coordinate/Piola owner was recovered. The historical neck
records price declared sections; their retired apparatus is not restored here.
The repeated failures avoided are treating a picture as a source map, omitting
geometric/prestress terms, promoting a local fixture to a consumer and counting
an energy identity as stability or future sufficiency.

## 2. One explicit smooth tube-around-curve map

Let `c:I→ℝ³` be a `C³` embedded unit-speed curve. Write `t=c_s`. Choose a `C²`
positively oriented orthonormal frame `(t,d1,d2)` satisfying

```text
t_s  = κ1 d1 + κ2 d2,
d1_s = −κ1 t + Ω d2,
d2_s = −κ2 t − Ω d1,       d1 × d2 = t.
```

These are the skew frame derivative relations, with declared normal-plane twist
`Ω`. On an interval a parallel normal frame can be chosen with `Ω=0`; rotating
its two normals by a declared angle `α(s)` gives `Ω=α_s`, with the curvature
components rotated by the same frame. This construction does not divide by
curvature, so an inflection or straight segment does not destroy its definition.

On the reference disk `D={u²+v²<1}`, choose `C²` section parameters
`a(s)>0`, `b(s)>0`, and `2|ε(s)|<1`. Define

```text
h=1+εu,
q1=a u h,              q2=b v h,
X(s,u,v)=c(s)+q1 d1(s)+q2 d2(s).
```

This is polynomial in the disk coordinates, hence smooth through its axis.
The asymmetry is actual: for `ε≠0`, the section is not invariant under
`(q1,q2)↦(−q1,−q2)` about the declared spine. On its boundary, putting
`u=cosθ`, `v=sinθ` gives

```text
q_boundary(θ)=(a(1+εcosθ)cosθ, b(1+εcosθ)sinθ).
```

The factor is positive. The stronger bound `2|ε|<1` comes from invertibility of
the full interior disk map, not a chosen tolerance: its two Jacobian factors
are `1+εu` and `1+2εu`. The first component `a(u+εu²)` is strictly increasing
in `u∈[−1,1]`; after recovering `u`, the second recovers
`v=q2/[b(1+εu)]`. Thus each section map is one-to-one on the disk.

No float enters the construction. Angles, positive roots and clocks are their
constraint identities; a future native realization still owes their exact
decoder/constraint/enclosure implementation.

## 3. Actual derivatives, induced metric and volume

Put

```text
ν=1−κ1 q1−κ2 q2,
p1=q1_s−Ωq2,          p2=q2_s+Ωq1,
A0=a(1+2εu),          B0=bεv,          C0=bh.
```

The profile derivatives are complete:
`q1_s=a_s u h+a ε_s u²`, `q2_s=b_s v h+b ε_s uv`.
Differentiating the actual map gives

```text
X_s=νt+p1d1+p2d2,       X_u=A0d1+B0d2,       X_v=C0d2.
F=dX=[t d1 d2] · [[ν,0,0],[p1,A0,0],[p2,B0,C0]].
```

The ambient metric is the declared Euclidean one, so the induced coordinate
metric is `g=FᵀF`, explicitly

```text
g_ss=ν²+p1²+p2²,     g_su=p1A0+p2B0,     g_sv=p2C0,
g_uu=A0²+B0²,        g_uv=B0C0,          g_vv=C0².
```

Its oriented volume Jacobian and metric determinant are

```text
J=det F=ν Δ,       Δ=A0 C0=ab(1+εu)(1+2εu),
det g=J².
```

The proper frame has determinant one; the displayed derivative matrix is
triangular. This proves both factorizations. The `p` entries, including taper,
changing asymmetry and twist, remain in the metric even though they cancel
from this volume determinant. Keeping only `J` would lose kinetic and port
readings involving those off-diagonal terms.

The full three-dimensional `g` here is the pullback of the Euclidean metric;
it is locally flat wherever `X` is a regular chart. A bent spine does not by
itself create intrinsic ambient curvature. The boundary's restricted metric
can be curved. For `a=b` constant and `ε=0` on the circular toroid of §7, in coordinates
`φ=s/R0`, `θ`, it is `(R0−a cosθ)² dφ²+a²dθ²`, with Gaussian curvature
`−cosθ/[a(R0−a cosθ)]`: the inner and outer faces have opposite signs.
This follows from the warped surface metric's `K=−f_θθ/(a²f)`,
`f=R0−a cosθ`. A different ambient or material measuring metric must be
declared separately; its pullback would be `Fᵀ G(X) F`.

On `ν>0` the hypotheses make `J>0`, and `g` is positive definite because
`zᵀgz=|Fz|²` with `F` invertible. A convenient sufficient local bound is
`|(κ1,κ2)| max(a,b)(1+|ε|)<1`. It follows by Cauchy–Schwarz and
`|q|≤max(a,b)(1+|ε|)`. This is a derived sufficient inequality, not a necessary
radius or a global self-intersection certificate. Global injectivity of `X`
must also be supplied: distant stations can overlap despite every local `J>0`.

In polar coordinates `u=r cosθ`, `v=r sinθ`,

```text
J_polar=r ν ab(1+εr cosθ)(1+2εr cosθ).
```

Its `r=0` zero is only the polar chart's axis; the Cartesian disk chart above
remains regular there. By contrast `ν=0`, `a=0`, `b=0`, `h=0` or
`1+2εu=0` destroys this volume chart's inverse. A boundary surface must be
checked with its own two-column rank; loss of volume-chart rank does not by
itself prove that every boundary surface is singular.

The exact section area is `πab(1+ε²/2)`: integrate
`Δ=ab(1+3εu+2ε²u²)` on the unit disk, using oddness and
`∫_D u²=π/4`. Its first `q1` moment is
`πa²b(ε+ε³/4)`, while its `q2` moment vanishes. The centroid is therefore
`(aε(1+ε²/4)/(1+ε²/2),0)`. This makes the declared asymmetry measurable,
without identifying a shape parameter with a velocity or a potential law.

## 4. Transported charge/content flux and continuity

Allow `X` to depend `C²` on a receiving clock `τ`, and set `w=X_τ` at fixed
reference coordinates. Assume `J>0` and an actual physical current/density law

```text
∂τρ+div_x j=σ.
```

Here `j` is content per physical area per unit of that clock; it is not a
coordinate velocity. At each regular chart point define

```text
ρ_hat=J ρ∘X,
j_hat=J F⁻¹(j∘X−(ρ∘X)w),       σ_hat=J σ∘X.
```

Then the exact nonlinear moving-chart law is
`∂τρ_hat+∂_i j_hat^i=σ_hat`.
For a fixed reference region `U`, with enough integrability and boundary
regularity to differentiate/integrate this equation,

```text
d/dτ ∫_U ρ_hat = ∫_U σ_hat − ∫_∂U j_hat·n_reference.
```

Derivation: the cofactor columns are the cross products of the other two
`X_i`. Their divergence vanishes by equality of mixed partials. Hence
`div_reference(JF⁻¹ z∘X)=J(div_x z)∘X`.
Also `∂τJ=J tr(F⁻¹∂τF)=div_reference(JF⁻¹w)`.
Applying the product/chain rules to `Jρ∘X`, then subtracting the divergence
of `JF⁻¹ρw`, cancels the density's chart-advection and volume-rate terms.
The remaining terms are `J(∂τρ+div_x j)∘X`. These identities require the
actual derivative matrix of a `C²` map; an arbitrary matrix field need not
satisfy the cofactor-divergence identity.

For a section `s=constant`, its actual oriented area vector is

```text
X_u × X_v=Δt,
j_hat^s=Δ (j∘X−ρ∘X w)·t.
```

Thus flux is transported through the actual curved/asymmetric section, not
through an assumed Euclidean unit disk. Side-wall flux similarly uses
`X_v×X_s` or `X_s×X_u` and the complete relative current. In a steady,
source-free tube, constant integrated longitudinal flux additionally needs
zero side leakage. A tapered tube's velocity cannot simply be declared parallel
to its spine while asserting no penetration; its transverse return is owed.
For `ρ=constant`, `j=0`, `σ=0`, changing reference coordinates alone gives
`j_hat=−ρJF⁻¹w` and `∂τ(Jρ)+div j_hat=0`, not spontaneous content production.

## 5. Actual power pairing and the moving boundary

At a regular point, for a physical effort covector `e` and flow velocity `v`,

```text
e_hat=Fᵀe,       v_hat=F⁻¹v,       e_hat·v_hat=e·v.
```

For physical traction `T` on a boundary patch with reference area factor `A`,
use `e_hat=A FᵀT` and `v_hat=F⁻¹v`; then the reference integrand is exactly
`A T·v`. On a moving material/receiving boundary,

```text
T·v=T·(v−w)+T·w.
```

The last term is work at the moving support. It cannot be erased by quoting
chart covariance or by using only relative flow. A scalar port effort can also
pair with a transported content flux if its units/material law make that pairing
power. No universal identity `energy current = effort × content current` is
assumed. An actual energy balance `∂τe_energy+div Q=S−d` instead transports
its full flux as `J F⁻¹(Q∘X−e_energy∘X w)`.

For a declared mass density and coordinate velocity `ξ`, the actual kinetic
reading is `½∫ρ_mass J |w+Fξ|²`. Static geometry gives the pulled-back form
`ρ_mass Jg`; moving geometry keeps the cross and self-energy of `w`.
Geometry alone supplies neither stiffness, dissipation nor pump power.

When neighboring finite regions share this same physical interface map, their
area/normal pullbacks carry opposite outward flows and the same effort. This
is the concrete geometry needed to instantiate `Dirac.interconnect_power` and
finite-cell Stokes/Gauss. Independent face fluxes must be computed through the
same interface, rather than making a residual close by definition. Native HNN
contacts still owe their actual map from ring/contact rates to these face rates.

## 6. Egg closure from the actual repository oval

For a straight spine `c(s)=(s,0,0)`, fixed normals, `Ω=ε=0`, choose

```text
a(s)=b(s)=R(s),
R(s)²=B²(A²−s²)/(A²+W²+2Ws),
−A<s<A,       A>B>0,       |W|<A.
```

The denominator is at least `(A−|W|)²>0`. Its lateral boundary is the
surface of revolution of the repository's real Hügelschäffer oval:

```text
F_egg(s,y,z)=(A²+W²+2Ws)(y²+z²)−B²(A²−s²)=0.
```

At `s=±A`, all section points collapse to one cap point. The tube parameter
chart fails there because `R→0` and its axial derivative need not stay finite.
The physical boundary is nevertheless smooth: at a cap
`∂sF_egg=±2B²A≠0`; away from the caps its transverse gradient is nonzero.
A Cartesian graph chart covers each cap. No extension of the inverse tube
Jacobian through a collapsed section is claimed.

The topology is also constructive: on the unit ball
`ξ²+η²+ζ²≤1`, the map
`(ξ,η,ζ)↦(Aζ, f(ζ)ξ, f(ζ)η)`,
`f(ζ)=AB/√(A²+W²+2WAζ)`, is a smooth diffeomorphism onto the egg solid.
Its Jacobian is `A f²>0`, and its inverse recovers `ζ=s/A` and divides the
transverse coordinates by this same positive `f`. Restriction gives the
boundary sphere diffeomorphism. Thus the cap singularity is avoided by an
explicit full Cartesian chart, without identifying a ball with a solid torus.

This bounded solid is a capped globe with sphere boundary. The oval is a real
circle, while the smooth projective **complex curve** for `0<|W|<A` has genus
one. Neither is this three-dimensional boundary's topology. At `W=0` the
physical surface is an ordinary smooth ellipsoid even though the project's
homogenized cubic family has its extra component at infinity.

At `W=A`, the denominator vanishes at `s=−A` and the surface equation factors:

```text
F_egg=(s+A)[2A(y²+z²)−B²(A−s)].
```

The components intersect on `s=−A`, `y²+z²=B²`, where the full equation's
gradient vanishes. The inner limit `R(s)→B` is not a shrinking cap. This is a
genuine degeneration of this chosen family, not a removable tube coordinate
singularity or an established physical null-cone law. The reflected statement
holds at `W=−A`. A closed geometric surface is not an impermeable wall; sources,
admitted boundary flux, material and completeness receivers remain specified.

## 7. Toroidal periodicity and an explicit Euclidean toroid

A closed tube requires a closed embedded spine of length `L`, plus smooth seam
conditions for every derivative used by the law. One sufficient set is periodic
`c,t,d1,d2,a,b,ε` with matching jets. Then `X(s+L,u,v)=X(s,u,v)`.
If an unrotated normal frame returns with normal-plane holonomy angle `χ`, an
additional frame rotation must obey `α(L)−α(0)+χ∈2πℤ` for this periodic frame.
More generally an actual seam map `φ:D→D` must satisfy
`X(L,z)=X(0,φ(z))`, matching jets and pulling back material, flows, efforts and
receivers through the same transition. A mismatch is a gluing defect, not a
periodic circuit. These seam equations do not erase lifted winding.

For an explicit example use

```text
c(s)=(R0 cos(s/R0), R0 sin(s/R0),0),    L=2πR0,
t=(−sin(s/R0),cos(s/R0),0),
d1=(−cos(s/R0),−sin(s/R0),0),          d2=(0,0,1).
```

Here `κ1=1/R0`, `κ2=Ω=0`. Constant `a,b,ε` give
`X=((R0−q1)cos(s/R0),(R0−q1)sin(s/R0),q2)`.
The derived sufficient bound `a(1+|ε|)<R0` keeps `R0−q1>0`.
The ambient azimuth then recovers `s mod L`, and the injective section map
recovers `(u,v)`, proving a global embedding in this example. Its body is a
solid torus, and its lateral boundary is a two-torus. No cap is added.
Allowing periodic taper, asymmetry or frame rotation keeps this conclusion
when global injectivity and the seam equations persist; a uniformly thin
normal displacement is sufficient here, for example
`max(a,b)(1+|ε|)<R0` for the rotated circle frames.

At the symmetric circular inner contact `a=R0`, `ε=0`, `r=1`, `θ=0`,
`ν=0` and the inner boundary circle collapses to the symmetry-axis point.
Past it the normal chart can overlap. Identifying overlapping sheets, closing
the hole or prescribing exchange there needs new gluing/boundary data; none
is an invertible rechart. A twisted material pattern may fail to return even
when the geometric circular section returns.

An intrinsic slope `(p,q)` with coprime integers is an embedded torus loop in
`HolonicTorusKnots`. Composing it with a certified boundary embedding above
produces an actual spatial loop. Its ambient isotopy classification is an
additional theorem. Arbitrary real phase rates need not close.

## 8. Helical specialization and the exact rechart distinction

For `R0>0`, pitch `H`, and the exact positive constraint
`V²=R0²+H²`, a unit-speed helix is

```text
c(s)=(R0 cos(s/V),R0 sin(s/V),H s/V).
```

Its nondegenerate curvature and torsion are `R0/V²` and `H/V²`, agreeing with
the existing helical guide. At one angular turn, `s→s+2πV`, the axial carry
is `2πH`. For `H≠0` it is an open Euclidean helix, not a closed toroidal
spine. Quotienting ambient height by this carry is a different global model
with periodic boundary conditions. At a straight degeneration use the normal
frame/screw law, not a divided Frenet torsion.

The exact criterion for a coordinate rechart is a diffeomorphism `Φ` of the
reference region, with `X_tilde=X∘Φ` and the same pulled-back material,
receiver, clock and boundary data. Its metric is
`g_tilde=(dΦ)ᵀ(g∘Φ)dΦ`, its density uses the determinant, and its covectors
and flows use dual/contravariant transport. It changes none of the physical
pairings above. Changing only their coordinate labels is not enough.

| Change | Required interpretation |
|---|---|
| Relabel stations, transverse coordinates or the angular seam, transporting all operands | Rechart, when the displayed diffeomorphism and gluing squares hold. |
| Rotate a circular isotropic section's normal frame and counter-rotate its coordinates/material/receivers | Rechart. Rotating a labelled pump or anisotropic material instead is a physical relative phase/material change. |
| Change `a,b,ε` or twist an anisotropic/asymmetric section while keeping its reference boundary/material labels fixed | Usually a new embedded shape and induced metric. Prove `X_tilde=X∘Φ` before treating a special case as gauge. |
| Change material density, stiffness, contact dissipation or pump declaration on the same shape | New constitution and its deposition/pump work; not established by the metric. |
| Identify endpoint disks to make a periodic tube, impose a different seam, pinch or reconnect a hole | New gluing, topology or boundary conditions; an invertible chart cannot supply it. |
| Move a boundary in the ambient medium | Changed domain/receiver, with relative content flux and actual moving-support work. A moving mesh within one fixed physical boundary is instead a rechart. |

## 9. The smallest formal target and consuming joins

The smallest checked algebraic target belongs beside the proper real frame in
`Geometry/FrameTransport`, with no new tube library. Given that frame and the
supplied derivative columns from §3, the isolated module proves

```text
X_u × X_v=ab(1+εu)(1+2εu)t.
```

Its immediate consumers are the oriented Jacobian
`X_s·(X_u×X_v)=νab(1+εu)(1+2εu)` and actual section flux
`j·(X_u×X_v)=ab(1+εu)(1+2εu)(j·t)`.
This is the missing geometric face map, rather than another arbitrary matrix
congruence. The transverse columns are now joined to actual `HasFDerivAt` in §11; the
longitudinal column and full moving-volume join retain the displayed hypotheses.

The next theorem, separately, is the actual `C²` cofactor/geometric-conservation
identity used in §4, in `ChangingReceiver`, extending its affine one-dimensional
law. Integral transport then needs its domain, trace, integrability and derivative
domination hypotheses. The existing finite-cell continuity and port laws consume
independently computed oriented face fluxes and mapped efforts. Native HNN still
owes the tube/contact rate decoder, its producing adjoint and the contemporary
material/phase return; no coordinate derivation closes those automatically.

Acceptance for this conceptual loop is the explicit smooth map, full metric,
Jacobian, section flux, moving-support power and stated regular/gluing domains.
These have been derived above. The two pointwise formal checks are accepted
as described below; the longitudinal/C2 continuity joins and native execution
remain unclaimed. The separate finite-work lemmas also pass isolated checks.
No phase-port, private source owner or frame construction is duplicated.

## 10. Accepted isolated area and current algebra

The unchanged actual `lean/Holonics/Geometry/FrameTransport.lean` compiled
directly from its repository path into an isolated object directory. Its source
is pinned by the [owner dependency receipt](receipts/2026-10-04_smooth-tube/frame-owner-accepted-01.json).
The [submitted tube module](receipts/2026-10-04_smooth-tube/TubeSectionAreaVector-accepted-02.lean)
imports that owner. It checks `tube_section_area_vector` and `tube_section_flux`
with no warning, error or `sorryAx`; both audits list only `propext`,
`Classical.choice`, `Quot.sound`. The [accepted receipt](receipts/2026-10-04_smooth-tube/tube-area-accepted-02.json)
and [compiler log](receipts/2026-10-04_smooth-tube/compiler-02.log) preserve the
complete result. Wall time was 1348541976 ns against the unchanged
17000000000 ns child deadline, with child peak RSS 2870824 KiB. Complete import
parts and source stayed unchanged after execution; the child was reaped and
exact common lease released. Canonical owner integration and its complete
owner check remain pending.

At this algebra-only stage the columns were theorem operands. Section 11
identifies the actual transverse derivative. Full Piola/geometric conservation,
global embedding/gluing and native physical decoder remain the consumer joins in §9.

## 11. The actual section derivative and its consuming face

At a fixed spine position, c, f, a, b and ε are constant. Define
`X(z)=c+a z₁(1+εz₁)d1+b z₂(1+εz₁)d2`. The accepted module
[`TubeSectionDerivative-accepted-03.lean`](receipts/2026-10-04_smooth-tube/TubeSectionDerivative-accepted-03.lean)
uses `HasFDerivAt` product/smul/add rules to construct a continuous linear
derivative on `(δu,δv)`. Its coordinate columns are exactly
`a(1+2εu)d1+bεv d2` and `b(1+εu)d2`.

The five declarations are `tube_section_hasFDerivAt`,
`tube_section_fderiv_first`, `tube_section_fderiv_second`,
`tube_section_actual_area`, `tube_section_actual_flux`. The last two consume
these actual columns through the accepted area/current laws, not an assumed
derivative hypothesis. This polynomial derivative is global on ℝ×ℝ;
positivity/regularity hypotheses are needed only by the subsequent geometric
interpretation, inverse map and full three-dimensional law.

The [complete accepted receipt](receipts/2026-10-04_smooth-tube/tube-derivative-accepted-03.json)
and [compiler log](receipts/2026-10-04_smooth-tube/derivative-compiler-03.log)
show exit zero, no warnings/errors/`sorryAx`, and each axiom list exactly
`propext`, `Classical.choice`, `Quot.sound`. The actual unchanged frame owner
is imported through the accepted area module. Source SHA256 is
`0af342373beaff8bd637c23803180897b14a758e408beb4f76968b0967bdb66d`.
Wall time 1,963,430,300 ns / fixed 17,000,000,000 ns; peak child RSS
2,935,304 KiB. The existing 4-GiB charged-page cap and memory floors remained;
charged pages and child RSS are separate readings. All 3,946 module import
parts remained unchanged in the complete postcheck. Child reaping, empty
owned group and exact shared-lease release were confirmed. Earlier failed
preparation/elaboration receipts remain historical in local scratch, not accepted proofs.

The full longitudinal Fréchet derivative, Piola/geometric conservation, integral
transport, native current/material decoder and independently computed work remain
open. Supplying any vector j to `tube_section_actual_flux` proves its pairing;
it does not make j a continuity current. Canonical root integration
is proposed, with the atlas rows changed in the same candidate.

## 12. Complete patched owner and its actual importing consumer

The seven declarations now reside in the existing FrameTransport owner in the
isolated `3a242c99` snapshot. Its complete direct compilation produced fresh
objects with no warning or error. The
[owner receipt](receipts/2026-10-04_canonical-geometric-integration/canonical-frame-06.json)
and [log](receipts/2026-10-04_canonical-geometric-integration/canonical-frame-06.log)
record 6,297,434,153 ns wall against the unchanged 17,000,000,000 ns child deadline,
2,970,604 KiB child RSS and 3,594,182,656 bytes charged group peak.
The [combined importing consumer](receipts/2026-10-04_canonical-geometric-integration/CanonicalGeometricAudit.lean)
then resolves these seven and Motion's two work declarations from the fresh
owner objects; its [receipt](receipts/2026-10-04_canonical-geometric-integration/canonical-audit-10.json)
and [log](receipts/2026-10-04_canonical-geometric-integration/canonical-audit-10.log)
audit exactly the standard three axioms for all nine, with no warning, error or
`sorryAx`. The complete import-part postchecks and quiescent shared-lease release
are recorded separately; the Frame metadata postcheck had a CPU limit but no
outer wall timeout, so its receipt does not claim that outer deadline.

This closes the complete actual-owner/import check at the pinned source proposal.
It does not close the moving-volume law, native spatial-tube decoder or actual
receiver/material/work consumer. Those hypotheses and equations remain §§4,9,11.
