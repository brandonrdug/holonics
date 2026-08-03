# THE ANALYTIC BODY CARRIES THE CURRENT; THE INTERFACE RETAINS THE OPEN FIELD

**Date:** 2026-07-30  
**Status:** EXACT ANALYTIC WAVE CARRIER BUILT · MODE-LOCAL MATERIAL INCIDENCE BUILT ·
EXACT INTERFACE FIBERS BUILT · EXACT CONSERVATIVE CIRCULATION BUILT · REACTIVE
EVANESCENT STORAGE REMAINS OPEN  
**Production owners composed:** `CausalFieldAtlasLaw`, `ExactTorus`, `ExactQuadric3`,
`ExactDimensionalWaveLaw`, `ExactReceiverPhasePopulation`, `ExactReceiverPrimaryDoctrine`, and
the new `ExactRatMatrix`, `ExactAnalyticFieldWaveLaw`, and `ExactAnalyticAdvectionLaw`  
**Instrument:** `crates/holonic-engine/examples/analytic_field_transport.rs`  
**Returned testimony:** `output/analytic-field-transport/`

## The quest preserved

The construction is not a rendered mathematical graph. It asks what exact current can lawfully
move on the caused analytical bodies already owned by the field atlas, what changes at an
interface, what recurs on a closed body, and what one receiving membrane obtains after co-present
phase currents meet.

The source bodies are therefore not terminal lines:

- a source-owned rational quartic torus remains a continuous implicit body with exact gradient and
  Hessian;
- an observation-conditioned quadric remains its complete homogeneous quadratic;
- a torus longitude, torus meridian, or quadric conic is an analytical open section of that body;
- an overlap is geometrical testimony only until a physical interaction doctrine declares that
  current may meet there; and
- a display or TSV receives the resulting current but never schedules or defines it.

The new consequence is a changing exact current on those analytical sections, with exact
reflection, transmitted traveling incidence, open grazing/evanescent fibers, closed-cycle phase
holonomy, conservative advection, and receiver-local resonance contacts.

## One conservation grammar does not erase the constitutive laws

Wave transport, optical interface behavior, conservative advection, and diffusion can share the
incidence statement

\[
\partial_t q + \partial J = S,
\]

but they are not one interchangeable law.

- The guided scalar wave carries a complex phase current and uses a unitary section transport plus
  passive admittance scattering.
- Geometric optics restricts the incident covector at a material interface and classifies the
  transmitted normal fiber as propagating, grazing, or evanescent.
- Conservative advection transports chart values by a capacity-skew generator and preserves
  totals, quadratic energy, and declared closed-chain circulation.
- `ExactDiffusionLaw` remains a distinct dissipative conductance law. It was not relabeled as
  fluid motion.

This distinction is the operative holonic commonality: the same caused analytical body and
boundary calculus can receive different exact interaction doctrines without flattening their
physics.

## Analytical orbit carriers

### Quadric conic

For a resolved quadric \(F(x)=0\), one declared conic chart is

\[
x(c,s)=o+cu+sv,\qquad c^2+s^2=1.
\]

Admission proves \(F(x(c,s))=0\) identically by checking the center value, the two equal quadratic
restrictions, the vanishing linear terms, and the mixed Hessian term. Its exact tangent is

\[
\dot x(c,s)=-su+cv,
\]

and the engine certifies

\[
\nabla F(x)\cdot\dot x=0.
\]

The instrument conditions the sphere centered at \((0,12,0)\) from six oriented occurrences, then
carries the exact conic with axes \((2,0,0)\) and \((0,0,2)\). At phase \((3/5,4/5)\), for example,
the point and tangent are exact rational sections rather than sampled approximations.

### Torus longitude and meridian

An exact positively oriented frame \((e_1,e_2,a)\), with \(e_1\times e_2=a\), fixes the winding
hand which the torus quartic and two endpoint positions alone do not determine. For major radius
\(R\), minor radius \(r\), longitude phase \((c,s)\), and fixed meridian phase \((c_m,s_m)\), the
longitude is

\[
x(c,s)=o+(R+rc_m)(ce_1+se_2)+rs_ma.
\]

At fixed longitude \((c_\ell,s_\ell)\), the meridian is

\[
x(c,s)=o+(R+rc)(c_\ell e_1+s_\ell e_2)+rsa.
\]

Both are checked against the exact quartic and its gradient. A construction bug found during this
work had incorrectly used both radial basis vectors with the same meridian derivative. The
correct meridian tangent uses the fixed longitude radial vector:

\[
\dot x=-rs(c_\ell e_1+s_\ell e_2)+rca.
\]

No projected ellipse, polyline, or raster cell participates.

## Interior winding is not an endpoint lookup

The earlier dimensional wave owner derived phase transport from endpoint unit-conic coordinates.
That is sufficient only when the endpoint relation determines the path. A torus loop can return to
the same point after nontrivial interior winding.

`ExactWavePhaseTransport` now carries one exact rational unit-conic relation

\[
T(c,s)=
\begin{bmatrix}
c&-s\\
s&c
\end{bmatrix},
\qquad c^2+s^2=1,
\]

with exact inverse, composition, exponentiation, and action on current. A carrier may retain this
mode-locally even when its endpoint coordinates are equal. A grading test sends \((1,0)\) through
equal endpoint coordinates with a declared quarter-turn and receives \((0,1)\); the inverse return
restores \((1,0)\).

This is the computational reflection which the analytical body owes: the section carries what
happened through it. Reconstructing that relation from endpoint addresses would erase the path.

## Material interfaces: reflection, refraction, and lawful obstruction

For incident covector \(k_i\) and nonzero interface normal \(n\), the exact reflected covector is

\[
k_r=k_i-2\frac{k_i\cdot n}{n\cdot n}n.
\]

The retained tangential part is

\[
k_\parallel=k_i-\frac{k_i\cdot n}{n\cdot n}n.
\]

Given the transmitted material dispersion face \(\kappa_2^2\), the normal coefficient satisfies

\[
\lambda^2
=
\frac{\kappa_2^2-\lVert k_\parallel\rVert^2}{n\cdot n}.
\]

The engine does not take an unjustified square root. It returns:

- `Propagating` when \(\lambda^2>0\), retaining the exact square and coorientation hand;
- `Grazing` when \(\lambda^2=0\); or
- `Evanescent` when \(\lambda^2<0\), retaining the exact positive deficit.

For a propagating scalar guide with positive material admittances \(Y_1,Y_2\), the declared
traveling amplitudes are

\[
r=\frac{Y_1-Y_2}{Y_1+Y_2},
\qquad
t=\frac{2Y_1}{Y_1+Y_2},
\]

and

\[
Y_1-Y_1r^2-Y_2t^2=0.
\]

The first instrument run exposed a false extension: those real two-port coefficients were being
applied to grazing and evanescent fibers as though each were ordinary transmitted traveling
power. That was corrected before this record. `DimensionalWaveCarrierDoctrine` now has exact
mode-local incidence. In the current conservative traveling sector:

- the propagating band has a transmitted carrier;
- the grazing band returns `GRAZING_OPEN` and has no transmitted normal-power carrier; and
- the evanescent band returns `EVANESCENT_OPEN` and has no fabricated unitary traveling carrier.

At the shared junction the latter two modes therefore see one conservative incident port and
reflect completely. A later reactive/storage law may retain their boundary fields and return
energy; absence from traveling incidence is not deletion.

The exact interface instrument uses \(k_i=(3,4,0)\) and returns:

| mode | transmitted geometric fiber | traveling amplitude fiber | exact result |
|---|---|---|---|
| 1 | propagating | admitted | \(r=-1/3,\ t=2/3,\) energy residual \(0\) |
| 2 | grazing | open | no fabricated traveling coefficient |
| 3 | evanescent | open | normal-square deficit \(7/9216\) |

All three return \(k_r=(-3,4,0)\).

## Closed geometry does not force closed phase

`ExactAnalyticFieldWaveLaw::cycle_phase_holonomy` accepts only an ordered, boundary-closed arc word.
It composes the complete mode-local section transports and returns the exact loop relation.

The quarter-turn transport closes after four sections:

\[
(0,1)^4=(1,0).
\]

The rational \(3\)-\(4\)-\(5\) phase does not:

\[
\left(\frac35,\frac45\right)^4
=
\left(-\frac{527}{625},-\frac{336}{625}\right).
\]

The instrument returns:

| analytic cycle | mode 1 | mode 2 | mode 3 |
|---|---|---|---|
| torus longitude | identity | \((-527/625,-336/625)\) | identity |
| quadric conic | \((-527/625,-336/625)\) | identity | \((-527/625,336/625)\) |

Only identity holonomy admits an arbitrary nonzero fixed current in this two-coordinate phase
fiber. The same geometrically closed body can therefore be resonant for one mode and obstructed
for another. This is a concrete exact form of “the ecology crystallizes greater structure”: the
structure is the recurrence or residual caused by the complete passage, not a visual loop label.

## Conservative fluid-like circulation

The first fluid construction is deliberately finite and structural. It is not a claim to have
implemented Navier–Stokes.

Let \(x\) be exact signed chart values on a declared collection of analytical arcs, let
\(\Omega=\operatorname{diag}(C_i)\) be positive capacities, and let \(A\) satisfy

\[
A^\mathsf T\Omega+\Omega A=0,
\qquad
A\mathbf 1=0.
\]

For exact interval \(h\), the Cayley successor is

\[
Q
=
\left(I-\frac h2A\right)^{-1}
\left(I+\frac h2A\right).
\]

The new shared `ExactRatMatrix` owns the checked exact rational matrix construction, multiplication,
application, transpose, and certified Gauss–Jordan inverse. The advection owner forms \(Q\) once
and proves:

\[
Q^\mathsf T\Omega Q=\Omega,
\qquad
Q\mathbf1=\mathbf1.
\]

Consequently every event preserves

\[
\mathbf1^\mathsf\Omega x
\quad\text{and}\quad
\frac12x^\mathsf\Omega x
\]

exactly.

A claimed circulation covector is not accepted merely because it is a left eigenvector of \(Q\).
`new_on_field` first checks that its arc chain has zero boundary in the caused analytical-junction
incidence. It then checks that the covector is left-fixed by \(Q\). This implements a finite
Kelvin-like receipt without deriving a cycle from projected appearance.

The two four-arc cycles begin with

\[
x_T=(1,2,4,8),\qquad x_Q=(3,5,7,11).
\]

Across 24 exact Cayley successors the local values change, while every event returns

\[
\text{total}=41,\qquad
E=\frac{289}{2},\qquad
\Gamma_T=15,\qquad
\Gamma_Q=26
\]

with zero residuals.

The growing rational denominators are lawful exact phase faces of the recurrent Cayley map. They
also identify a concrete optimization problem: retain or factor a recurrent operator/orbit word
instead of repeatedly expanding its rational face. Replacing the values by floats would conceal,
not solve, that recurrence.

## The receiver obtains a resonance image after the current exists

`ExactAnalyticFieldWaveLaw::restrict` enumerates the sparse contemporary traveling sections, not a
screen grid. Every returned section includes:

- analytical arc and support germ;
- source and target caused junctions;
- exact local unit-conic phase;
- exact point and tangent on the implicit body;
- exact complex current and energy; and
- physical delay and remaining arrival time.

Sections at one exact point enter one `ExactReceiverPhasePopulation`. Same-mode currents superpose
before response; distinct modes remain separate. Only then does the declared outer receiver form
its premultiplied primary/alpha/transmittance face.

Across 24 wave successors the instrument returned 264 changing analytical sections and 96
receiver contacts after the header rows in their traces. The number of co-present contacts
alternated between three and five as currents crossed the two cycle orientations and the material
interface. The final exact traveling energy was \(25\), equal to cumulative source work. Every
passive scattering residual was zero.

This is a resonance image in the intended sense: a receiver-relative quotient of a physically
changing current. It is not a colored picture standing in for the dynamics.

## Returned files

- `analytic_geometry.tsv` — every exact arc, support, caused endpoints, and tangent;
- `interface_optics.tsv` — propagating/grazing/evanescent fibers and lawful amplitude status;
- `cycle_holonomy.tsv` — exact mode-local loop return;
- `wave_ticks.tsv` — event, source work, energy, front, and contact populations;
- `wave_sections.tsv` — every contemporary exact analytical traveling section;
- `interface_scattering.tsv` — every reached junction and passive certificate;
- `receiver_contacts.tsv` — co-present modal populations and receiver response;
- `conservative_advection.tsv` — changing values and exact total/energy/circulation receipts.

No file is source standing. All are downstream observation membranes.

## What is now owned, and what is concretely open

The engine now owns:

1. exact quadric-conic and torus longitude/meridian carriers;
2. exact path-owned phase winding independent of endpoints;
3. mode-local material incidence;
4. exact reflection and unsquared transmitted normal fibers;
5. exact separation of propagating traveling power from grazing/evanescent obstruction;
6. exact analytical-cycle holonomy;
7. exact capacity-skew conservative advection over boundary-certified cycles; and
8. exact current-to-receiver resonance contacts.

The next physical constructions are specific rather than universal mysteries:

- a reactive boundary-storage current must receive `EVANESCENT_OPEN`, carry its non-traveling
  phase/decay and stored energy, and return that energy into later traveling current;
- a volume-form advection owner must transport on arbitrary-grade caused cells, using exact
  primal/dual incidence and material capacity rather than only an admitted analytical-arc chart;
- electromagnetic polarization requires vector/bundle-valued phase sections and interface
  doctrine beyond the present scalar guide; and
- fluid–optical coupling must be a declared interaction by which the conservative material current
  changes later wave dispersion or interface incidence. Co-presence on one body does not silently
  authorize that coupling.

These are the current application-level conditioning capabilities not yet founded. They are not a
request for one external “general law.”

## Research relations

- Desbrun, Hirani, Leok, and Marsden,
  [*Discrete Exterior Calculus*](https://arxiv.org/abs/math/0508341), supplies the exact
  arbitrary-dimensional incidence/differential-form register which motivates the later volume
  current.
- Pavlov, Mullen, Tong, Kanso, Marsden, and Desbrun,
  [*Structure-Preserving Discretization of Incompressible Fluids*](https://arxiv.org/abs/0912.3989),
  motivates treating energy and Kelvin circulation as structural receipts rather than toleranced
  after-the-fact diagnostics.
- Doval et al.,
  [*Fresnel coefficients, coherent optical scattering and planar waveguiding*](https://arxiv.org/abs/2206.12321),
  relates interface scattering, guided modes, and resonance conditions. The present construction
  uses a bounded scalar exact guide and does not claim its full electromagnetic derivation.
- Feng, Gkioulekas, and Crane,
  [*Points as Tori: Fast Pointwise Signed Distance for Point Clouds*](https://nzfeng.github.io/research/PointsAsTori/PointsAsTori.pdf),
  supports the use of analytical local torus germs queried without first committing to a global
  mesh or terminal resolution. The present temporal/current laws are laboratory constructions,
  not claims made by that paper.

## Verification

```bash
cargo fmt --all -- --check
cargo test -p holonic-engine --lib
cargo test -p holonic-engine --lib analytic_field::tests -- --nocapture
cargo test -p holonic-engine --lib dimensional_wave::tests -- --nocapture
cargo run -p holonic-engine --example analytic_field_transport -- \
  output/analytic-field-transport
```

Formatting is clean. The complete library suite returns 237 passed, zero failed, and two
device-only tests ignored. The focused suites pass. The instrument completes all 24 wave and 24
advection successors and refuses any nonzero exact certificate residual.
