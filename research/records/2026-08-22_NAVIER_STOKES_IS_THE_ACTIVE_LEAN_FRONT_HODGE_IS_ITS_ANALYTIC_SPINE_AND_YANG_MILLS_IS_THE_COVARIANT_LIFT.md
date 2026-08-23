# NAVIER–STOKES IS THE ACTIVE LEAN FRONT, HODGE IS ITS ANALYTIC SPINE, AND YANG–MILLS IS THE COVARIANT LIFT

**Date:** 2026-08-22  
**Purpose:** the Claude-readable schedule and deed contract for Brandon's parallel Lean research line  
**Authority boundary:** `[definition]` This record schedules a user-directed mathematical research
track beside Claude's active BSD work. It does not alter `blueprint/THE_ROADMAP.md`, displace the
Rust/CUDA construction frontier, or authorize an update to `CONSTRUCTION_STATE.md`.

## The order

1. `[established-bounded; formal-checked]` **N1 — local vorticity transport on the actual `R³`
   carrier.** `NavierStokesVorticity.lean` now constructs the velocity Jacobian, curl, cross/Lamb
   interaction, differentiable addressed velocity-to-jet-to-vorticity passage, exact local curl
   kernel, `C²` pressure-annihilation square, divergence-of-vorticity identity, nonlinear
   transport/stretching identity, and a jet-level differentiated momentum/vorticity balance. At
   every strictly positive time, the repository's `SmoothSolution` carrier now supplies the
   differentiable addressed occurrence, the Lamb identity, the pressure-annihilation square, an
   admitted second-jet/vorticity-Jacobian passage, both derivative-compatibility squares, the
   actual nonlinear vorticity transport identity, and `div curl(u) = 0`. `[open]` Constructing the
   force jet and identifying the time and viscous ports with the time derivative and Laplacian of
   vorticity remain the next N1 analytic seams.
2. `[open]` **N2 — periodic energy and Hodge–Leray transport.** Introduce an actual three-torus or
   fundamental-domain integration owner, prove pressure and advection cancellation, construct the
   divergence-free/gradient splitting, and retain the harmonic and boundary alternatives rather
   than treating pressure as a scalar governor.
3. `[open]` **N3 — parabolic scale transport.** Prove that the Navier–Stokes rebase
   `u_lambda(x,t) = lambda u(lambda x, lambda^2 t)` commutes with the PDE and calculate the induced
   faces on energy, enstrophy, helicity, and critical norms. The receiver must expose why the
   `L²` energy law is supercritical in three dimensions rather than promoting it to regularity.
4. `[open]` **N4 — scale-local flux and continuation fibres.** Formulate a receiver-indexed local
   regularity/continuation criterion at the critical grain, retain the shortest scale/history that
   separates regular from unresolved conduct, and connect exact boundary flux to the Hodge–Leray
   owner without manufacturing a global local quotient for incompressibility.
5. `[open]` **Y1 — the covariant lift to Yang–Mills.** Replace `d`, curl, and the linear Laplacian by
   a founded connection, curvature `F = dA + A wedge A`, covariant derivative, Bianchi identity,
   gauge rebase, and Yang–Mills heat flow. Noncommutation must return the curvature commutator; an
   abelian or fixed finite spectrum is not this deed.
6. `[open]` **H1 — Chern–Weil return into the algebraic Hodge boundary.** Only after the connection,
   curvature, Hodge star, compact geometry, and de Rham/cohomology passage exist may invariant
   curvature polynomials be transported into rational Hodge classes and compared with the
   cycle-class image. This is the first legitimate bridge to `HodgeConjecture.Datum`; it is not a
   proof that every rational Hodge class is algebraic.

`[project-postulate]` The order is asymmetric on purpose: Navier–Stokes supplies the sharpest
local nonlinear analytic occurrence; Hodge theory supplies its decomposition and elliptic
boundary machinery; Yang–Mills tests whether the same passage survives nonabelian covariant rebase;
and algebraic Hodge enters only after Chern–Weil produces an actual typed cohomological edge.

`[definition]` P versus NP is outside this worktrack. Poincaré is already represented and the
mathematical proposition is closed; neither is allowed to interrupt the active fluid/gauge squeeze.

## The existing holonic owners and the missing edge

`[proved-derived; formal-checked]` `Millennium/Swing.lean` owns the swing as harmonic conjugation and,
on the frozen board, as the half-turn `a |-> 2b-a`. It proves involution, fixed anchor, order-sensitive
composition, parity preservation, and orientation reversal. In the vorticity deed it will type the
antisymmetric cross interaction: exchanging its two rays is exactly the zero-anchored half-turn.

`[proved-derived; formal-checked]` `Foundation/Lineage.lean` owns the addressed span
`X <- W_f -> Y`. Its serial composite retains both occurrences and their joining equality, while
its relational shadow forgets that population. The velocity-to-Jacobian-to-vorticity construction
must therefore be an addressed composite, not merely the equation `omega = curl u`.

`[proved-derived; formal-checked]` `Millennium/Coupling.lean` owns a two-step additive
`TransportChain`, its collapsed source population, realized middle population, retained middle
population, and homological obstruction. The local symmetric-curl passage belongs here: symmetric
matrices enter the complete Jacobian-chart population and curl carries them to zero. This source is
larger than the population of realized pressure Hessians; `C²` Hessian symmetry supplies the actual
pressure entrance separately.

`[established-bounded; measured]` No Lean structure named `HolonicInteraction` presently stands.
The typed research object has four roles—source current, standing intermediary lattice, dynamic
perturbation, and perspective receiver—and retains the plural junction/path population. The local
fluid deed will expose those roles in its interaction profile, but will not counterfeit the missing
general owner or use the phrase as proof.

`[interpretation]` In the first fluid occurrence, velocity is the situated current, its Jacobian is
the standing local transport, vorticity is the antisymmetric receiver face, and the cross/Lamb term
is the interaction residue that is invisible to the symmetric pressure-Hessian chain. This reading
is useful only because the following exact linear identities are independently proved.

## N1 deed contract

`[definition]` **Source owners:** `NavierStokes.Space`, `fderiv`, `gradient`, `Swing`,
`AddressedPassage`, and `TransportChain`.

`[definition]` **Port types:** `(velocity field, point) -> continuous linear Jacobian -> matrix
chart -> vorticity vector`; and `symmetric Jacobian -> arbitrary Jacobian -> curl vector`.

`[definition]` **Event occurrence:** one addressed field/point occurrence whose derivative
occurrence joins by literal equality to the curl occurrence.

`[definition]` **Predecessor identity:** the pair `(u,x)` remains in the composite occurrence; equal
vorticity faces do not identify velocity fields, points, or Jacobians.

`[definition]` **Local constitutive law:** Mathlib's coordinate cross product, antisymmetric curl face,
matrix action, transpose action, and the Lamb identity
`J u = J^T u + curl(J) cross u`.

`[definition]` **Receiver question:** which part of the local velocity jet survives the
antisymmetric curl receiver, and which part is annihilated?

`[definition]` **Returned consequence:** an exact local kernel theorem identifying the annihilated
matrix population with symmetric Jacobians, an exact Lamb decomposition, a differentiability-
admitted lineage witness from an `R³` velocity occurrence to its vorticity, and the local
transport/stretching balance at a mixed-symmetric second jet.

`[open]` **Alternatives retained:** constructing the force jet under its separate force-smoothness
port, commuting curl with time/Laplacian derivatives, treating the `t = 0` boundary by
within-derivatives, the global incompressibility projection, periodic integration, critical
continuation, and all four official Navier–Stokes conclusions.

`[project-postulate]` **Grade bar:** the deed closes only if Lean checks the exact identities on the
actual three-dimensional carrier with no `sorryAx`. A finite grid, numerical trajectory, imported
fluid solver, scalar pressure heuristic, or analogy to the existing Kelvin fixture does not pass.

## Relation to Claude's BSD line

`[definition]` Claude retains the active BSD family trajectory. This worktrack neither duplicates
`FamilyPrimeRank` nor asks BSD status prose to schedule it.

`[interpretation]` The useful cross-pressure is structural: both lines must keep local occurrences,
ordered transports, scale families, and the population collapsed by a receiver. Any later common
lemma must be earned as an actual shared type or commuting passage; the word “holonic” alone is not
the bridge.

## The material-polygon insertion belongs to Navier--Stokes

`[definition]` Brandon's n-gon, unicursal-stroke, angle, gyroparallelogram, time-orientation,
heat/entropy, and gravity prompt is attached to the Navier--Stokes worktrack. The immediate order is
therefore `local vorticity -> material polygon -> circulation evolution -> periodic/Hodge
decomposition -> scale-local flux`; it is not a separate general-relativity schedule.

`[established-bounded; measured]` The available Claude transcript contains the late n-gon and
gyroparallelogram prompts but no direct prose response after them. Claude continued the BSD family
descent. His six “pins” are six arithmetic placement lemmas using sign, `p`-adic valuation parity,
and `2`-adic valuation parity; the three binary readings produce eight cells. They are not six
geometric vertices, and no `2^6 -> hexagon` theorem is present.

`[proved-derived; formal-checked]` `Millennium/NavierStokesMaterialPolygon.lean` now defines an
`extra + 3`-vertex Lagrangian polygon on the actual `NavierStokes.Space` carrier. Every addressed
vertex has a genuine within-derivative and obeys the velocity field through `derivWithin` on the
oriented half-line `Ici 0`; every time-slice retains its full cyclic edge population; and Lean
proves that the oriented boundary sum is zero at every time. `SolutionMaterialPolygon` binds this
carrier to the velocity and pressure of one admitted `SmoothSolution`.

`[proved-derived; formal-checked]` At every receiver time, the complete cyclic population of
pressure differences telescopes to zero. The module also defines a left-endpoint polygonal
circulation receiver and proves that a spatially constant current has zero circulation because the
retained edge population closes.

`[proved-derived; formal-checked]` The stronger material face is the symmetric/trapezoidal edge
pairing, which retains the current at both endpoints. Lean proves that the contribution caused by
motion of the material edges is half a cyclic kinetic-energy difference on each edge and therefore
cancels exactly around the closed polygon.

`[proved-derived; formal-checked]` `Millennium/NavierStokesCurvedTransport.lean` installs a finite
Kelvin balance certificate on an admitted `SmoothSolution`: `MaterialCirculationBalance` retains
pressure-edge, viscous, and forcing returns separately; cyclic cancellation removes pressure; and
Lean proves conditional constancy of the symmetric circulation on the zero-viscous-return and
zero-forcing-return fibre.

`[proved-derived; formal-checked]` `Millennium/NavierStokesKelvin.lean` now owns the genuine closed
path receiver: velocity is lowered to a spatial one-form by the Euclidean inner product and
integrated with Mathlib's `curveIntegral`. `VelocityKelvinCertificate` retains curve integrability
at every nonnegative receiver time, so the admitted occurrence cannot enter through the integral's
totalized non-integrable value. `KelvinCertificate` proves that a differentiable curve-circulation
with zero derivative on `Ici 0` is constant between every two nonnegative times;
`CurveCirculationBalance` reaches the same result by setting its retained source to zero.

`[open]` The next Kelvin deed differentiates the time-dependent curve integral, derives its source
from `SmoothSolution.momentum`, realizes viscosity and force as boundary/area fluxes, and proves the
polygon-to-smooth-loop passage. The finite and curve-integral receivers now expose both ends of that
analytic construction.

`[proved-derived; formal-checked]` `PolygonTurnLedger` retains every interior and exterior angle,
a declared half-turn, the local supplementary law, and the winding-one exterior return. From those
explicit hypotheses Lean derives the interior sum `(extra + 1) * halfTurn`, hence
`(extra + 1) * pi` for an `extra + 3`-gon. `TurnPresentation` separately proves that the
actual-minus-reference defect is additive under componentwise pairing and invariant under a common
additive coordinate shift.

`[proved-derived; formal-checked]` `PolygonGaussBonnet` now retains an addressed bulk-curvature
population beside all boundary angles, assumes the bulk-plus-boundary full-turn law, and proves
that total angle excess is exactly total bulk curvature. The previous flat turn ledger embeds as
its zero-curvature fibre.

`[proved-derived; formal-checked]` `TriangulatedGaussBonnetLedger` reaches below that interface: it
retains every face/corner angle, assumes only the triangular face-angle budget and the Euler
incidence count of the chosen triangulation, defines interior curvature and boundary turning
locally, and derives the discrete Gauss--Bonnet sum
`sum bulkCurvature + sum boundaryTurn = 2 * pi * eulerCharacteristic`.

`[open]` The Gauss--Bonnet realization deed now has exact ports: construct principal boundary turns
and bulk curvature from a metric connection, derive the retained bulk-plus-boundary law, and bridge
the existing crossing ledger's winding to that realized geometry.

`[proved-derived; formal-checked]` `ReturnedQuadrilateral` retains source, two transported arms,
and the actual returned point. Its flat fourth point is proved equal to a frozen-board Swing through
the left anchor followed by transport of the right edge; subtracting that completion gives a
translation-invariant return defect. On a scalar field, its undivided four-point face is the
existing `swingPair`, and the existing affine rebase theorem transports its two coordinates by one
common square. A nonzero affine scale and an admissible starting pair preserve both admissibility
and projective equivalence.

`[proved-derived; formal-checked]` `Geometry/Gyrogroup.lean` now owns the gyrogroup operation, zero,
inverse, gyration equivalences, gyroassociativity, gyration automorphism, loop law,
gyrocommutativity predicate, coaddition, and based gyroparallelogram. Its exact additive instance
proves that the gyroparallelogram reduces to `left + right - source`; the material-quadrilateral
module proves this is the same completion obtained by Swing followed by edge transport.

`[proved-standard; cited]` The implemented gyrocommutative completion uses Ungar's standard
condition `D = (B boxplus C) minus A`, equivalently the gyrovector law relating the two based arms
to the returned diagonal; see [Ungar, *Hyperbolic Barycentric Coordinates*](https://ajmaa.org/searchroot/files/pdf/v6n1/v6i1p18.pdf).

`[open]` The next gyrogeometric deed is the nontrivial Möbius or Einstein-ball instance, after which
the repository's measured finite `Gyration` can be compared to its path-return automorphisms and
Thomas-precession face through an explicit homomorphism.

`[proved-derived; formal-checked]` The exact coupling now formalized is
`Lambda(n,s) = 2^n C / (2^s r)`. Advancing both binary fork depth and dyadic denominator depth by
one leaves it fixed, and the depth-two settled-scale face is `2^2 (C/r) = 4 C/r`.

`[proved-derived; formal-checked]` `EinsteinFluidDynamics` now constitutes a covariant bilinear
source field from the actual local velocity and pressure through an explicit coupling interface.
The interface retains the supplied metric, Einstein tensor, covariant divergence, tensor field
equation, contracted Bianchi return, and metric compatibility as distinct ports. Their composition
with nonzero coupling derives covariant source conservation, and every declared linear
conservation receiver reads zero. Under `UsesRefineForkCoupling`, every tensor receiver reads the
field equation with coefficient `4 * (C/r)`.

`[interpretation]` In the full-turn calibration, `Theta = C/r` turns the checked receiver equation's
coefficient into `4 Theta`. If the intended curvature target instead uses `4 theta/r`, the second
inverse-length factor belongs in the typed curvature realization rather than being erased inside
the scalar receiver.

`[open]` The Einstein realization deed is now concrete: instantiate the abstract tangent fibre and
tensor-field ports with a symmetric nondegenerate Lorentzian metric, compatible connection,
derived Einstein tensor, causal cone, calibrated units, and fluid stress-energy; then prove the
receiver family separates the tensor equality. That realized background is the curved manifold on
which the Kelvin and Gauss--Bonnet passages will be transported.

## First returned construction

`[proved-derived; formal-checked]` `Millennium/NavierStokesVorticity.lean` lifts Mathlib's
`crossProduct` into `NavierStokes.Space`, proves exchange as the zero-anchored `Swing`, and proves
the conventionally oriented Lamb identity
`J u = Jᵀ u + curl(J) × u`.

`[proved-derived; formal-checked]` The named equality `curlAddHom.ker = symmetricJacobians` is the
complete local reconstruction-fibre statement for the matrix curl receiver. Its corresponding
`TransportChain` glues, so the middle homological obstruction is trivial at exactly that aperture.
This does not assert a global curl-free field is a gradient.

`[proved-derived; formal-checked]` A `ContDiffAt ℝ 2` scalar pressure has a symmetric gradient
Jacobian by Mathlib's symmetric-second-derivative theorem transported through the Riesz map;
therefore `vorticityAt (gradient p) x = 0` is proved without leaving Hessian symmetry as an axiom.

`[proved-derived; formal-checked]` Smoothness on the nonnegative space-time half-cylinder descends
to a smooth spatial slice at every `t > 0`. Consequently, a `SmoothSolution` supplies the admitted
velocity-to-Jacobian-to-vorticity occurrence and its pointwise Lamb identity at each positive-time
event. The strict inequality is essential to this theorem; the initial-time boundary remains an
open within-derivative face.

`[proved-derived; formal-checked]` The same positive-time slice passage downgrades the solution's
pressure smoothness to `C²`, so the abstract pressure-Hessian chain now returns
`vorticityAt (gradient (pressure · t)) x = 0` on the actual `SmoothSolution` carrier.

`[proved-derived; formal-checked]` With `J i j = partial_j u_i` and
`H i j k = partial_k partial_j u_i`, the module proves

```text
curl ((u dot grad)u)
  = (u dot grad)omega - (omega dot grad)u + (div u)omega,
div omega = 0.
```

`[proved-derived; formal-checked]` The positive-time `C∞` slice now supplies a `C²`-admitted
`secondJetAt`, its mixed-partial symmetry, and an addressed composite from the retained
field/point occurrence through that second jet to its induced vorticity Jacobian. A separate exact
trace bridge transports `SmoothSolution.incompressible` into the matrix receiver.

`[proved-derived; formal-checked]` A continuous-linear curl receiver on derivative maps proves that
the induced vorticity Jacobian is the derivative chart of the actual vorticity field. A second
product-rule square proves that `advectionJacobianFromJets` is the derivative chart of the actual
advective field. These are identities of the admitted derivatives, not analogies between nearby
coordinate fixtures.

`[proved-derived; formal-checked]` Composing those squares with the incompressible jet identity
returns, on every positive-time `SmoothSolution` occurrence,

```text
curl ((u dot grad)u) = (u dot grad)omega - (omega dot grad)u,
div omega = 0.
```

`[proved-derived; formal-checked]` On the incompressible fibre, applying the linear curl transport
to a differentiated momentum balance removes the symmetric pressure jet and returns the local
vorticity balance with transport and stretching as distinct ordered terms.

`[open]` The remaining attachment to `SmoothSolution` owes the force jet under a separate
`ForceCondition`, conversion of the interior `derivWithin` time face, and commutation of spatial
curl with the time derivative and Laplacian. The differentiated-momentum theorem exposes these
ports and does not claim them.

## Validation receipt

`[established-bounded; measured]` Focused checks from
`soma/formal/elementary-holonics` returned:

Both final invocations addressed source closure
`sha256:d179a17c236bbdda07d2469e0dc5bba4f518f92f96efc93c2c869a044097231b`.

| Command | Elapsed | Exit | Purpose |
|---|---:|---:|---|
| `lake env lean ElementaryHolonics/Millennium/NavierStokesVorticity.lean` | 28.9 s | 0 | complete N1 owner and inline axiom audit after realized second-jet attachment |
| `lake build ElementaryHolonics.Millennium.NavierStokesVorticity` | 25.9 s | 0 | named owner closure from the Lake build graph |

`[proved-derived; formal-checked]` Every printed theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or a custom mathematical axiom.
An exact declaration scan also returned no `sorry`, `admit`, `axiom`, or `sorryAx` occurrence.

`[established-bounded; measured]` An independent read-only N1 audit checked the row/column and
second-jet conventions, Lamb orientation, product-rule advection jet, divergence cancellation, and
the sign of the stretching term. A final delta audit separately checked the differentiated momentum
and rearranged local vorticity balance. A solution-attachment audit then checked the positive-time
neighbourhood argument, the infinite-to-`C²` regularity downgrade, and both totalized-derivative
layers in the pressure theorem. It found no remaining theorem or sign correction after the
differentiable-occurrence and local-kernel repairs. A realized-second-jet audit then checked the
derivative order, addressed join, trace orientation, vorticity-derivative square, product rule, and
final nonlinear sign. Its only requested repair was to stop presenting the totalized trace bridge
as admitted at `t = 0`; the solution theorem is now restricted to the positive-time occurrence.
The `t = 0` boundary and time/Laplacian commutation squares remain explicitly open.

## Material, Kelvin, curvature, and gyro validation receipt

`[established-bounded; measured]` The final source closures are:

| Owner | SHA-256 |
|---|---|
| `Geometry/Gyrogroup.lean` | `745584b6cdd1453b53d8f4708dc252da79a90a4a0c88b51641ef8e09429ecae0` |
| `Millennium/NavierStokesMaterialPolygon.lean` | `971a22468740e10c976fbbe578e9fbe0c03291d540424b575523bf5dbbd8fb77` |
| `Millennium/NavierStokesCurvedTransport.lean` | `d710b600c07431f2a615bbc64f3dd1fed786822356a341bb642e72f3d4f4d48d` |
| `Millennium/NavierStokesKelvin.lean` | `f565bd61d453703ff2f7fcd392b04e02de1c203b7385216768eafde5cbbed6d1` |
| `ElementaryHolonics.lean` import surface | `3631ec11252e13bcc8ddb42a16ea957b060ec18cc75cc2d3db9fc54e2a2c3ed6` |

`[established-bounded; measured]` Focused final builds from
`soma/formal/elementary-holonics` returned:

| Command | Reported owner time | Exit | Purpose |
|---|---:|---:|---|
| `lake build ElementaryHolonics.Geometry.Gyrogroup` | 1.0 s | 0 | gyrogroup, coaddition, and gyroparallelogram closure |
| `lake build ElementaryHolonics.Millennium.NavierStokesMaterialPolygon` | 3.9 s | 0 | material polygon, symmetric circulation, Swing/cross-ratio bridge, scale/fork law |
| `lake build ElementaryHolonics.Millennium.NavierStokesCurvedTransport` | 4.9 s | 0 | conditional finite Kelvin, triangulated Gauss--Bonnet, Einstein conservation transport |
| `lake build ElementaryHolonics.Millennium.NavierStokesKelvin` | 3.4 s | 0 | integrable curve receiver and Kelvin constancy |
| `lake build ElementaryHolonics` | 2.4 s | 0 | public aggregate import closure |

`[proved-derived; formal-checked]` Every printed theorem in the four-owner cone depends only on
`propext`, `Classical.choice`, and `Quot.sound`; the gyrogroup flat theorems need only a subset.
The final exact scan found no declaration of `axiom` and no occurrence of `sorry`, `admit`, or
`sorryAx`; `git diff --check` returned clean.

`[established-bounded; measured]` Independent read-only audits checked cyclic indexing, derivative
totalization, Swing orientation, boundary-order cross ratio and admissibility, the standard
gyroparallelogram formula and gyrocommutative port, the symmetric moving-edge cancellation, the
Euler/angle algebra of discrete Gauss--Bonnet, and the covector-valued divergence in Einstein
conservation. Their requested type repairs were incorporated before the final receipts, including
the explicit `CurveIntegrable` witness on every admitted velocity-loop circulation.
