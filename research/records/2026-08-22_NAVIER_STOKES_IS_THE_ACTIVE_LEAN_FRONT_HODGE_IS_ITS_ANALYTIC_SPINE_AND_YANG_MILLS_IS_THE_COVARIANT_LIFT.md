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
   differentiable addressed occurrence, the Lamb identity, and the pressure-annihilation square.
   `[open]` Constructing the solution's actual second and force jets and identifying the time and
   viscous jet ports with the time derivative and Laplacian of vorticity remain the next N1
   analytic seams.
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

`[open]` **Alternatives retained:** constructing the product-rule second jet and force jet from the
existing smoothness fields, commuting curl with time/Laplacian derivatives, treating the `t = 0`
boundary by within-derivatives, the global incompressibility projection, periodic integration,
critical continuation, and all four official Navier–Stokes conclusions.

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

`[proved-derived; formal-checked]` On the incompressible fibre, applying the linear curl transport
to a differentiated momentum balance removes the symmetric pressure jet and returns the local
vorticity balance with transport and stretching as distinct ordered terms.

`[open]` The remaining attachment to `SmoothSolution` owes explicit construction of the actual
product-rule second jet and force jet, compatibility between that second jet and the derivative of
the first-jet chart, and commutation of spatial curl with the time derivative and Laplacian. The jet
theorem exposes these ports and does not claim them.

## Validation receipt

`[established-bounded; measured]` Focused checks from
`soma/formal/elementary-holonics` returned:

Both final invocations addressed source closure
`sha256:16a6de727811723534c59f4279827635243170942b0bcc0cfbedfd4e36a89ee7`.

| Command | Elapsed | Exit | Purpose |
|---|---:|---:|---|
| `lake env lean ElementaryHolonics/Millennium/NavierStokesVorticity.lean` | 22.1 s | 0 | complete N1 owner and inline axiom audit after solution attachment |
| `lake build ElementaryHolonics.Millennium.NavierStokesVorticity` | 30.0 s | 0 | named owner closure from the Lake build graph |

`[proved-derived; formal-checked]` Every printed theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or a custom mathematical axiom.
An exact declaration scan also returned no `sorry`, `admit`, `axiom`, or `sorryAx` occurrence.

`[established-bounded; measured]` An independent read-only N1 audit checked the row/column and
second-jet conventions, Lamb orientation, product-rule advection jet, divergence cancellation, and
the sign of the stretching term. A final delta audit separately checked the differentiated momentum
and rearranged local vorticity balance. A solution-attachment audit then checked the positive-time
neighbourhood argument, the infinite-to-`C²` regularity downgrade, and both totalized-derivative
layers in the pressure theorem. It found no remaining theorem or sign correction after the
differentiable-occurrence and local-kernel repairs; `t = 0`, realized solution second jets, and the
time/Laplacian commutation squares remain explicitly open.
