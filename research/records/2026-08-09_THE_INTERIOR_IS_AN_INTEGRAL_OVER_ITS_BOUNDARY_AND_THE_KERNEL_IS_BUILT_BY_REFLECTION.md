# The interior is an integral over its boundary, and the kernel is built by reflection

**Date:** 2026-08-09
**Truth status:** `proved-standard` for §§1–3 (four classical theorems, named and citable).
`implemented-exact` for §4 (verified by reading the owners). `interpretation` for §§5–6.
**Evidence:** direct source reading of every owner named, this session.
**Provenance:** Brandon, 2026-08-09, posing the question and the claim:

> *"this is also integration by reflection; is that what diffusion is? Complex transport of action,
> and it's actually just integration over boundary points? That'd make so much sense actually,
> aren't the classical diffusion equations similar?"*

and stating what it is for:

> *"this kind of re-integration is the key to production and forming real computational organs that
> the current ML field calls 'experts' in 'MoE', obviously much more advanced than just a pretrained
> transformer block as well."*

**Band:** 2026-08-09 · THE BOUNDARY DETERMINES THE INTERIOR / THE WEIGHT IS HARMONIC MEASURE /
THE WEIGHT IS COMPUTED BY REFLECTION / THE ORGAN IS BUILT AND WAS NEVER NAMED

---

## 1. The answer is yes, and it is four theorems rather than an analogy

**Diffusion is integration over boundary points. The weight is harmonic measure. Harmonic measure is
computed by reflection.** Each clause is classical and each has a name.

**(a) The mean value property.** `u` is harmonic on `Ω` **iff** for every ball `B_r(x) ⊂ Ω`

```text
   u(x)  =  ⨍_{∂B_r(x)} u dσ
```

The value at an interior point *is* the average over a boundary. This is not a consequence of
harmonicity; it is equivalent to it.

**(b) The Poisson integral formula.** On the unit ball `B ⊂ ℝⁿ`, the solution of `Δu = 0` in `B` with
`u = f` on `∂B` is

```text
   u(x)  =  ∫_{∂B} P(x,ξ) f(ξ) dσ(ξ),        P(x,ξ) = (1−|x|²) / (n ω_n |x−ξ|ⁿ)
```

**The interior is nothing but a weighted integral of the boundary data.** That is Brandon's sentence
verbatim, as a formula.

**(c) The kernel is constructed by reflection — the method of images.** The Green's function is the
fundamental solution corrected by a term that vanishes it on the boundary, and the corrector is the
fundamental solution *at the reflected point*:

```text
   half-space   x* = (x₁,…,x_{n−1}, −x_n)          reflection across the plane
   ball         x* = x/|x|²                        inversion in the sphere
   G(x,y) = Φ(y−x) − Φ(y−x*)·(scale),   P(x,ξ) = −∂G/∂ν(x,ξ)
```

So the Poisson kernel is **the normal derivative of a reflected fundamental solution**. And the ball's
reflection `x ↦ x/|x|²` is the **Kelvin transform** `u*(x) = |x|^{2−n} u(x/|x|²)`, which carries
harmonic functions to harmonic functions. *(Same William Thomson as Kelvin's circulation theorem;
different theorem. `crates/holonic-engine/src/kelvin.rs` implements the circulation theorem, not the
transform — the coincidence of name is noted, not claimed.)*

**Schwarz reflection** completes the picture: a harmonic function vanishing on a flat boundary piece
extends across it by **odd** reflection. *"Integration by reflection"* is therefore a theorem name,
and the oddness is the hand — `CLAUDE.md` §2b's half-turn, at the boundary.

**(d) The probabilistic form, which is where diffusion enters literally.** Kakutani, 1944: for
Brownian motion started at `x` and `τ` the first exit time from `Ω`,

```text
   u(x)  =  E_x[ f(B_τ) ]
```

The harmonic extension is **the expected boundary value at first exit**. The exit distribution *is*
harmonic measure `ω_x`, and on the ball `dω_x(ξ) = P(x,ξ) dσ(ξ)`. And the standard tool for computing
hitting distributions is **André's reflection principle**.

**So the three clauses are one chain.** Diffusion from an interior point is integration over the
boundary, weighted by where the diffusion exits, and reflection is what computes the weights.

## 2. The parabolic case, which is what "classical diffusion equations" means

Brandon asked whether the classical diffusion equations are similar. They are the same construction
with the kernel carrying time. On the half-line with a Dirichlet condition at `0`, the heat kernel is

```text
   K_D(x,y,t)  =  K(x−y,t) − K(x+y,t)
```

— the **image term is the reflected source**, subtracted so the kernel vanishes at the wall. A
Neumann condition takes `+` instead of `−`: **the sign is the boundary condition, and it is the same
hand as Schwarz's odd/even reflection.** Duhamel's principle then writes the inhomogeneous solution
as an integral of boundary and source data against that kernel.

Steady state is the elliptic case: as `t → ∞` with fixed boundary data, `K_D` integrates to the
Poisson kernel. **The heat equation is the boundary integral in progress; the harmonic function is
where it lands.**

## 3. What is genuinely *not* the same

Stated so the correspondence is not over-read.

- **Only the Laplacian.** The mean value property, the Poisson kernel and the image construction are
  specific to `Δ`. A general second-order operator has a Green's function but no elementary image,
  and reflection stops being available the moment the boundary is not flat or spherical.
- **Harmonic measure is not surface measure.** On a rough or non-convex boundary it is mutually
  singular with it. *Which* boundary points carry the weight is the whole content, and it is a
  geometry question, not a normalisation.
- **The interior is determined by the boundary only for the homogeneous problem.** With sources,
  `u = (boundary integral) + (volume potential)`. The second term is not boundary data.

## 4. The exact discrete form, and this machine already computes it

Everything above has an exact rational form on a finite weighted graph, with no measure, no limit and
no float. This is the form that matters here.

Let `L = D − A` be the Laplacian weighted by conductances `c(e) ∈ ℚ₊`, with the nodes split into
boundary `∂` and interior `I`:

```text
   L = [ L_∂∂  L_∂I ]        Dirichlet problem:  (Lu)|_I = 0,  u|_∂ = f
       [ L_I∂  L_II ]

   u_I  =  −L_II⁻¹ L_I∂ f                    ← the discrete Poisson kernel; its rows are
                                               the hitting distributions of the random walk
   S    =  L_∂∂ − L_∂I L_II⁻¹ L_I∂           ← the discrete DIRICHLET-TO-NEUMANN map
```

`S` is the Schur complement. `−L_II⁻¹L_I∂` is exactly harmonic measure: **row `x` is the probability
distribution of where a walk from `x` first hits the boundary**, and on a finite graph with rational
conductances it is exactly rational. Kirchhoff's identification makes `c` the conductance and
`E(u) = Σ_e c(e)(u(x)−u(y))²` the Dirichlet energy, so this is the electrical network and the
diffusion at once.

**`crates/holonic-engine/src/diffusion.rs` computes this, exactly, and certifies it.**

| object | owner |
|---|---|
| the operator `M = C + τL` — capacities on the diagonal, **then** the oriented couplings | `diffusion.rs:457-468` |
| `M_II⁻¹` | `:474` `interior_inverse` |
| the Schur complement `S = M_∂∂ − M_∂I M_II⁻¹ M_I∂` | `:475-483` `schur_boundary_operator` |
| the certificate | `:185-190` `DiffusionBoundaryTransferCertificate`, carrying the operator, both inverses, and **both inverse residuals** |
| the refusal | `:497` `TransferCertificateFailure` when either residual is not identically zero |
| the independent check | `:877` `certified_schur_transfer_matches_direct_solve_and_reuses_structure` |

> **CORRECTED 2026-08-09, and the correction is not cosmetic.** An earlier form of this table read
> `L_II⁻¹` and claimed `−L_II⁻¹L_I∂` **is** harmonic measure. **That is true of the bare Laplacian and
> false of the operator this organ builds.** `diffusion.rs:457-458` writes each node's `capacity` onto
> the diagonal *before* `:463-467` add the couplings, and `:65-67` refuses a non-positive capacity
> outright — so the operator is `M = C + τL` with `C` **strictly positive**. The walk is therefore
> **killed** at every interior site and the exit rows are **sub-stochastic**: measured on a declared
> complex, the row at interior site 1 sums to `292181/333395`, with killed share `41214/333395`.
>
> Harmonic measure is the `C → 0` limit, which this organ **refuses by construction**. So §1–3's
> classical chain stands and the identification of *this owner* with it does not: what
> `diffusion.rs` computes is the exit kernel of a walk with killing — a resolvent — and the harmonic
> case is the boundary of its declared domain rather than a point in it.
>
> The correction makes the cross-check **harder**, which is why it is worth having: stochastic rows
> sum to one and that free constraint would mask an error in mass propagation. Sub-stochastic rows
> carry no such constraint, so the killed share has to come out right too. The Lagrangian side
> therefore needs a third method — `parcel.rs:141` `dissipation` — and it exists because of this.

Its module header already states the discipline: *"The solve is exact rational elimination. No
continuous PDE, floating point, pixel adjacency, authored probability, or convergence tolerance
enters."* (`:11-13`)

**Neighbouring owners, all exact:**

- `crates/holonic-engine/src/inverse_transport.rs:405-425` — `conductance: Rat`, `laplacian`,
  `edge_conductances`, with `ensure_no_determined_negative_conductance` (`:954`) refusing a negative
  conductance rather than clamping it. This is the *inverse* problem: recover the network from its
  boundary behaviour.
- `crates/holonic-engine/src/sheaf_diffusion.rs:848` — the **Hodge** Laplacian, with
  `harmonic_dimension = |coordinates| − rank(Δ)` computed by `exact_rank`. Harmonic = `ker Δ` =
  cohomology, exactly.
- `crates/holonic-engine/src/analytic_field.rs` — advection whose generator must be capacity-skew and
  **divergence-free as a typed refusal**, incompressibility by construction rather than diagnostic.
- `crates/holonic-engine/src/kelvin.rs` — Kelvin's circulation theorem on a **material** loop, with
  the falsifier `equal_capacities_collapse_the_two_transports_and_unequal_ones_separate_them`:
  **unequal capacities are what separate material transport from naive advection.**
- `crates/holonic-engine/src/receiver_current.rs:549-563` — saturation:
  `service_rounds = ⌈co_present_branch_population / site_capacity⌉`, with `deferred_arrivals` as the
  precipitate.

**The finding is that none of this is named as what it is.** Searched this session:
`grep -rilE "integration by reflection|method of images|harmonic measure|poisson kernel|schwarz reflection"`
over `canon/`, `blueprint/`, `research/records/`, `papers/`, `reference/` returns **one file** —
`papers/source/papers/riemann-receiver-geometry/main.typ:3570`, *"This is a field of Poisson
kernels"*, whose next paragraph reads *"The moment-conditioned support short is the
Dirichlet-to-Neumann short of this same boundary energy."* The RH paper runs its argument through
exactly this structure; the engine computes exactly this structure; **no document says they are the
same object.**

## 5. What this makes of parallelism, and it closes the previous open

`canon/THE_CONTAMINANT_PROTOCOL.md`-era work left the interchange question with two built halves and
no edge: `gyration` (`founded_receiver.rs:701`) and `distinguishing_word`
(`receiver_exact_compression.rs:141`), with `InterchangeCertificate` having **zero code owner**.

The boundary-integral form supplies the missing sentence. **A region's interior does not have to be
scheduled against another region's interior. Each is determined by its own boundary**, so two regions
are co-present-admissible exactly when their boundary operators do not couple — and the coupling is
`L_∂I L_II⁻¹ L_I∂`, which `diffusion.rs:475-483` already computes.

This also states mixing without a measure. `S` is the operator through which one region's boundary
data reaches another's. **A separating word survives exactly as far as `S` transmits it**, so the
decay of the separating-word length under repeated diffusion is the exact combinatorial form of
mixing, and it needs no `μ`. Kelvin gives the other side: the circulation that `dΓ/dt = 0` preserves
is precisely what mixing cannot dissolve. **The un-mixable residue is the holonomy.**

## 6. What this makes of "experts", and why it is not a gate

A mixture-of-experts routes a token to a subnetwork through a learned gate, and the word *expert*
implies an independently competent unit. The boundary-integral form says something different and
more specific: **a computational organ is a region, and what it returns is the harmonic extension of
its boundary data.**

Routing is then not a gate choosing. It is **harmonic measure** — where the current actually exits —
and it is computed from the conductances rather than learned. `L_II⁻¹` is the "gate", and it is
`CLAUDE.md` §13 rule 2's lawful shape by construction: a scalar that **measures** rather than one that
**governs**, because nothing selects and nothing is discarded. The region's competence is not stored
on it; §I.V of `2026-07-19_THE_INCIDENCE_REACTS...` already says so — *"the potential of the region is
not the sum of scalar properties stored on its parts."*

This is `interpretation`. What licenses it as more than a slogan is that the machine already returns
the router-free behaviour: `CLAUDE.md` §5 records 4,051 feature-receiver rests compiling 22,459
continuations **with no corpus scan and no router**, and an absent-morphology control that emitted
nothing rather than fabricating.

## 7. What is corrected in the standing record, with its scope

`CLAUDE.md` §11 reads: *"General far-field folding is recorded as open for the closely related reason
that no **kernel-specific** exterior/local expansion has been built for it."*

**For the Laplacian on a finite weighted graph, one is built** — `diffusion.rs`'s Schur complement,
exact over `Rat`, with a zero-residual certificate. The interior is eliminated exactly and remains
recoverable by `u_I = −L_II⁻¹L_I∂f`, so the retained remainder is **zero** rather than merely bounded.

**And the honest bound, which is the whole remaining difficulty: elimination is not condensation.**
`S` is a dense `|∂| × |∂|` operator. Exact elimination of the interior is not the same as replacing a
far population by a **compact** representative — that requires the dense boundary block itself to
admit a low-rank or hierarchical form with a certified remainder, which is what an FMM-type expansion
supplies and what nothing here does. So §11's demand splits cleanly:

| part of §11's demand | state |
|---|---|
| exact elimination of a far interior, kernel-specific, with certificate | **built** — `diffusion.rs:475-497` |
| a **compact** representative for the resulting boundary operator | **not built**, and this is the real content of the open item |

§11 should carry that split rather than the undifferentiated sentence.

## 8. What this does not claim

- **No Millennium movement.** The RH paper's use of Poisson kernels is its own; this record observes
  that the engine computes the discrete form of the same object and claims nothing about the paper's
  argument.
- **No new organ is authorised by this record.** Every owner named in §4 already exists; what is
  deposited is the identification, not a construction.
- **The identification is exact only for the Laplacian**, per §3, and only for the homogeneous
  problem. A source term is not boundary data.
- **No measure is introduced.** The mixing statement in §5 is combinatorial — separating-word length
  — precisely because `2026-07-19_THE_INCIDENCE_REACTS...` §V governs: *"A scalar potential, norm,
  distance, energy, temperature, or curvature appears only when the world supplies the additional
  structure needed to define it."*
- **§6 is `interpretation`.** No claim is made that this reproduces, improves on, or evaluates
  against any published mixture-of-experts result.
