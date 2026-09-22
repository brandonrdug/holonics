# Proposal: the Holon as a recursive generator–flux–observer object

**Date:** 2026-09-22  
**Status:** Research proposal for Claude iteration. It is not a cemented definition, proved theorem, implementation claim, or change to the active construction order.

## Proposal

A Holon is a recursively typed dynamical object whose current, constitution, generator family, contact flux, frame and receiver share one incidence and transport law. Each chart is itself a Holon at its grain, related to other Holons by typed transports and restrictions.

The SSM state and observation equations are a fixed linear chart of this object. The Holonic lift makes diffusion and flux constitutive operations, and allows the receiver itself to have state, material and dynamics.

## Existing owners and the gap

[Established, formal-checked] `Foundation/Holon.lean` defines an occurrence-bearing core `H_occ = (Ω, source, target, receive)`. Occurrences carry typed incoming/outgoing ports and a received face. It also defines serial composition through an exact joining occurrence, Cartesian and diagonal compositions, receiver maps and complete preimage fibres. `Ω` is an occurrence type, not an event archive.

[Established, source-inspected] Related dynamic owners already exist:

- `holonic_interaction::Medium` has the fixed-chart flow `q̇ = (Ω − M_contact)Gq + Bu` and its storage balance.
- `HolonicInteraction` binds a medium, storage form, skew structure and declared contact faces.
- `ExactDiffusionLaw` and `ExactSheafDiffusionLaw` return typed currents and energy balances.
- The fluid construction couples an internal field to velocity through a shared advection operator and its adjoint, with an energy/dissipation law.
- `HNN_FORMULA.md` records SSM, participation and field-refinement charts.
- `FractalPacking`, `HolonicRecurrentEcology.FirstArrival`, `ContinuingTower` and phase/carry owners encode generator words, restrictions and receiver-arrival populations.

The open gap is their joint signature and consuming operation: one recursive object whose state, observer, geometry, contact flux, changing constitution and scale restriction obey compatible equations. A previous tuple sketch left flux and observation as operations around a payload. This proposal makes them equations of the object.

## Candidate mathematical object

Let `K` be an oriented complex with boundary `∂`, and `V → K` its typed current and internal-mode fibres. A Holon at grain ℓ is proposed as

```text
H_ℓ = (H_occ;
      K_ℓ, ∂_ℓ, V_ℓ, Ψ_ℓ(τ), Θ_ℓ;
      G_ℓ, P_ℓ, F_ℓ, R_ℓ;
      {π_(m←ℓ)}_(m<ℓ))
```

`Ψ_ℓ(τ) ∈ Γ(K_ℓ,V_ℓ)` is the continuing joint current. `Θ_ℓ` is its constitution. `G_ℓ` is its typed generator family. `P_ℓ` is its admitted pair-contact family. `F_ℓ` is its frame and pairing; `R_ℓ` is its participating coholon/receiver-Holon's family. `π` restricts the whole object across grains.

Each generator `G_i(λ)` carries its domain/codomain, initial configuration, local clock and phase lift. Each pair contact carries geometry, rate ports, slip and material. Constitution, generator, contact and receiver maps are themselves typed Holonic operators, not untyped metadata.

A computational representation can use a finite typed arena and references for recursion. Every referenced chart still has the Holon signature, and its maps preserve ports, frames and pairings. Thus a chart is a Holon in its own right without requiring an infinitely nested in-memory value.

The evolving state includes geometry and phase, not only current coefficients:

```text
x_ℓ(τ) = (Ψ_ℓ(τ), {q_g(τ), θ̃_g(τ), modes_g(τ)}_g, receiver states, ...)
θ̃_g = θ_g + 2π n_g.
```

A section crossing updates integer winding through its carry cocycle. Each generator keeps its own clock.

## State and flux

An existing covariant storage/flux construction gives the linear physical chart

```text
q = C φ,                 J = −W d_A φ,
∂_τ q + ∂_A J = s,       L_A = d_A* W d_A + C.
```

Here `φ` is a situated section, `d_A` the connection-valued local difference, `J` oriented current, `∂_A` the declared boundary/adjoint operator and `s` exterior source. Pairing and sign convention belong to the law. This covariant storage–flux complex is an existing return, but is not yet the recursive HNN object proposed here.

For a nonlinear current section, let `μ_Θ[Ψ] = D_Ψ E_Θ[Ψ]` be the coholon effort. Let `d_G^U` be the oriented covariant difference over admitted contacts, using actual generator/frame transport `U_e`. For contact `e=(g,h)`, a representative face is

```text
(d_G^U μ)_e = U_(e←h)(γ, θ̃) μ_h − μ_g.
```

A proposed diffusive constitutive branch is

```text
j_diff = −M_Θ d_G^U μ,             M_Θ ⪰ 0,
∂_τ Ψ = A_(G,Θ)(Ψ, γ, θ̃) + B_K u − (d_G^U)* M_Θ d_G^U μ.
```

`A_(G,Θ)` carries admitted generator transport, conservative circulation and declared local reaction; `B_K u` injects source current through typed ports. The positive composition `(d_G^U)* M_Θ d_G^U` makes diffusion follow from incidence, constitutive effort and contact mobility.

For fixed material, closed boundaries and power-neutral `A_(G,Θ)`, this branch obeys

```text
d/dτ E_Θ[Ψ] = −⟨d_G^U μ, M_Θ d_G^U μ⟩ ≤ 0.
```

Source work, interface work, changing material and non-passive reaction contribute their actual terms. This does not assume every Holonic operator is a gradient flow or every physical constitution is positive definite.

The geometric state evolves under its own law, e.g. `∂_τ q_g = V_g(Ψ,Θ,G)` and `∂_τ θ̃_g = ω_g(Ψ,Θ,γ)`. Pair slip `J_e(ṡ_g,ṡ_h)` remains distinct from section difference `d_G^U Ψ`; a declared chart couples these ports where required. Equal coordinates or dimensions do not identify them.

Constitution changes through deposition of covectors that actually reach a locus: `Θ_next|_U = Θ|_U + Γ_U(j|_(∂U), η|_(∂U))`. Retained standing is the quotient sufficient for admitted future actions and receivers; a source fibre or defect remains when the quotient does not determine those futures.

## Observer equation

A passive coholon can read a face. An active receiving Holon also has its own current and constitution. The candidate coupled equations are

```text
∂_τ Ψ_H = F_H(Ψ_H; K_H, Θ_H, G_H) + B_H j_(R→H),
∂_τ Ψ_R = F_R(Ψ_R; K_R, Θ_R, G_R) + B_R j_(H→R),
y_R = ρ_R(Ψ_H|_Σ, Ψ_R, j_Σ, F_R).
```

The shared interface declares the relation between its directed currents and their power. For a passive physical coupling, one possible obligation is `P_(H→R)+P_(R→H)=−D_Σ`, with `D_Σ≥0`. A passive coholon is the specialization with no independent receiver state, reducing to a paired reading such as `⟨r̄_R | U_(R←H) Ψ_H⟩`.

This lifts the SSM observation equation to a participating receiver: it can change the receiving Holon's state and be changed by it through their shared current/material law.

## Helical generators and recursive scale

A generator word `G_w = G_(iₖ)…G_(i₁)` composes only when intermediate ports join. Its order, source address, clocks, winding and carry remain attached. In a toroidal/helical realization, `U_e` transports phase and frame over actual contact cells; declared loops return their holonomy. Co-presence alone does not create contact.

A restriction `π_(ℓ←ℓ+1)` acts on the whole Holon. With `T_(ℓ,w)` the full state/material/geometry evolution under word `w`, exact descent requires

```text
π_(ℓ←ℓ+1) ∘ T_(ℓ+1,w) = T_(ℓ,w) ∘ π_(ℓ←ℓ+1),
ρ_(ℓ+1) = ρ_ℓ ∘ π_(ℓ←ℓ+1).
```

The square must also preserve contact flux, constitution, clocks and receiver participation. If it fails, return a typed defect `δ_(ℓ,w)` and the interior/fibre it distinguishes. Compression of a current alone does not license dropping a flux or observer term.

Fractal geometry can arise from actual generator words, restrictions, intersections and receiver first-arrivals. For recurrence `Φ` and receiver region `A`, the existing definition is `A₀=A`, `A_(n+1)=Φ⁻¹(A_n)∖A`. The proposal does not presume every Holon is fractal or infer infinite-scale structure from a finite rendering.

## SSM and diffusion as restrictions

With fixed incidence, constitution, geometry, generator and passive receiver, and a linear state law, the object reduces to

```text
x_(k+1) = A x_k + B u_k,
y_k = C x_k + D u_k.
```

`A` is the discretized composition of generator transport and constitutive flux; `B` injects source current; `C,D` are one receiver chart. Eliminating a linear interior may produce a transfer kernel, while the Holon retains the interior or its exact boundary response and reconstruction fibre. Selective/phase-varying SSM coefficients are ordered generator maps with their actual clocks.

A diffusion model chooses an initial Holon and an integration/noise law for its field equation. Its state includes the material and geometry governing flux; its receiver reads the resulting boundary. Diffusion is a state-evolution chart of the Holon, not an engine attached to it.

## Computational signatures

The same typed Holon should own the consuming operations:

```text
advance(H, source, controls, clocks)
    -> (H_next, regional_receipt, interface_flux, energy_balance, residual)
receive(H, receiver)
    -> (face, compatible_source_fibre)
interact(H_left, H_right, shared_contact)
    -> (H_left_next, H_right_next, paired_flux, interface_balance)
restrict(H_fine, grain)
    -> (H_coarse, scale_defect_or_descent_witness)
pullback(H, receiver_covector)
    -> (current, material, generator, contact, receiver covectors).
```

These are proposed operation signatures, not claims that a single Rust type implements them. The complete pullback includes transported current and changing participation, plus contact geometry, clocks, material and receiver.

## Questions for Claude iteration

1. Does the occurrence-bearing `Holon` core extend naturally into this dynamic object while preserving its composition laws?
2. What are the exact spaces and pairings for current, coholon effort, geometry, phase lift, contact rates and active observer current?
3. What connection-valued incidence `d_A` is valid? When does `d_A²=0`, and when must curvature/holonomy be returned as a face?
4. Derive source, contact, boundary and changing-material terms in one finite energy balance. Separate established identities from proposed constitutive choices.
5. Give an active receiver Holon's coupled state equation and prove or refute the interface power law; keep passive coholon reception as a specialization.
6. State the whole-object scale square for current, flux, constitution, generators and receivers. Give a closing example and a counterexample with retained defect.
7. Identify the smallest native consumer that can execute this object through existing resident-field owners.

Recommended first controls: a two-cell diffusive Holon; two coupled Holons with one active receiver; then a phase-carrying ring/contact loop with a coarse restriction. Fixed linear controls must recover the existing Medium and SSM equations. A failure should identify the missing term or noncommuting square.

## Source route

- [The computational Holon and helical pair interaction](../../docs/HOLON.md).
- [HNN state-space, diffusion and operator compositions](../../docs/HNN_FORMULA.md).
- [Covariant storage–flux complex](2026-08-24_THE_HOLONIC_INTERACTION_IS_A_COVARIANT_STORAGE_FLUX_COMPLEX_AND_THE_CUSP_RAISES_DIFFERENCE_ORDER.md).
- [Fractal generators and latent reasoning](2026-09-08_FRACTAL_GENERATORS_AND_LATENT_REASONING.md).
- [Coupled fluid, internal mode and diffusion](../../docs/HOLONIC_FLUID_CONSTRUCTION.md).
- [Occurrence-bearing formal Holon](../../formal/elementary-holonics/ElementaryHolonics/Foundation/Holon.lean).
- [Native covariant interaction medium](../../crates/holonic-engine/src/holonic_interaction.rs).
- [Active construction state](../../CONSTRUCTION_STATE.md).

This proposal becomes library law only after its domains, pairings, joins and consumers are resolved.
