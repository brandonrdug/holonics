# The Holon is an interconnected port object on a complex

**Tree:** `854c99be` plus the uncommitted campaign-1 work. **Request:** Brandon, September 22:
analyze and refine the [Luna proposal](2026-09-22_PROPOSAL_THE_HOLON_AS_A_RECURSIVE_GENERATOR_FLUX_OBSERVER_OBJECT.md)
so the Holon becomes the formal basis of the Lean mathematics and the foundational class of the Rust
machinery, leading to a refactor and consolidation. This record gives the refinement, answers the
proposal's seven questions, and states the foundation campaign.

## What the proposal gets right, and what it bundles

[established-bounded; source-inspected] The proposal correctly puts current, constitution,
generators, contacts, frames, receivers and scale restriction under one incidence and one transport
law, and it correctly asks that flux and observation be equations of the object, not operations
around a payload. It also names the right existing owners: `Foundation/Holon.lean` (occurrence core,
serial/Cartesian composition, preimage fibres), `holonic_interaction::Medium`
(`q̇=(Ω−M_contact)Gq+Bu`), the diffusion laws, the fluid construction and the scale owners.

[definition; agent-inferred] Three refinements are needed before it can be a foundation:

1. **Separate the Holon from its state.** The tuple places the evolving section `Ψ_ℓ(τ)` inside the
   object. Brandon's ruling is that a Holon is continuing potential, already present, never produced.
   So the Holon is the *law and its ports* — incidence, interconnection, constitution, generators,
   interfaces and restrictions. A state is a point on it; a trajectory is one of its admitted motions.
2. **Receivers are Holons at ports, not a field inside.** The tuple carries a receiver family
   `R_ℓ`. Observation is interconnection: a receiver is another Holon joined at a shared port. A passive
   coholon is the specialization with no storage and no power draw, which reads an effort. Then
   "a Holon of Holons is a Holon" becomes a theorem about interconnection, which is the recursion the
   proposal wants (whole and part at once).
3. **Do not force a gradient or Hamiltonian form.** The repository already records that a learned
   reaction or nonlocal attention field need not be a gradient flow (`docs/HNN_FORMULA.md`,
   port-Hamiltonian paragraph). The foundation must therefore split every Holon into a
   power-conserving interconnection plus element relations that may be storing, dissipating,
   sourcing or active, with the energy balance computed from them and passivity proved where it holds —
   never assumed.

## The refined object

[definition; agent-inferred] **A Holon** is

```text
H = (K, ∂_A;  Π;  𝒟;  𝓔;  G;  π)
```

- `K`, `∂_A` — an oriented complex with typed fibres and a connection-valued incidence `d_A`
  (covariant difference using the generators' frame transports `U_e`); `∂_A` its adjoint.
- `Π` — **ports**: interface cells where the Holon meets others, each carrying a flow `f` and an
  effort `e` with their pairing `⟨e,f⟩`, which is power (W). Information ports pair entropy rate with
  temperature, so a cross-entropy current is a literal port flux.
- `𝒟` — the **interconnection (Dirac) structure**: a subspace of flows × efforts equal to its own
  orthogonal under `⟨⟨(f₁,e₁),(f₂,e₂)⟩⟩=⟨e₁,f₂⟩+⟨e₂,f₁⟩`. It encodes incidence and its adjoint
  (Stokes), the skew generator transport, and port incidence. Its defining property is power
  neutrality, `⟨e,f⟩=0` on `𝒟`, which is Tellegen.
- `𝓔` — the **element relations**, i.e. the constitution: storage `E_Θ` with effort `μ=D E_Θ`
  (capacitive `C`, inverse-inductive `K`), resistive relations (contact mobility `M`, slip dissipation
  `JᵀDJ`, `⪰0` where passive), sources, active or learned relations (explicit, with their power term),
  and time-varying pumps.
- `G` — **generators** with initial configurations, clocks and phase lifts `θ̃=θ+2πn`; they supply
  `U_e` and the skew part of `𝒟`; a section crossing is a lossless jump that carries winding.
- `π` — **restrictions** to coarser grains, as maps of the whole object.

A **motion** is a trajectory whose flows and efforts lie in `𝒟` and satisfy `𝓔`. The balance follows:

```text
d/dτ E_Θ = −(dissipated power) + (port power) + (active power) + ⟨∂_Θ E, Θ̇⟩
```

where the last term is deposition work when the constitution changes. Deposition `Θ̇` is the slow
law of the element relations, driven only by covectors that reached the locus.

## How the library objects become facets of one object

| Library object | Facet of the Holon |
|---|---|
| Complex | `K`, `∂_A` |
| Holon and coholon | flows and efforts; the pairing is power; Stokes is the adjointness of `d_A` and `∂_A` inside `𝒟` |
| Constitution | `𝓔` |
| Generator | `G`, supplying `U_e`, skew transport, clocks and phase lifts |
| Pair contact | a resistive element on relative slip, `f=Jv`, `e=−Df` |
| Parametron | a lossless storage loop (`C`, `K`) with a time-varying pump; the perceptron is its locked-sheet receiver face |
| Tube and tower | `π` and the longitudinal composition of Holons along ports |
| Relative completeness | interior states not determined by port trajectories but coupled through them, with persistent motion |
| Deposition | `Θ̇` |
| Ratio | the relative transport between two Holons read at ports; loss `log R` |
| Receipt | port powers, energy balance terms and local readings per region |
| Keys | the generators' initial configuration and gauge; Bombe loop closure is the cycle (Kirchhoff loop) constraint of `𝒟` |

Standard specializations: a linear SSM is a discretized linear port system with fixed constitution
and a passive receiver; diffusion is the purely resistive case (gradient flow of `E_Θ`); Maxwell is the
Stokes–Dirac structure on the de Rham complex; incompressible Euler is a Lie–Poisson skew structure
and Navier–Stokes adds viscous resistance. `Foundation/Holon.lean`'s occurrence Holon is the event
chart: an occurrence is a port event, and `Holon.comp`'s joining occurrence is port identification.

## Answers to the proposal's questions

1. **Occurrence core.** It extends as the event chart of the port object: each occurrence carries a
   flow–effort pair at its ports, and serial composition through a joining occurrence is port
   interconnection. The composition laws are preserved if interconnection of Dirac structures is closed,
   which is standard in finite dimension.
2. **Spaces and pairings.** Flows are chains (currents, rates, slip, entropy rate); efforts are
   cochains (potentials, forces, temperature). Geometry and phase lifts are generator state; contact rates
   are flows on contact cells; an active observer's current is the flow at its port.
3. **`d_A`.** Any connection gives a power-neutral Stokes–Dirac structure, because neutrality uses only
   the adjoint pair. `d_A² = F_A`; exactness, potentials and cohomology need `F_A = 0`. Otherwise curvature
   is returned as a cell face (`CellHolonomy`).
4. **Energy balance.** The balance displayed above. Tellegen and interconnection are established
   identities; storage, resistive and active relations are constitutive choices; deposition work is its
   own term.
5. **Active receiver.** Interconnecting two Holons through an interface resistive element gives
   `P_(H→R)+P_(R→H)=−D_Σ` with `D_Σ≥0` when that element is passive. A passive coholon is the zero-storage,
   zero-power limit that reads an effort.
6. **Scale square.** `π∘T_fine = T_coarse∘π` on flows, efforts, constitution, clocks and ports; static
   interior elimination (Kron/Schur, `Λ_DN`) closes exactly; dynamic reduction returns a typed defect.
7. **Smallest native consumer.** `holonic_interaction::Medium` already implements the linear port form.
   The generator machine's rings and contacts are the next consumer.

## The foundation campaign

[project-postulate] This precedes the ring, key and motor campaigns, which will be built on it:

1. **Lean.** A finite-dimensional linear Dirac structure and port Holon over an ordered field:
   power neutrality, the energy balance with storage, resistive, active and deposition terms,
   closure of interconnection (a Holon of Holons is a Holon), passive-coholon specialization, active
   receiver interface law, connection-valued incidence with curvature face, lossless clock jump with
   winding, restriction and its square with Kron/Schur closing and a defect witness, and instances:
   `HolonicInteraction.Medium`, a linear SSM, diffusion, the parametron LC loop with a pump, the pair
   contact as a resistive element.
2. **Rust.** A core module whose types are the Holon's facets (ports, interconnection, element
   relations, generators, restriction) with an exact reference implementation, the five signatures
   (`advance`, `receive`, `interact`, `restrict`, `pullback`), and conformance tests (power balance,
   interconnection closure, restriction square). Existing carriers become implementations of it.
3. **Consolidation.** Every native owner either implements the core or is shown to be a chart of
   one that does; duplicated carriers are removed.

This record is the refinement; the governing definition is in the
[elementary objects](../../docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object).
