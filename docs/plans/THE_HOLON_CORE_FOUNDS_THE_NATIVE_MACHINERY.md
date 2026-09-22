# The Holon core founds the native machinery

[project-postulate] Brandon, September 22: the Holon is the foundational object of the Lean
mathematics and the foundational class of the Rust codebase; every HNN mechanism is built on it,
through a refactor and consolidation. Object: [elementary objects](../ELEMENTARY_OBJECTS.md#the-holon-as-one-object),
[refinement](../../research/records/2026-09-22_THE_HOLON_IS_AN_INTERCONNECTED_PORT_OBJECT_ON_A_COMPLEX.md).
This plan records the facet survey of the native tree and the proposed core, pending approval of the
restructuring phases.

## What already exists (source-inspected survey, September 22)

[established-bounded; source-inspected] `holonic_interaction::HolonicInteraction` already holds most
of a Holon: storage form (`Medium`, `SymmetricForm`), skew interconnection (`Medium.structure`,
`Coupling` — "the port-Hamiltonian interconnection"), resistive contacts (`ContactFace`,
`ContactDissipation`, `HelicalPairInteraction`), a source port (`SourceCurrent`) and a participating
receiver with its own storage and skew structure (`Perspective`, `ReceiverBody`). Missing everywhere:
ports carrying flow–effort pairs, an explicit Dirac type with composition, and a stepping motion on
the law (only linearization/transfer/poles exist). Duplication found: 27 `*Complex` types; five power
readings (`TellegenReceipt`, `StorageRateReading`, `ClockedEnergy`, `PowerStations`,
`DiffusionEnergyBalance`); three clocks (`Clock`, `ClockSpec`, `JointClock`); name collisions
(`GeneratorFamily` ×2, `Generator`, `SiteKind` ×2); ~351 receiver-named public types; two exact
linear-map types (`ExactRatMatrix`, `sheaf_diffusion::ExactLinearMap`). No pump schedule or LC loop
owner exists; the resident parametron is a limb-exact product body without metric phase.

| Facet | Best existing owner |
|---|---|
| Complex `K`, `∂_A` | `GradedCausalComplex` + `HodgeOperator`; connection from generator transports; device `NativeFieldDeclaredIncidence` (CSR + transpose) |
| Ports `Π` | `JointUnits` + `Quantity` for units; port-incidence role of `SourceCurrent`/`Perspective` |
| Interconnection `𝒟` | `HolonicInteraction` skew assembly; `junction_law::tellegen` |
| Element relations `𝓔` | `SymmetricForm`/`Inertia` (storage), `ContactFace`/`ContactDissipation` (resistive), `SourceCurrent` (source), resident normal material (active/learned); pump and LC loop absent |
| Generators `G` | `CompiledGeneratorSite` content: `SituatedScrew`, `RationalPhase`, `Clock`, `Odometer` |
| Receivers | `Perspective`/`ReceiverBody` (active); `receiver_release::Reading` (passive coholon) |
| Restriction `π` | `continuing_tower::{Tower, Transition, Migration}`, `continuing_tube::SquareDefect` |
| Motion | `ExactEventLaw` (event chart); `NativeCoupledBody` (resident) |

## The proposed core

[project-postulate; agent-inferred] A new crate `crates/holonic-core`, depending only on
`relational-geometry` and numeric/serde crates (builds without CUDA), exposed as `holonics::core` and
never glob-re-exported into the engine. Modules mirror the Lean foundation (`ElementaryHolonics/Holon/`):

```text
scalar       Rat reference field; DyadicBall (centre, radius, grain) — generalizes NativeFieldCurrentBall
complex      CellComplex (∂∘∂=0 validated; from GradedCausalComplex); Connection (d_A, curvature face)
port         PortUnits (flow, effort, power dimensions); Port; FlowEffort with power ⟨e,f⟩
dirac        DiracStructure { Kernel(F,E) | Incidence(B) | Skew(J) }; check (isotropic + maximal); compose (closure)
element      ElementRelation { Storage | Resistive | Source | Active{power declared} | Pump{schedule, clock} }; PowerTerm
generator    Generator { transport, initial configuration (the key), Clock, PhaseLift (Cayley phase + winding, carry) }
restriction  Restriction over Transition; Descent { Witness | Defect (retains interior/fibre) }
holon        Holon (the law); HolonState (a point); interconnect(a, b, joined ports) -> Holon
law          HolonLaw { advance, receive, interact, restrict, pullback } with EnergyBalance
             { stored_change, dissipated, port, active, deposition_work, discretization_defect, residual }
conformance  Tellegen; power balance (residual = 0 exactly); interconnection closure; restriction square;
             passive coholon = Reading; lossless winding carry; chart square (reference ∈ resident ball)
```

Reference motion: implicit midpoint for the skew-plus-quadratic part gives an exact discrete balance
(`discretization_defect = 0`); backward Euler reports its defect. The resident CUDA realization is a
chart: `ResidentHolonChart` compiled from a core `Holon` onto the existing CSR/D* layouts and
kernels, owing "exact reference value ∈ returned dyadic ball", not equality. `NativeCoupledBody`
keeps its API and delegates to the chart.

## Phases (each lands with its Lean counterpart or names the #62 obligation)

1. **Lean foundation** — `ElementaryHolonics/Holon/` (in progress).
2. **Core base** — move `ExactRatMatrix`, `SymmetricForm`, `Inertia` (and closure) into `holonic-core`
   with re-exports at old paths; replace `ExactLinearMap`.
3. **Holon from `HolonicInteraction`** — its parts become core facets; `declared` builds a core
   `Holon`; power readings become views of `EnergyBalance`.
4. **Complex consolidation** — `GradedCausalComplex`/`HodgeOperator` supply `K`; diffusion/current/
   resistive complexes become constructors; diffusion laws implement `HolonLaw`.
5. **Generators** — one `Clock` (`ClockSpec` its wire); `CompiledGeneratorSite` → core `Generator`;
   collisions renamed with aliases.
6. **Restriction** — tower/tube types move to `core::restriction`; grain/coarsening towers and
   `StandingLaw` become instances.
7. **Receivers** — `Reading` is the passive coholon; `Perspective`/`ReceiverBody` active receivers;
   normalized/pair receivers are active elements with their power term.
8. **Device chart and retention** — `ResidentHolonChart`; `NativeCoupledBody` delegates; the
   remaining history structures retire under the retention law; unconsumed body states are charted or
   retired after a consumer audit.

Constraints: rest/wire compatibility for `SavedCoupledBody`, `NativeIncidentModelRest`,
`CoupledConstitutiveRest`, the complex schema string and custom deserializers; interaction types stay
`Serialize`-only so no wire mints an unchecked object; no device layout change during consolidation;
public names kept; the Lean citation scan extended to `holonic-core`.
