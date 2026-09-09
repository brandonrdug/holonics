# Holonics in Lean

[definition] This library develops Holonics as a reusable mathematics of situated objects,
interaction, transport and receiver-relative description. Begin with the framework, then follow
a physical, computational or problem-specific realization. The
[framework guide](../../docs/FORMAL_FRAMEWORK.md) explains the connections, including molecular
conformation, neural tubes, phase modulation and cosmological receivers.

## Import by mathematical subject

```lean
import ElementaryHolonics.Framework
```

[definition] Narrower entry points expose the same owners without importing the entire research
station. They add no axioms or alternative definitions.

| Import under `ElementaryHolonics.Framework` | Read it for |
|---|---|
| `Core` | Occurrences, holons, addressed interaction, receiver fibres, natural charts and ordered transport |
| `Geometry` | Orientation, constraints, lattices, higher differences, recursive scale and curvature |
| `Dynamics` | Local clocks, world-tubes, finite returns, differential boundaries and changing constitution |
| `Information` | Normalization, complete receiver families, entropy/action and future-exact compression |
| `Physics` | Coupled incidence, phase carriers, membranes, quantum/crystal evolution and spacetime receivers |
| `Computation` | Execution, recurrent ecologies, classical learning charts and morphology continuation |

[definition] These are overlapping mathematical subjects, not independent layers of a machine.
For example, a molecular conformation, electrical circuit and HNN can use the same coupled
incidence algebra, while retaining different constitutive laws and physical evidence.

## The elementary spine

[definition] `Foundation/Holon.lean` starts with an occurrence population, oriented source and
target ports, and a receiver. `Holon.Interaction` is an actual pullback join. Serial composition
retains both occurrences and their joining equality; its Preimage Fibre retains compatible
causes. `BoundaryHolon` adds an explicit boundary law. `CausalNaturalHolon` transports the whole
diagram through admitted parameter changes.

[definition] `Foundation/TransportWord.lean` keeps ordered generators;
`Foundation/ReceiverHistoryCompression.lean` extends receiver factorization through every
admitted finite word. Commutation can make an endpoint insensitive to order. It does not erase
the carrying occurrences. Neither a number nor a theorem's printed name is a holon's identity.

[definition] `Transport/WorldTube.lean`, `Physics/PhaseCarrier.lean` and
`Physics/CoupledIncidence.lean` now own reusable implementations previously housed under
`Millennium/`. Historical modules forward imports and declaration namespaces remain compatible.
The [new finite modulation theorem](ElementaryHolonics/Physics/ConstitutiveModulation.lean)
connects changing conformation and internal current to the complete coupled response.

[definition] The [continuing unification](../../docs/FORMAL_FRAMEWORK.md#changing-constitution-and-changing-grain-are-one-returned-comparison)
adds `Transport/ChangingReceiver`, with mechanical and actual nonlinear-fluid instances in
`Physics/MechanicalReceiver` and `Physics/FluidReceiverClosure`. They connect changing
constitutive geometry, receiver scales and retained feedback through one difference calculus.

[definition] The [comprehensive programme](../../docs/plans/THE_REALITY_OF_DIFFERENCE_IN_CONSTRUCTION.md)
now uses `Transport/ReceiverPotential`, `Foundation/JointReceiverDescent` and
`Geometry/SwingPotential` through the framework subjects. The first use connects exact future
faces with plural mechanical sources and the formal `Computation/JointReceiverWitness`.

## Applications and proof scope

[definition] `ElementaryHolonics.lean` is the complete research import face, including `Framework`
and the retained `RH/`, `Mathematics/` and `Millennium/` applications. Author and conjecture names
remain useful source attribution and statement coordinates; they do not define the framework's
conceptual organization. The [August 28 catalogue](MILLENNIUM_FORMAL_CATALOG.md) is historical
scope testimony. Current research position and order belong to
[CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md) and [the roadmap](../../docs/plans/THE_ROADMAP.md).

[definition] Lean's exact `ℝ` and `ℂ`, classical mathematics and Mathlib are admitted mathematical
charts. They are not device floats. Physical interpretation still requires units, constitutive
laws, boundaries and calibrated receivers. Kernel acceptance proves the stated theorem under
its assumptions; it supplies neither a molecular experiment nor a useful trained Athena.
Lean is exterior verification and does not enter HNN cultivation or inference.

## Verify the intended surface

```sh
# From the repository root: framework (also the pinned Lake default).
bash tools/lean_check.sh

# A subject or one changed owner.
bash tools/lean_check.sh ElementaryHolonics.Framework.Geometry
bash tools/lean_check.sh ElementaryHolonics.Physics.ConstitutiveModulation

# The complete research import face, when the change reaches that scope.
bash tools/lean_check.sh ElementaryHolonics
```

[definition] `./check.sh` forwards to the same checker. Verification uses this project's
[toolchain](lean-toolchain) and [dependency manifest](lake-manifest.json); it does not update
versions or borrow a predecessor environment. `.lake/` caches are retained. Mathlib and Cslib
are pinned to v4.33.0; Physlib is pinned by revision in [lakefile.toml](lakefile.toml).
