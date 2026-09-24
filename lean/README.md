# Holonics in Lean

[definition] This project develops Holonics as a reusable mathematics of situated objects,
interaction, transport and receiver-relative description. Lean holds the mathematics; Rust holds
what runs. Begin with the framework, then follow a physical, computational or target-specific
realization. The [framework guide](../docs/FORMAL_FRAMEWORK.md) explains the connections, and the
[elementary objects](../docs/ELEMENTARY_OBJECTS.md) own the vocabulary.

[definition] The Lake package is `soma_elementary_holonics`, with one library `ElementaryHolonics`
and the default target `ElementaryHolonics.Framework`. Declarations live under the namespace
`Soma.Holonics`. Rebuild step 1 (#70) renames the package to `holonics`, splits the library into
`Holonics` (the `Framework` closure) and `HolonicsResearch` (the rest), and moves the namespace to
`Holonics`. Module names such as `Holon/Generator` and `Foundation/GeneratorInference` keep their
spelling until step 7 renames the navigator owners.

## Import by mathematical subject

```lean
import ElementaryHolonics.Framework
```

[definition] Narrower entry points expose the same owners without importing the research umbrella.
They add no axioms or alternative definitions.

| Import under `ElementaryHolonics.Framework` | Read it for |
|---|---|
| `HolonObject` | The Holon as one object: `Holon/{Port,Dirac,Complex,Element,Generator,Restriction,Law,Conformance,Deposition,Reaction,Cayley}` |
| `Objects` | The elementary objects' proved joins: `Objects/{Pairing,Deposition,Ratio,Parametron,RelativeCompleteness,…}` |
| `Core` | Occurrences, holons, addressed interaction, receiver fibres, standing and release, natural charts and ordered transport |
| `Geometry` | Orientation, constraints, lattices, screws, phase carry, pair resonance, recursive scale and curvature |
| `Dynamics` | Local clocks, world tubes, the helical pair interaction, serial screw chains, cell holonomy, source moments and changing constitution |
| `Information` | Normalization, complete receiver families, navigator inference, entropy/action and future-exact compression |
| `Physics` | Coupled incidence, phase carriers, membranes, quantum/crystal evolution and spacetime receivers |
| `Computation` | Execution, recurrent ecologies, classical learning charts and morphology continuation |

[definition] These are overlapping mathematical subjects, not layers of a machine. A molecular
conformation, an electrical circuit and an HNN can use the same coupled incidence algebra while
keeping different constitutive laws and physical evidence.

## The elementary spine

[definition] `Foundation/Holon.lean` starts with an occurrence population, oriented source and
target ports, and a receiver. `Holon.Interaction` is an actual pullback join. Serial composition
keeps both occurrences and their joining equality; its Preimage Fibre keeps compatible causes.
`BoundaryHolon` adds an explicit boundary law; `CausalNaturalHolon` transports the whole diagram
through admitted parameter changes. The port Holon `H=(K,∂_A; Π; 𝒟; 𝓔; G; π)` is
`Framework.HolonObject`.

[definition] `Foundation/TransportWord.lean` keeps ordered transport words;
`Foundation/ReceiverHistoryCompression.lean` extends receiver factorization through every admitted
finite word; `Foundation/CompleteReceiverHistory.lean` adds completeness, identifying quotient
equality with equality of all declared receiver/history faces and returning a separating history
when quotients differ (its declarations keep the `Soma.Holonics.Millennium.ReceiverHistory`
namespace). Commutation can make an endpoint insensitive to order without erasing the carrying
occurrences. Neither a number nor a theorem's printed name is a Holon's identity.

[definition] `Transport/AddressedLinearizedPassage.lean` owns the linearized differential on an
addressed passage, its pullback-joined two-step composition, reverse-order adjoint, receiver
radical and complete preimage fibres; `Millennium/SituatedReturnedDifference.lean` keeps the
dependent connection-square return. `Transport/ChangingReceiver`, with its mechanical and
nonlinear-fluid instances `Physics/MechanicalReceiver` and `Physics/FluidReceiverClosure`, joins
changing constitutive geometry, receiver scales and retained feedback in one difference calculus
([guide](../docs/FORMAL_FRAMEWORK.md#changing-constitution-and-changing-grain-are-one-returned-comparison)).
[`Physics/ConstitutiveModulation`](ElementaryHolonics/Physics/ConstitutiveModulation.lean) connects
changing conformation and internal current to the complete coupled response.

## Targets and proof scope

[definition] `ElementaryHolonics.lean` is the complete research import face: `Framework` plus the
`RH/`, `Mathematics/`, `Millennium/` and `Computation/` owners of the targets (RH, Hodge, complex
Euler/Navier–Stokes, BSD). The targets are instances of Holonic Compression and landmark
discovery ([the line](../docs/plans/THE_REBUILD.md#the-line-the-rebuild-serves)), not a separate
category; step 7 renames the directories named after the prize by subject. Author and conjecture
names stay as source attribution and statement coordinates. The
[catalogue](MILLENNIUM_FORMAL_CATALOG.md) is historical scope testimony; order and position
belong to [THE_REBUILD](../docs/plans/THE_REBUILD.md) and [CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md).

[definition] Lean's exact `ℝ` and `ℂ`, classical mathematics and Mathlib are admitted
mathematical charts, not device floats. Physical interpretation still needs units, constitutive
laws, boundaries and calibrated receivers. Kernel acceptance proves the stated theorem under its
assumptions; it supplies neither a molecular experiment nor a trained Athena. Lean is exterior
verification and never enters the HNN.

## Verify

```sh
# From the repository root: the framework (the pinned Lake default).
bash tools/lean_check.sh

# A subject or one changed owner.
bash tools/lean_check.sh ElementaryHolonics.Framework.Geometry
bash tools/lean_check.sh ElementaryHolonics.Physics.ConstitutiveModulation

# The complete research import face, when a change reaches that scope.
bash tools/lean_check.sh ElementaryHolonics
```

[definition] `tools/lean_check.sh` is the only entry point. It builds from source with this
project's [toolchain](lean-toolchain) and [dependency manifest](lake-manifest.json), never updates
versions, and fails on any declaration elaborated with `sorry`. `.lake/` caches are kept. Mathlib
and Cslib are pinned to v4.33.0; Physlib is pinned by revision in [lakefile.toml](lakefile.toml).
The executables `m6_lean_causal_return` and `derivation_atlas` are declared there too.
