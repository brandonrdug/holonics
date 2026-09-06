# Holonics

[project-postulate] **Holonics is a mathematical framework and ontology for situated objects,
causal composition, information transport and physical realization.** Its central mathematical
object is the holon: an addressed occurrence population with source and target ports, a receiver,
and the full fibre behind its returned face. The framework develops reusable ways to construct,
explain and compute with mathematical, physical, biological and learning systems.

[definition] **HNA** is the Holonic Neural Network architecture within Holonics, implemented in
Rust with resident CUDA execution. Its product objective is frontier-level usefulness on consumer
hardware through efficient, continuous learning and reusable local structure—the project's
“20W ideology”. Lean carries formal mathematical constructions across the framework.

**Athena** is a native model/ecology. **Eros** forms and refines it through recurrent operation.
**Soulkiller** dismantles supported pretrained realizations into reusable native material.
Training, inference, model persistence and export belong to one explicit framework lifecycle.

## Start here

- [Mathematical framework and executable architectures](docs/ARCHITECTURE.md)
- [The mathematics tablet](docs/canon/THE_MATHEMATICS_TABLET.md)
- [Moving frames, singularities and the RH research strategy](docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md)
- [Soulkiller: intake, excitation, dismantling and model-family support](docs/SOULKILLER.md)
- [Athena/HNA: training, inference, requests and artifact scopes](docs/ATHENA.md)
- [Native HNA: live current sessions and the independent application](docs/NATIVE_HNA.md)
- [Interoperability: Safetensors, ONNX and executable model recompilation](docs/INTEROPERABILITY.md)
- [Build and development guide](docs/DEVELOPMENT.md)

## Run the current native interface

[project-postulate] Current construction prioritizes **native HNA foundations and contextual
transport**, before further Soulkiller/Gemma-led production. See the
[contextual audit](research/records/2026-09-05_CONTEXTUAL_TRANSPORT_PRECEDES_INHERITED_MODEL_PRODUCTION.md).

```sh
cargo build -p holonics-workbench --bin holonics
target/debug/holonics hna --help
target/debug/holonics hna native-session applications/holonics-workbench/examples/native/phase-seed.json --input applications/holonics-workbench/examples/native/current-requests.jsonl --checkpoint .local/artifacts/native-example.hna
target/debug/holonics hna wave-control applications/holonics-workbench/examples/native/wave-control.json --format json
```

[established-bounded; measured] The ground-up phase ecology now has a public Rust/JSONL interface
and an independent current-compensation application. Actual local development changes later
receiver conduct, with explicit outside-domain/plural readings, live recharting and owned source
handles. The [native guide](docs/NATIVE_HNA.md) states the local rational-linear family and recipes.
Native checkpoints preserve the whole phase ecology and stream, with source/frame history and
outstanding handles. Integrated application/world continuation and resource evidence remain NCF4.
This is not a language model or a general-context capability claim.

[established-bounded; source-inspected] The earlier full-operator path executes the supported
Gemma text realization and restricted Soulkiller bodies on CUDA. The API retains one successor
session across ordered occurrences and can apply developmental returns through previously
learned overlays. `hna infer` returns one selected face; `hna train` returns a developmental
run receipt. Full checkpoints, backpressured sessions and paired text/model continuation are
available through `HnaModel`, `HnaTextApplication` and `hna session` at their declared scopes.
Their storage and numerical results do not establish contextual learning or frontier-level
quality. The tied-head experiment is archived, not the current foundation route.

For Rust clients, `crates/holonics` exposes `holonics::hna`, `holonics::soulkiller` and
`holonics::interop`. Existing Safetensors/ONNX package exports preserve Holonics artifacts;
compilation into standard executable model architectures has its own [contract](docs/INTEROPERABILITY.md).

## Repository map

| Directory | Purpose |
|---|---|
| [crates](crates/README.md) | Live Rust libraries and public framework API |
| [applications](applications) | CLI/workspace and standalone research tools |
| [accelerators](accelerators/README.md) | Independent device-only targets |
| [formal](formal/README.md) | Live Lean projects |
| [docs](docs/ARCHITECTURE.md) | Architecture, interfaces, doctrine, active plans and navigation |
| [research](research/README.md) | Dated evidence, experiments, papers and notebooks |
| [archive](archive/README.md) | Completed plans and frozen historical bodies |
| [tools](tools/README.md) | Optional helpers used for relevant work |

[definition] [CONSTRUCTION_STATE.md](CONSTRUCTION_STATE.md) records the current position;
[the roadmap](docs/plans/THE_ROADMAP.md) orders construction. [AGENTS.md](AGENTS.md) is the
shared agent contract. History and retired plans do not silently schedule new work.

Use the [owner map](docs/ARCHITECTURE_MAP.md) for Lean–Rust–CUDA relations, the
subject guides and Provenance for research navigation, and the
[repository/recovery guide](docs/REPOSITORY.md) for relocated paths and backups.
