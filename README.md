# Holonics

[project-postulate] **Holonics is a machine-learning framework for Holonic Neural Networks
(HNA), built in Rust with resident CUDA execution and mathematical foundations in Lean.**
The objective is frontier-level usefulness on consumer hardware through efficient, continuous
learning and reusable local structure—the project's “20W ideology”.

**Athena** is a native model/ecology. **Eros** forms and refines it through recurrent operation.
**Soulkiller** dismantles supported pretrained realizations into reusable native material.
Training, inference, model persistence and export belong to one explicit framework lifecycle.

## Start here

- [Architecture and the consumer-hardware objective](docs/ARCHITECTURE.md)
- [Soulkiller: intake, excitation, dismantling and model-family support](docs/SOULKILLER.md)
- [Athena/HNA: training, inference, requests and artifact scopes](docs/ATHENA.md)
- [Interoperability: Safetensors, ONNX and executable model recompilation](docs/INTEROPERABILITY.md)
- [Build and development guide](docs/DEVELOPMENT.md)

## Run the current native interface

```sh
cargo build -p holonics-workbench --bin holonics
target/debug/holonics hna --help
target/debug/holonics hna infer /path/to/supported/model 'Explain holonics briefly.'
target/debug/holonics --format json hna train /path/to/supported/model sequence.json
```

[established-bounded; source-inspected] The current full native path executes the supported
Gemma text realization and restricted Soulkiller bodies on CUDA. The API retains one successor
session across ordered occurrences and can apply developmental returns through previously
learned overlays. `hna infer` returns one selected face; `hna train` returns a developmental
run receipt. It does not yet save a full cultivated-operator checkpoint or claim frontier-level
output quality. The exact scopes and next production bridges are documented above.

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
