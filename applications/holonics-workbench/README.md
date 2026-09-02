# Holonics Workbench

Holonics Workbench is the operator application for the live Rust body. The `holonics` executable
offers a stateless CLI and a long-lived Ratatui terminal UI over the same typed command/event
runtime.

It does not implement engine behavior. Athena, Eros, Soulkiller, exact diffusion, package storage,
CUDA conduct, and ONNX/Safetensors export remain owned by their existing libraries.

## Build and run

From the repository root:

```bash
cargo build -p holonics-workbench
./target/debug/holonics --help
```

Open the terminal UI:

```bash
./target/debug/holonics
```

or:

```bash
./target/debug/holonics tui
```

Ratatui uses an alternate terminal screen and restores the terminal when the application exits.
Press `q` outside the command editor to exit.

## TUI controls

- `:` — clear and focus the command palette.
- `Enter` — execute the typed command.
- `Esc` — leave the editor without executing.
- `Tab` — move between command catalogue, event timeline, and inspector.
- `Up` / `Down` — move within the active pane.
- `Enter` on the catalogue — copy that command template into the palette.
- `q` — exit when the palette is not editing.

The center pane is an append-only causal event timeline. The right pane shows the selected event's
structured payload. It is a cold inspector and cannot change native routing.

## First Athena session

Enter these commands in one TUI process:

```text
athena demo-open alpha
athena inspect alpha
athena conduct alpha spool/inherited-excitation-windings thread/excitation-1 1 7
athena continue alpha 0
athena return alpha 100 200 1 1/2 1
athena inspect alpha
athena diffuse-demo alpha 200 1
athena snapshot alpha /your/explicit/path/alpha.snapshot.json
athena export alpha safetensors /your/explicit/path/alpha.safetensors
```

`demo-open` is deliberately named: it creates three bounded BF16 excitation occurrences and passes
them through the real Soulkiller boundary. It does not execute a foreign model or establish
qualitative language capability.

The `return` coordinates are:

```text
session returned-occurrence emitting-boundary real imaginary storage
```

Integers and exact fractions such as `-3/2` are accepted. The returned occurrence must be genuinely
later than the emission.

`diffuse-demo` declares unit capacity and unit conductance over the package's first native spool.
It is an explicit convenience experiment, not a derived physical calibration.

Snapshots and exports are written only to the path you provide. Paths are carriage, not model
identity.

## CLI

The CLI executes one command and exits. It is best suited to inspection and material operations:

```bash
holonics status
holonics capabilities
holonics --json status

holonics eros mouth research/records --extension md --radius 3 --scales 2
holonics eros atlas applications/holonics-workbench --extension rs

holonics soulkiller config /path/to/config.json
holonics soulkiller index /path/to/model.safetensors.index.json
holonics soulkiller onnx /path/to/model.onnx

holonics engine package /path/to/package-or-snapshot.json
holonics engine export /path/to/snapshot.json onnx /path/to/export.onnx
```

Use the TUI for multi-step in-memory Athena interaction. Across separate processes, use explicit
snapshot paths.

`--json` emits one JSON object per `WorkbenchEvent`, suitable for scripts and later graphical
clients. Human and JSON output are projections of the same event population.

## Command families

### Athena

- `demo-open`, `open`, `inspect`
- `conduct`, `continue`
- `return`, `decline`
- `diffuse-demo`
- `snapshot`, `export`

### Eros

- `mouth` — exposure-driven codec ladder.
- `atlas` — source-material incidence, rank gauge, face quotient, and separators.

### Soulkiller

- `config` — lossless root-field inspection.
- `index` — tensor/shard declaration inspection.
- `onnx` — lossless model graph/operator inspection.

These are cold inspection commands and never execute the foreign realization.

### Engine

- `status` — actual CPU parallelism and CUDA apparatus testimony.
- `capabilities` — callable Workbench surface and explicit open fibres.
- `package` — derived native anatomy, lineage, receivers, and realization manifest.
- `export` — exact rested-inference ONNX or Safetensors export.

## Consumer hardware expectations

The current machine is an RTX 4080 SUPER with 16 GiB VRAM and a 12-core/24-thread Ryzen 9 7900X.
Native successor conduct mounts its invariant table and word on CUDA. The exact diffusion demo uses
CPU arbitrary-precision rational elimination and is intended for small or sparse experimental
complexes.

The first build can take several minutes and create a large Cargo `target/` tree. That is compiler
material, not Athena runtime storage.

## Capability boundary

Established here:

- exact operator control over dynamic Athena generations;
- live GPU native conduct;
- local return/commit and decline;
- snapshot/remount, diffusion, and exact export;
- Eros material inspection;
- Soulkiller foreign-chart inspection;
- shared CLI/TUI structured events.

Still open:

- unrestricted Soulkiller dismantling directly from arbitrary model directories;
- useful qualitative text/image/audio generation;
- general plugin discovery over every engine owner;
- distributed multi-instance ecology control.

The Workbench reports these as open rather than simulating them.
