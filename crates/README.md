# Rust libraries

[definition] The host workspace has three crates. Lean holds the mathematics; Rust holds what
runs. Start with [the machine](../docs/THE_MACHINE.md) and the
[elementary objects](../docs/ELEMENTARY_OBJECTS.md#operator-contract), whose operator contract
lists each object's current and target owners. The device-only builds of `accelerators/` retired with
the October card crate (C8 of #603; held at [`d6bbd1644`](https://github.com/brandonrdug/holonics/tree/d6bbd1644/accelerators)).

| Library | Responsibility |
|---|---|
| `holonics-engine` (`engine/`) | The engine: the field's law and its host reference, cut by object, with the codec, the region and the passage. |
| `holonics-engine-cuda` (`engine-cuda/`) | The engine's card realization: the driver, the card and the field's resident realization with its kernels. |
| `athena` | The commands, binary `athena`: the store line's trainer, writer, lane founding and pass boundary, its live reading, and the card's parity against the host. It depends on the engine crates alone. |

[definition] [THE_REBUILD](../docs/plans/THE_REBUILD.md) orders the work (its unified plan, U0–U8); the October library `holonics` retired with C8c of #603, held at [`d5ed4adc1`](https://github.com/brandonrdug/holonics/tree/d5ed4adc1/crates/holonics). The retired engine, the HNN prototype and the applications are in history at [`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734); the owners retired on September 28 are at [`2d34b819`](https://github.com/brandonrdug/holonics/tree/2d34b819). A law is ported from history one owner at a time and tested by the law it implements.

Check: `cargo check --workspace --all-targets`.
