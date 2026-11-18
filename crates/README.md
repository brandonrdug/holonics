# Rust libraries

[definition] The host workspace has three crates. Lean holds the mathematics; Rust holds what
runs. Start with [THE_ENGINE](../docs/THE_ENGINE.md), the engine's guide (its pipeline phase by
phase, its declaration, its saved state and its commands), then [the machine](../docs/THE_MACHINE.md) and the
[elementary objects](../docs/ELEMENTARY_OBJECTS.md#operator-contract), whose operator contract
lists each object's owners and the engine's module for it. The device-only builds of `accelerators/` retired with
the October card crate (C8 of #603; held at [`d6bbd1644`](https://github.com/brandonrdug/holonics/tree/d6bbd1644/accelerators)).

| Library | Responsibility |
|---|---|
| `holonics-engine` (`engine/`) | The engine: the field's law and its host reference, cut by object, with the codec, the region and the passage. |
| `holonics-engine-cuda` (`engine-cuda/`) | The engine's card realization: the driver, the card and the field's resident realization with its kernels. |
| `athena` (`athena/`) | The commands, binary `athena`: the store line's trainer, writer, state tools and pass boundary (`store`), the world that answers an act (`world`), its readings (`ruler`), the card's parity against the host (`parity`) and the exterior's reads and writes (`exterior`). It depends on the engine crates alone; [THE_ENGINE §7](../docs/THE_ENGINE.md#7-the-commands) lists its words. |

[definition] [THE_REBUILD](../docs/plans/THE_REBUILD.md) orders the work: its eight steps, with the campaign under way in its §3 and the position in [CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md). The unified plan U0 to U8 that this file named until November 18 is that plan as it stood to November 7, at [`0a051ae5`](https://github.com/brandonrdug/holonics/blob/0a051ae5/docs/plans/THE_REBUILD.md). The October library `holonics` retired with C8c of #603, held at [`d5ed4adc1`](https://github.com/brandonrdug/holonics/tree/d5ed4adc1/crates/holonics), and its card crate `holonics-cuda` with C8a, held at [`d6bbd1644`](https://github.com/brandonrdug/holonics/tree/d6bbd1644/crates/holonics-cuda). The retired engine, the HNN prototype and the applications are in history at [`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734); the owners retired on September 28 are at [`2d34b819`](https://github.com/brandonrdug/holonics/tree/2d34b819). A law, a part or a whole configuration is ported from history when a step needs it, and is tested by the law it implements ([CLAUDE.md](../CLAUDE.md#past-configurations)).

Check: `cargo check --workspace --all-targets`.
