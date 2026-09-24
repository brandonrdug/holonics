# Holonics

Holonics is a theory of everything grounded in the reality of difference: a mathematical,
physical and computational framework for how situated things exist, interact, change and become
observable. Its elementary object is the **Holon**: a law with incidence, ports, material
relations, navigators and scale restrictions. Holons join at ports into Holarchies, receivers read
situated faces, and time passes in aeons, epochs and cycles. **HNN** is the neural machinery built
from these objects: chains of complex parametron rings joined by helical pair contacts
([the machine](docs/THE_MACHINE.md)). Compression is intelligence is navigation: Holonic
Compression and landmark discovery, executed at scale by the HNN, are the line the repository
builds.

The repository was reset on September 24, 2026 to what functions, and it is being rebuilt from the
elementary objects ([plan](docs/plans/THE_REBUILD.md), [state](CONSTRUCTION_STATE.md)).

| Path | Contents |
|---|---|
| [`crates/holonics`](crates/holonics) | The main Rust library: the Holon law, ratio and ring arithmetic, geometry, receivers |
| [`crates/holonics-cuda`](crates/holonics-cuda) | The CUDA backend (currently the device driver) |
| [`accelerators/`](accelerators) | Device-only builds excluded from the host workspace (the driver smoke kernel) |
| [`lean/`](lean) | The Lean mathematics (`Holonics.Framework` and the research umbrella) |
| [`docs/`](docs) | [The machine](docs/THE_MACHINE.md), the [elementary objects](docs/ELEMENTARY_OBJECTS.md), [the Holon](docs/HOLON.md), the [HNN formula](docs/HNN_FORMULA.md), [notation](docs/HOLONIC_NOTATION.md) and the mathematics guides |
| [`research/`](research) | Dated research records, papers and design notes |

Build: `cargo check --workspace --all-targets`; Lean: `bash tools/lean_check.sh`. Contributor
guides: [CLAUDE.md](CLAUDE.md) and [AGENTS.md](AGENTS.md).

Holonics is dual-licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.
