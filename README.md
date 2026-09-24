# Holonics

Holonics is a theory of everything grounded in the reality of difference: a mathematical,
physical and computational framework for how situated things exist, interact, change and become
observable. Its elementary object is the **Holon**: a law with incidence, ports, material
relations, generators and scale restrictions. Holons join at ports into Holarchies, receivers read
situated faces, and time passes in aeons, epochs and cycles. **HNN** is the neural machinery built
from these objects.

The repository was reset on September 24, 2026 to what functions, and it is being rebuilt from the
elementary objects ([plan](docs/plans/THE_REBUILD.md), [state](CONSTRUCTION_STATE.md)).

| Path | Contents |
|---|---|
| [`crates/holonics`](crates/holonics) | The main Rust library: the Holon law, ratio and ring arithmetic, geometry, receivers |
| [`crates/holonics-cuda`](crates/holonics-cuda) | The CUDA backend (currently the device driver) |
| [`lean/`](lean) | The Lean mathematics (`ElementaryHolonics.Framework` and the research umbrella) |
| [`docs/`](docs) | The [elementary objects](docs/ELEMENTARY_OBJECTS.md), [the Holon](docs/HOLON.md), [notation](docs/HOLONIC_NOTATION.md) and the mathematics guides |
| [`research/`](research) | Dated research records, papers and design notes |

Build: `cargo check --workspace --all-targets`; Lean: `bash tools/lean_check.sh`. Contributor
guides: [CLAUDE.md](CLAUDE.md) and [AGENTS.md](AGENTS.md).

Holonics is dual-licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.
