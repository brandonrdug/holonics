# Rust libraries

[definition] The host workspace has two libraries. Lean holds the mathematics; Rust holds what
runs. Start with [the machine](../docs/THE_MACHINE.md) and the
[elementary objects](../docs/ELEMENTARY_OBJECTS.md#operator-contract), whose operator contract
lists each object's current and target owners. Device-only builds live under
[`accelerators/`](../accelerators/README.md).

| Library | Responsibility |
|---|---|
| `holonics` | The main library; it builds without CUDA. Its operator modules are `ratio` (one per two, exact carriers), `geometry` (frames, screws, winding, the half-turn), `holon` (the Holon law and its facets, with `contact` and `parametron`), `navigator`, `receiver` (reception, receipts, standing, release, the population), `holarchy` (with the known-truth terrains), `aeon`, `compression` (with the landmark tree), `hnn` (the field's host reference) and `physics`. |
| `holonics-cuda` | The CUDA backend. Today it holds the device driver (context, module, stream, allocation, transfer completion, launch census) and the `mount-smoke` binary. It depends on `holonics` and realizes its operations on the card. |

[definition] [THE_REBUILD](../docs/plans/THE_REBUILD.md) orders the work on these modules (its unified plan, U0–U8). The retired engine, the HNN prototype and the applications are in history at [`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734); the owners retired on September 28 are at [`2d34b819`](https://github.com/brandonrdug/holonics/tree/2d34b819). A law is ported from history one owner at a time and tested by the law it implements.

Check: `cargo check --workspace --all-targets`.
