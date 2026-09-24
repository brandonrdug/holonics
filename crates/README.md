# Rust libraries

[definition] The host workspace has two libraries. Lean holds the mathematics; Rust holds what
runs. Start with [the machine](../docs/THE_MACHINE.md) and the
[elementary objects](../docs/ELEMENTARY_OBJECTS.md#operator-contract), whose operator contract
lists each object's current and target owners. Device-only builds live under
[`accelerators/`](../accelerators/README.md).

| Library | Responsibility |
|---|---|
| `holonics` | The main library; it builds without CUDA. The Holon law and its facets (`holon`, `port`, `dirac`, `complex`, `element`, `generator`, `restriction`, `law`, `deposition`, `reaction`, `conformance`), ratio and ring arithmetic (`ratio`), exact geometry with screws and winding (`geometry`), receivers with standing and release (`receiver`), structural carriers (`structure`), and the exact base (`exact_linear`, `exact_value`, `exact_work`, `inertia`, `prime_image_algebra`, `rational_polynomial`, `rebase_invariants`, `primality`, `hardware_cover`). |
| `holonics-cuda` | The CUDA backend. Today it holds the device driver (context, module, stream, allocation, transfer completion, launch census) and the `mount-smoke` binary. It depends on `holonics` and realizes its operations on the card. |

[definition] [THE_REBUILD](../docs/plans/THE_REBUILD.md) reorganizes `holonics` into the operator
modules `ratio`, `geometry`, `holon` (with `contact` and `parametron`), `navigator` (today's
`generator`) and `receiver` (step 1), adds `holarchy`, `aeon`, `compression` and `hnn` (steps
2–4), and builds the resident HNN in `holonics-cuda::hnn` (step 5). These target names are not
code until their step lands. The retired engine, the HNN prototype and the applications are in
history at [`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734); a law is ported
from there one owner at a time and tested by the law it implements.

Check: `cargo check --workspace --all-targets`.
