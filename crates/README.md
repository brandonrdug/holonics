# Rust libraries

[definition] Live host Rust libraries belong here. Applications live under `applications/`; a library's
examples and focused executable controls live beside that owner under `examples/`. Independent
device-only builds live under `accelerators/`. Start with [the machine](../docs/THE_MACHINE.md)
and follow the actual source/consumer map.

| Library | Responsibility |
|---|---|
| `holonics` | Main Holon law, structural carriers, receiver-relative geometry, live receiving/standing and source-neutral exact operators. |
| `holonics-hna` | Native application/session API, exterior codecs and bounded artifact adapters. |
| `holonics-workspace` | The specialized persistent snapshot/workspace artifact family. |
| `holonic-engine` | Native mathematical computation, resident CUDA laws, operator ecology, dismantling and comparison owners. |
| `holonic-life` | Earlier lifecycle/package, source transport and application-boundary owners (Cargo package `life`). |
| `holonic-language` | Reflective substrate owner. |
| `holonic-body`, `holonic-abi` | Shared exact substrate and host/device wire carriers, pending the portable kernel-law consolidation. |
| `holonic-mount` | CUDA apparatus. |

The [architecture map](../docs/ARCHITECTURE_MAP.md) gives exact ownership and scope. A crate's
historical package name does not create a second implementation.
