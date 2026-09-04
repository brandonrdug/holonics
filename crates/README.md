# Rust libraries

[definition] All live host Rust libraries belong here; executable consumers belong under
`applications/`, and independent device-only builds under `accelerators/`.

| Library | Responsibility |
|---|---|
| `holonics` | Public framework namespaces: HNA, Soulkiller and interoperability. |
| `holonics-hna` | Native application/session API, exterior codecs and bounded artifact adapters. |
| `holonics-workspace` | The specialized persistent snapshot/workspace artifact family. |
| `holonic-engine` | Native mathematical computation, resident CUDA laws, operator ecology, dismantling and comparison owners. |
| `holonic-life` | Earlier lifecycle/package, source transport and application-boundary owners (Cargo package `life`). |
| `holonic-structure`, `relational-geometry`, `holonic-language` | Structural, geometric and reflective substrate owners. |
| `holonic-body`, `holonic-abi`, `holonic-membrane` | Exact low-level laws and boundary carriers. |
| `holonic-mount`, `holonic-surface`, `holonic-circulation-abi` | CUDA/display apparatus and the specialized circulation ABI. |

The [architecture map](../docs/ARCHITECTURE_MAP.md) gives exact ownership and scope. A crate's
historical package name does not create a second implementation.
