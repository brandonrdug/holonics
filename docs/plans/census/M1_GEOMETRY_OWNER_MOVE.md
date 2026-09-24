# M1 geometry owner move

The former `relational-geometry` source now lives under `crates/holonics/src/geometry/`.
`holonics::geometry` owns exact frames and vectors, screw pairs, phase/carry, η charts,
receiver-relative projection/topology, decorated paths and exact analytic operations. Its
fourteen examples moved to the main library. In-repository Rust callers and Cargo manifests
use that owner directly; the standalone package and the facade re-export are retired.

The internal geometry modules `exact` and `exact_analysis` are private implementation carriers.
Their public types and functions are reached through `holonics::geometry`, so they do not create
a public `holonics::exact` object. Geometry source imports were recharted under the internal
module; the move changes no formula, chart admission or receiver scope. Historical serialized
schema strings beginning `relational-geometry.` remain byte-identical.

`cargo check -p holonics --lib` passed; the moved geometry owner tests passed **87** with no
failure or ignored test. The locked workspace all-target check passed, including the moved
examples and all engine/HNA/life callers. `cargo tree -p holonics -e normal` now has only
`holonic-words` among the remaining repository library dependencies, and no engine, HNA, life,
mount or CUDA edge. Exact commands and logs are recorded in the verification TSV.

The main library now owns its Holon, structure and geometry source. The exact word/ABI seam,
source-neutral engine/HNN, live membrane runtime, and resident CUDA/HNN owner moves remain M1
work. The M2 Lean roots and closing README/operator-contract revision remain open.
