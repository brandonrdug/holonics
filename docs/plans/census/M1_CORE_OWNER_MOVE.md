# M1 core owner move

The Holon law and its exact substrate now live at the root of `crates/holonics/src/`, with
`holonics::Holon` as the central public type and qualified facet modules (`holon`, `law`, `port`,
`dirac`, `complex`, `element`, `generator`, `restriction`, `deposition`, `reaction`). The
source-neutral exact operators remain qualified under `exact_linear`, `exact_value`,
`exact_work`, `inertia`, `prime_image_algebra`, `rational_polynomial` and their owning modules.
This is the same checked Rust law moved from `holonic-core`; no new Holon is founded here.

The source belongs at the crate root: the former core source has 240 internal `crate::` references
whose meaning is preserved by that placement. A nested `holonics::core` module would require
another path layer or a forwarding alias. The `holonic-core` Cargo member and dependency are
retired. Engine, HNA, life, plate, tests and examples import the moved types directly from
`holonics`. Five external `fibre_field_names!` macro calls now name the main crate.

Eight pure engine re-export files retired with the move: `exact_linear`, `exact_value`,
`exact_work`, `hardware_cover`, `inertia`, `prime_image_algebra`, `rational_polynomial` and
`continuing_tower`. The engine-only prime-image consumer checks remain in
`core_prime_image_integration_tests.rs`. Mixed engine modules (`world`, `rebase_invariants`,
`relation_ladder`, `receiver_release`, `continuing_tube`, `holonic_interaction`) retain their own
operations but no longer publicly forward core declarations. `causal_chord` retains its
half-plane functions because they adapt errors to `ChordRefusal`; the exact count and carrier
belong to `holonics::rational_polynomial`. The historical `holonic_engine::hardware_cover`
string in a mode-identity packet is a retained wire identifier, not a Rust import path.

## Dependency and verification

`cargo tree -p holonics -e normal` has no engine, HNA, life, mount or CUDA edge. The main crate
still consumes `holonic-words`, `relational-geometry` and `holonic-structure`; their final M1
dispositions are separate source moves. `cargo check -p holonics --lib` passed; its moved core
suite passed **302**, failed **0**, ignored **1**. The engine's prime-image pair-law integration
test passed **1**. The locked workspace all-target check passed after the direct caller and
`holon-plate` manifest changes. Exact commands and logs are in the verification TSV.

This cut makes the main crate substantive and backend independent. It does not finish the
two-library target: structural/geometric source, source-neutral engine/HNN laws, live membrane
receive/standing runtime, resident HNN, mount, kernels and the CUDA package still have their M1
owner moves. M2 Lean roots and the closing README/operator-contract revision are also open.
