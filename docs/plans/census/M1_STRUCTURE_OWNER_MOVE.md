# M1 structural carrier owner move

The former `holonic-structure` library's thirteen Rust source files now live in
`crates/holonics/src/structure/`. `holonics::structure` is an internal module exposing the same
relation, chain, face, gauge, keyed/ordinal atlas, local-population, lineage and `CausalMembrane`
carriers. The standalone Cargo package and its facade re-export were removed. In-repository
engine, life, language and membrane callers import the moved module directly; their manifests
depend on `holonics` where they consume it. No schema or current wire identifier changed.

The former library was `no_std` with allocation. Its source still uses `alloc` where needed, but
it now builds as part of the main Holonics crate. This is a package-boundary move, not a new
causal law. The main crate remains backend independent: `cargo tree -p holonics -e normal` has no
engine, HNA, life, mount or CUDA dependency. Geometry and exact word arithmetic are still
separate source owners.

`cargo check -p holonics --lib` passed. The workspace all-target check passed after the move,
and `cargo test -p holonics --lib -- --test-threads=2` passed **332** tests, with **0** failures
and **1** ignored test. The additional thirty passing tests are the relocated structural owner
checks. Commands and logs are pinned in the verification TSV. This does not complete the M1
geometry, source-neutral HNN, live membrane or CUDA resident moves.
