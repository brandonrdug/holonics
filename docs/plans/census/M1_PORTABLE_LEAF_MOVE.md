# M1 portable leaf: first source cut

This cut renames the dependency-free `no_std` package at `crates/holonic-body` to
`crates/holonics-portable` and its Rust crate name to `holonics_portable`. Its production modules
and behavior are unchanged. Current host, ABI, lifecycle, CUDA backend, application and detached
NVPTX kernel callers now import that crate directly; there is no forwarding `body` package or
compatibility alias. Serialized and wire identifiers are unchanged.

This is the first M1 portable-leaf cut, not the completed consolidation. `soma-abi` remains a
separate `no_std` package depending on the portable leaf. `holonic-words` remains a separate host
package; its classification and eventual owner move are still open. No device arithmetic was
changed. The detached kernel is rebuilt from the renamed shared source; its committed PTX changes
only through compiler-mangled identifiers and three source-path strings. The PTX builder now
remaps the checkout root to `/holonics`, so generated source-path strings no longer retain a
worktree-specific absolute path.

Suggested focused gates:

- `cargo test -p holonics-portable`: 149 passed, 0 failed, 2 ignored.
- `cargo check -p holonics --all-targets`: passed.
- `cargo check -p holonics-cuda --all-targets`: passed.
- `cargo check -p holonics-hna --all-targets`: passed; this covers the local
  `native::coupled_wave::body` module paths.
- `accelerators/cuda-kernel/build-ptx.sh` on pinned `nightly-2026-05-22`: passed; all 37 entries
  are present and `ptxas -arch=sm_89` validates the artifact.
- RTX 4080 SUPER `mount-link-gate`: exact host/card return for 65,536 places; OWN planes, topology,
  and touched map match.
- `cargo test --release -p holonic-engine --lib section_layout_adoption:: -- --ignored
  --test-threads=1` was cancelled during its uncached release-profile compilation. The focused
  dev-profile replacement passed 2 tests, 0 failed, 0 ignored.

PTX review: committed pre-build SHA-256 `699dc997c3fd92d428b9f1cecb725faa96fb05065fc2b1577125e597b4e44cc0`;
rebuilt, remapped SHA-256 `ab4d5b519b76abfa72fafecf70a0ec763a33c85e373ed92f0f9188a54c61af08`.
The exported `.visible .entry` names and parameter type sequences match 37/37. After normalizing
Rust, LLVM and anonymous symbol hashes, only three lines differ: byte strings that formerly
embedded `crates/holonic-body/src/{carriage,manifold,manifold/body_mount}.rs` now contain stable
`/holonics/crates/holonics-portable/...` paths. No instruction-body difference remains. The PTX
artifact is regenerated and committed with the source move so the embedded source paths and symbols
describe the new owner.

Scope is the package identity and current source imports, plus the required stable path remap and
rebuilt PTX artifact. Host/device ABI consolidation and word-ring placement remain pending.
