# M1 portable leaf: first source cut

This cut renames the dependency-free `no_std` package at `crates/holonic-body` to
`crates/holonics-portable` and its Rust crate name to `holonics_portable`. Its production modules
and behavior are unchanged. Current host, ABI, lifecycle, CUDA backend, application and detached
NVPTX kernel callers now import that crate directly; there is no forwarding `body` package or
compatibility alias. Serialized and wire identifiers are unchanged, and committed PTX is untouched.

This is the first M1 portable-leaf cut, not the completed consolidation. `soma-abi` remains a
separate `no_std` package depending on the portable leaf. `holonic-words` remains a separate host
package; its classification and eventual owner move are still open. No device arithmetic was
changed. The source branch is ready for the coordinated host and pinned NVPTX gates; verification
is pending because another campaign currently owns the shared build target.

Suggested focused gates:

- `cargo test -p holonics-portable`
- `cargo check -p holonics --all-targets`
- `cargo check -p holonics-cuda --all-targets`
- Run `accelerators/cuda-kernel/build-ptx.sh` with its pinned nightly/toolchain, then verify the
  committed PTX artifact remains unchanged unless the generated artifact is proven semantically
  identical and the artifact owner explicitly updates it.

Scope is the package identity and current source imports only. Host/device ABI consolidation,
word-ring placement, and device gates remain pending.
