# M1 portable wire owner move

The detached Rust CUDA kernel and host adapters now consume one exact word-layout owner at
`holonics_portable::wire`. The move transfers these ten production modules from the `soma-abi`
package into `crates/holonics-portable/src/wire/`:

`contact`, `emission`, `live_event_cuda`, `material_shadow_cuda`,
`morphological_condition_cuda`, `morphological_conduct_cuda`, `recurrent_law_cuda`,
`returned_contact_cuda`, `text_restrict_cuda`, and `register`.

Their row layouts, constants, version words, discriminants, entry symbols, checked conversions,
and kernel behavior are retained. The `live_event_cuda -> emission` module dependency moves as a
single closure. Internal imports now use the portable crate's local modules; no forwarding paths
remain. The detached NVPTX kernel, `holonics-cuda`, `life`, and application manifests call the
portable owner directly. Their direct `soma-abi` dependencies have been removed. The package
remains in the workspace without those rows for the separate disposition of `current`, `holon`,
and `presentation`.

The moved source modules carry their inline unit tests. The two package-level REGISTER tests and
the cooperative CONTACT extent test moved from `soma-abi/src/tests.rs` to `holonics-portable`'s
`wire::tests`. `soma-abi`'s `current`, `holon`, and `presentation` modules and their tests are kept
unchanged. No kernel source behavior, entry signature or serialized identifier is intentionally
changed. The pinned PTX regeneration and parity checks below establish the bounded result of
that source move.

## Verification status

- `cargo check --locked -j2 --workspace --all-targets`: passed, including the dependent HNN,
  life, engine, CUDA, and application targets.
- `cargo test --locked -j2 -p holonics-portable -p soma-abi`: 168 portable tests passed with
  2 ignored; 4 remaining ABI tests passed. The moved `register` and `contact` tests check
  their word extents and register symbols on the portable host.
- `accelerators/cuda-kernel/build-ptx.sh` on pinned `nightly-2026-05-22`: passed;
  `ptxas -arch=sm_89` assembled the regenerated artifact. The prior PTX SHA-256 was
  `c42c65c86a687b8f7baf1ed7d215ca982a7e13b21cf882190219c00fd1726d3a`; the new
  artifact is `dd68dd2daf076c7e38130118ff12ff50df9d4e7d9422aadfb36e42ba2394b154`.
  All 37 exported entry names and parameter-type sequences match. Each exported entry body
  matches after normalizing Rust-mangled internal symbols, LLVM symbol suffixes, and anonymous
  symbol hashes; the complete PTX differs because moved module names and function ordering
  change internal symbols. This comparison does not assert identical helper-function names.
- Under `.local/gpu.lock` on the RTX 4080 SUPER, `mount-link-gate`, `mount-scope-gate`,
  `mount-register-gate`, and `mount-register-remount-gate` all passed against the regenerated
  artifact. The link, scope, and register gates report exact card/reference results; the
  remount gate reports exact fresh-context continuation.
