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
unchanged. No kernel source behavior, committed PTX artifact, entry signature or serialized
identifier is intentionally changed; PTX regeneration and parity checks remain pending coordinated
verification.

## Verification status

No builds or device runs were performed in this cut. Required focused gates are:

- `cargo test --locked -j 2 -p holonics-portable` and `cargo test --locked -j 2 -p soma-abi`;
- `cargo check --locked -j 2 -p holonics-cuda -p life -p holonic-engine -p holonics-hna -p holon-plate --all-targets`;
- rebuild the detached kernel using `accelerators/cuda-kernel/build-ptx.sh` on the pinned nightly,
  verify all exported entry names/parameter signatures and normalized instruction bodies against
  the committed PTX, accounting only for the established stable source-path remap;
- run the existing `mount-register-gate` and `mount-register-remount-gate` on the admitted CUDA
  device, and the applicable event/link gates for the live-current schemas.

The moved `register` and `contact` tests check their word extents and register symbols on the
portable host. Device gates are still needed to establish host/card parity.
