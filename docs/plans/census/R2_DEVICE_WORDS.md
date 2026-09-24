# R2/M1 device and exact-word ownership audit

Source audit for the R2 and M1 boundaries in
[`THE_REPOSITORY_RESTRUCTURE.md`](../THE_REPOSITORY_RESTRUCTURE.md#final-decisions), performed
2026-09-23. This records present dependency edges and migration gates; it is not a deletion
disposition.

## Verified Cargo and arithmetic edges

- The detached NVPTX package [`accelerators/cuda-kernel/Cargo.toml`](../../../accelerators/cuda-kernel/Cargo.toml#L22-L24)
  depends directly on `body` and `soma-abi`. Its source imports
  [`soma_abi::section_layout_cuda`](../../../accelerators/cuda-kernel/src/lib.rs#L76-L84);
  it does **not** have a direct Cargo dependency on `holonic-words`.
- Host [`holonic-core`](../../../crates/holonic-core/Cargo.toml#L10-L17) directly depends on
  `holonic-words`. `prime_image_algebra` imports `ExactRing` and `ModularWords` and stores the ring
  in `PrimeChart` ([source](../../../crates/holonic-core/src/prime_image_algebra.rs#L136-L149),
  [type](../../../crates/holonic-core/src/prime_image_algebra.rs#L513-L547)).
- [`holonic-words`](../../../crates/holonic-words/src/lib.rs#L9-L20) delegates the device-modulus
  operations to `soma-abi::section_layout_cuda`; the host and NVPTX arithmetic therefore share that
  source today ([modular operations](../../../crates/holonic-words/src/lib.rs#L216-L268),
  [ring implementation](../../../crates/holonic-words/src/lib.rs#L313-L330)). `holonic-words`
  imports `std::fmt` and is **not** `no_std`; the shared low-level arithmetic owner is `soma-abi`,
  whose crate root is `#![no_std]` ([crate root](../../../crates/holonic-abi/src/lib.rs#L1-L18),
  [CUDA arithmetic](../../../crates/holonic-abi/src/section_layout_cuda.rs#L1-L20)). Do not describe
  `holonic-words` as a direct NVPTX dependency. Its host use and the shared arithmetic source both
  need explicit dispositions before it can fold into `holonics::ratio`.

## PTX boundary and live consumers

- `holonics_cuda::SOMA_PTX` uses `include_bytes!` on the committed artifact
  [`soma_kernel_cuda.ptx`](../../../accelerators/cuda-kernel/soma_kernel_cuda.ptx), so Cargo needs
  that source-tree path at compile time ([definition](../../../crates/holonics-cuda/src/lib.rs#L61-L64)).
  Runtime loading passes the embedded byte slice to `Module::load_ptx`, whose API accepts bytes
  ([loader](../../../crates/holonics-cuda/src/cuda.rs#L930-L945)). There is no separate runtime
  filesystem lookup for this artifact. This differs from engine PTX generated in `OUT_DIR` by
  [`holonic-engine/build.rs`](../../../crates/holonic-engine/build.rs#L138-L284) and embedded by
  `include_bytes!(concat!(env!("OUT_DIR"), ...))`, for example
  [`cuda_refine.rs`](../../../crates/holonic-engine/src/cuda_refine.rs#L195-L208).
- Mount embeds and validates the committed PTX and its declared entries in
  [`lib.rs`](../../../crates/holonics-cuda/src/lib.rs#L69-L180); its section-layout and launch-law
  tests load the same bytes (for example
  [`section_layout/tests.rs`](../../../crates/holonics-cuda/src/section_layout/tests.rs#L850-L875)
  and [`launch_law/tests.rs`](../../../crates/holonics-cuda/src/launch_law/tests.rs#L715-L735)).
  The standalone mount gates also call `Module::load_ptx` on embedded bytes.
- Engine's [`section_layout_adoption` test](../../../crates/holonic-engine/src/section_layout_adoption/tests.rs#L207-L239)
  loads `holonics_cuda::SOMA_PTX`, resolves the section kernels and executes the generated section triple.
- `holonic-life` has live callers loading `SOMA_PTX`, including
  [`text_material_cuda.rs`](../../../crates/holonic-life/src/text_material_cuda.rs#L200-L210),
  [`returned_contact_cuda.rs`](../../../crates/holonic-life/src/returned_contact_cuda.rs#L270-L280),
  [`recurrent_section_cuda.rs`](../../../crates/holonic-life/src/recurrent_section_cuda.rs#L85-L100),
  [`material_shadow_cuda.rs`](../../../crates/holonic-life/src/material_shadow_cuda.rs#L77-L91),
  [`live_current_cuda.rs`](../../../crates/holonic-life/src/live_current_cuda.rs#L77-L98), and
  [`morphological_language/conduct_cuda.rs`](../../../crates/holonic-life/src/morphological_language/conduct_cuda.rs#L516-L530).
  Retiring `holonic-life` alone would not establish that the PTX, mount, or engine test can be
  removed.
- This committed Soma NVPTX artifact is a distinct realization from the engine HNN's NVCC-built
  `.cu` kernels. The engine build script registers CUDA source inputs and invokes `nvcc` for seven
  PTX artifacts ([rerun inputs](../../../crates/holonic-engine/build.rs#L51-L137),
  [compilation](../../../crates/holonic-engine/build.rs#L138-L284)). These build-time generated
  artifacts are also embedded as bytes; they are not runtime PTX file paths.

## Ownership boundary

The M1 apparatus move is complete: the driver and CUDA execution owners now live in
`holonics-cuda`:
`ffi.rs`, `cuda.rs`, `launch_law.rs`, `live_event_launch.rs`, `register_carrier.rs`,
`register_launch.rs`, `register_recast.rs`, and the CUDA staging/enactment portions of
`section_layout.rs`. The exports and module boundaries are enumerated in
[`holonics-cuda/src/lib.rs`](../../../crates/holonics-cuda/src/lib.rs#L11-L58).
Move the engine's resident HNN owners, device kernels, build script, and PTX inclusion/loading
owners to `holonics-cuda::hnn` as specified by §0.3 and §3.1.

Keep backend-neutral arithmetic and section laws in `holonics`: exact ring semantics and their
host reference; incidence declarations; local operators; scatter/accumulation laws and receipts;
and any refusal types consumed by those host laws. The engine imports the mount section APIs in
[`section_layout_adoption.rs`](../../../crates/holonic-engine/src/section_layout_adoption.rs#L55-L75);
`holonic-core` separately uses `ModularWords` in
[`prime_image_algebra.rs`](../../../crates/holonic-core/src/prime_image_algebra.rs#L136-L149).
The formal section law is independently owned in
[`SectionLayout.lean`](../../../formal/elementary-holonics/ElementaryHolonics/Foundation/SectionLayout.lean).
Keep CUDA-specific `SectionDeviceTables`, `SectionKernels`, device residency, driver resources,
launch derivation, and kernel execution in `holonics-cuda`; split them from the host declaration and
reference operations instead of importing the backend into main.

## Gates before retirement or move completion

1. Resolve the whole current consumer set for `SOMA_PTX`, mount APIs, and section-layout APIs,
   including the engine adoption regression, mount tests/gates, and each `holonic-life` caller.
   Record which are moved, replaced, or retired before deleting the artifact or kernel.
2. Preserve one-source host/NVPTX arithmetic while removing the Soma dependency edge. `soma-abi` is
   the present `no_std` source; `holonic-words` is host-only and uses `std`. Decide whether a small
   `no_std` shared implementation owner remains or the device compilation path can consume
   replacement source in `holonics::ratio`; do not duplicate the arithmetic and call parity
   verified merely because values match on a small fixture.
3. Split backend-neutral section declarations/reference law from CUDA staging and enactment, update
   every in-repository caller in the same move, and keep the Lean law paired with its Rust owner.
4. M1 acceptance remains the plan's gates: main `holonics` builds without CUDA SDK/driver/`nvcc`;
   `holonics-cuda` owner tests pass on the card; workbench and workspace all-target checks pass.
   Also verify PTX embedding/loading, the section-adoption path, and declared host/device arithmetic
   parity for every retained device entry.
