# M1 portable section ABI owner move

**Campaign:** #69, Rust cut. **Base:** `40f71c41` (portable leaf plus workspace caller receipt).

Moved `soma-abi::section_layout_cuda` into `holonics_portable::section_layout_cuda`. The module's
production source and symbols are unchanged: `Entry`, entry-name constants, parameter-word counts,
shared-tile name, modulus, and exact `reduce`/`canonical`/`add`/`mul`/`is_canonical` arithmetic all
retain their existing definitions. The explicit `_cuda` module name remains because the entry and
shared-memory declarations describe the actual CUDA kernel ABI; the same dependency-free `no_std`
source is compiled by both the host and detached NVPTX crate.

The detached kernel, CUDA section host implementation and PTX signature checks, and host
`holonic-words` wrapper now import the portable module directly. `holonic-words` now depends on
`holonics-portable` instead of `soma-abi`; the CUDA backend retains `soma-abi` for its other
register and live-event records. `soma-abi` itself remains a separate crate for those records and
depends on the portable base as before. There is no cycle or forwarding module.

Moved the four D3 section-ring tests and `RING_PROBES` out of the ABI crate's test module and beside
the portable implementation. The independent REGISTER entry-symbol test remains with ABI tests.

## Verification

- `cargo test -p holonics-portable -j 2`: 153 passed, 0 failed, 2 ignored, including all four moved
  section-ring tests.
- `cargo test -p soma-abi -j 2`: 24 passed, 0 failed; the retained register-entry test passes.
- All-target checks passed for `holonic-words`, `holonics`, `holonics-cuda`, and `holonics-hna`.
- `accelerators/cuda-kernel/build-ptx.sh` on pinned `nightly-2026-05-22` and `ptxas -arch=sm_89`:
  passed.
- Ignored `holonic-engine::section_layout_adoption` device tests under `.local/gpu.lock`: 2 passed,
  0 failed, 0 ignored in the dev profile against the regenerated PTX.

The PTX was regenerated because the module's Rust crate owner changed. The prior artifact SHA-256
was `ab4d5b519b76abfa72fafecf70a0ec763a33c85e373ed92f0f9188a54c61af08`; the regenerated artifact
is `c42c65c86a687b8f7baf1ed7d215ca982a7e13b21cf882190219c00fd1726d3a`. All 37 exported entry
names and parameter-type sequences match. After normalizing Rust-mangled, LLVM and anonymous
symbol hashes, the complete PTX text is identical: zero remaining hunks, including instruction
bodies and source strings. The build script's stable `/holonics` path remap is active.
