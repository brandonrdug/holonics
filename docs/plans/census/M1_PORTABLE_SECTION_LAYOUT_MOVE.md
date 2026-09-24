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

## Verification pending

No Cargo or kernel build was run in this source cut. Required focused gates:

- `cargo test -p holonics-portable -j 2`
- `cargo check -p holonic-words --all-targets -j 2`
- `cargo check -p holonics --all-targets -j 2`
- `cargo test -p holonics-cuda --lib section_layout -- --test-threads=2`
- `cargo check -p holonics-cuda --all-targets -j 2`
- `cargo check -p holonics-hna --all-targets -j 2`
- Rebuild `accelerators/cuda-kernel/build-ptx.sh` on its pinned toolchain, validate with `ptxas`,
  compare exported entry names/signatures and normalized instruction bodies, then run the ignored
  `holonic-engine::section_layout_adoption` CUDA tests under `.local/gpu.lock` against that PTX.

The PTX source dependency changes and will need regeneration after these gates. Its owner must
review the regenerated file for stable path mapping, unchanged public entries, and equivalent
device instruction bodies before committing that artifact.
