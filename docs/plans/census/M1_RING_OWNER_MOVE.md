# M1 exact ring owner move

**Campaign:** #69, Rust cut. **Base:** `558db631` (portable section ABI owner).

Retired the host-only `holonic-words` package. Its mathematical owners now live at
`holonics::ratio::ring`: `ExactRing`, `CheckedIntegers`, `ModularWords`, `AccumulationLaw`, and the
typed `RingRefusal`. `ModularWords::MERSENNE61` names the exact mathematical modulus instead of a
backend device. Its arithmetic still dispatches to the unchanged portable section implementation
for `2^61 - 1`, and uses exact `u128` reduction for other moduli.

`ModularWords::new` returns `Result<_, RingRefusal>` and refuses moduli below two without referring
to section clauses. The ring keeps its pure `is_canonical` predicate but no longer owns table
admission. `SectionClause`, `SectionRefusal`, and `Sectioned` now belong directly to
`holonics-cuda::section_layout`; that owner checks coefficient/global-field canonicality before
staging and reports the same first offending index and section clause. `AccumulationLaw` remains a
generic ring law in `holonics::ratio::ring`; CUDA decides which laws its section implementation can
enact.

Main prime-image code/tests now import ratio rings directly. CUDA consumes them from Holonics,
retains its section refusal types in the section module, and has no crate-root compatibility
re-exports for those section or ring types. Engine adoption consumers use each direct owner. The
dependency direction is `holonics-portable → holonics → holonics-cuda`; `holonics` has no CUDA edge.
`soma-abi` retains its other wire records, and the detached kernel continues to depend on the
portable section ABI. The `holonic-words` manifest, workspace member and lockfile package are
removed.

## Verification pending

No Cargo or CUDA build was run for this cut. Focused gates:

- `cargo test -p holonics --lib ratio::ring -j 2`
- `cargo check -p holonics --all-targets -j 2`
- `cargo check -p holonics-cuda --all-targets -j 2`
- `cargo test -p holonics-cuda --lib section_layout -- --test-threads=2`
- `cargo check -p holonic-engine --all-targets -j 2`
- `cargo check -p holonics-hna --all-targets -j 2`
- `cargo tree -p holonics` to confirm no `holonic-words` or CUDA edge.
- Run the ignored section-adoption card tests under `.local/gpu.lock` against the unchanged PTX.

No NVPTX source or PTX code changed: the kernel still compiles the unchanged
`holonics-portable::section_layout_cuda`; only host-side ring ownership, section admission, and the
CUDA crate's dependency on main changed.
