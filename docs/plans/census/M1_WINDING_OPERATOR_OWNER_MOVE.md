# M1 winding operator owner move

The exact symmetric-circulant operator now belongs to `holonics::geometry::winding_inertia`:
validated circulant and cyclic-reading charts, named hands/passages, algebraic root isolation,
character-by-character winding inertia, and the exact cycle adjacency/laplacian readings. It uses
only the main Holonics exact arithmetic, inertia, and polynomial owners. Its Rust unit tests moved
with the operator.

The engine's `winding_inertia` module retains the application receivers: growth-to-circulant,
cyclic form search and its receiver results, plus the crystallographic lattice/constructibility
rung. Those need `grown_cell`, `matroid_chow`, or `multiquadratic`. Their integration tests remain
there. `CyclicReading` and `WindingError` stay with the operator because validated reordering is a
portable exact operation and is used by the engine form search; the error type also gives the
engine-owned search its typed refusals.

Direct mathematical callers now name the main-library path. No engine forwarding export remains.
The Lean owner is unchanged: `ElementaryHolonics.Transport.HolonicInteraction` and its geometry
imports continue to supply the formal counterpart. The existing `holonic-engine.holonic-interaction.v1`
wire identifier is unchanged.

Verification on the causal-chord base: the core winding suite passed 21/21; engine receiver and
lattice tests passed 7/7; the conservative-core chain consumer passed 1/1; the Boolean-matroid
circulant admission and named-null tests passed 2/2; and the existing inline Lean citation gate
passed 1/1. CUDA PTX was built for the detected `compute_89` target as part of the engine test
build. No full workspace suite was run for this bounded source move.
