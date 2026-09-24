# M1 receiver release owner move

Issue: #69. Source-neutral receiver width and release operations now belong to the main
`holonics::receiver::release` module. The complete bounded implementation and its tests moved from
`holonic-engine`; the engine retains only its receiver-atlas, neck and interaction consumers.
Their imports, citation checker and operator maps point to the main owner. No old-path forwarding
module remains.

`holonics::law::receiver` remains the owner of passive linear readings, receiver faces, width value
invariants, `WidthRefusal`, the two-axis `Horizon`, and the validated width wire.
`holonics::restriction::tube::horizon` remains the owner of tube stations, transverse restrictions
and two-axis reach. The release module consumes these objects; it does not duplicate their laws.

## Lean correspondence and representation boundary

Lean `Foundation/ReceiverRelease.lean` proves width and release statements for an arbitrary
nonempty finite `Finset X` and exact rational reading `R : X → ℚ`. In particular,
`ReleaseLaw.widenSound` requires the measured width to fit the tolerance named by a `Widen`
return. Rust had accepted any proposed widening tolerance. The moved `release` now returns typed
`WidthRefusal::WidenTooNarrow(WidenClaim { law, width, tolerance })` when the proposal is below the
measured exact width. This preserves the caller's choice of decision while enforcing the proved
obligation.

The Rust implementation enumerates a bounded finite family exactly, or computes an exact image of
a declared rational `ExactZonotope` under an exact affine matrix. The enclosure's diameter is exact
for that declared hull and is an upper bound when the true compatible set is smaller; this is the
`width_le_of_bounds` direction. The Lean source proves that general bound theorem but does not
formalize Rust's zonotope data representation, its matrix recurrence, its nonlinear-enclosure
refusals or its resource ceilings. No theorem-to-code equality for the zonotope construction is
claimed here. Nonlinear readings on an enclosure and squared-Euclidean enclosure widths remain
typed refusals.

The face/passive law remains separately owned in `holonics::law::receiver`, and tube horizon
composition remains in `holonics::restriction::tube::horizon`. This packet is an owner relocation
plus the explicit widening-law correction; it does not add active reception or a global release
gate.

## Verification

Passed on the pre-standing-receipt base `27ab48c5` before the parent restacks this cut:

- `cargo test --locked -j 2 -p holonics --lib receiver::release::`: 39 passed, including the
  width-4 / proposed-tolerance-3 refusal and the valid width-4 / tolerance-4 proposal.
- `cargo check --locked -j 2 -p holonic-engine --all-targets`: passed; NVCC built the existing
  exact engine CUDA laws for compute_89.
- Engine focused tests: `lean_citations::` 3 passed; `receiver_atlas::` 36 passed / 1 ignored;
  `neck::` 21 passed; `continuing_tube::` 42 passed.
- After rebasing onto the verified standing tip `c776fcea`,
  `cargo check --locked -j2 --workspace --all-targets` passed in 4m27s. This checks the moved
  owner through engine, CUDA, life, HNA and the application targets on the stacked graph.

No Lean declaration changed. The Lean source-owner comments now point at their distinct Rust owners;
no separate Lake build was needed for this relocation. The matrix-to-zonotope construction and its
resource limits remain outside the formal theorem, as stated above. The command/result receipt is
recorded in `docs/VERIFICATION_RECEIPTS.tsv`.
