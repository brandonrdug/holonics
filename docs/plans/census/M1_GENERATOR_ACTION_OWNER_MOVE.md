# M1 generator/action grammar owner move

The allocation-free active-cut grammar now belongs to `holonics::generator::action`, the main
Holon library's situated generator/action owner. The move preserves the active schema version,
word positions, constructors, validation behavior, and tests from the former
`crates/holonic-abi/src/active.rs`. Main membrane receive and `life` host source adapters import
the owner directly; there is no `soma_abi::active` forwarding module. The detached CUDA kernel has
no active-cut import: at the source tip used for this cut, its imports are the device emission,
event and operation wire modules plus `contact` and `register`.

## Disposition of the unused host conduct routine

`crates/holonic-abi/src/conduct.rs` was removed with the active module because it imported
`crate::active::{relation_span_node, ValidationError, View}` and had no independent consumer.
Source inspection at the parent M1 tip found `ConductTarget`, `CurrentConduct`, and
`conduct_current` only in that file; there were no external call sites and no `#[test]` in the
module. The actual consumed receive owner is `holonics::membrane::LiveCurrentMachine`, described
with its source call sites by `docs/plans/census/R2_MEMBRANE_EDGE.md` and its owner in
`docs/plans/census/M1_MEMBRANE_OWNER_MOVE.md`.

The removed routine's chronological host dispatcher (including its pending-dark aggregation) is
not represented as a second public operator. The active-cut source construction and the live
receiver's established semantics remain documented in
`research/records/2026-07-18_THE_RELATION_IS_THE_ACTIVE_MOUTH_THE_HOLON_CLOSES_LIVE.md` and
`research/records/2026-07-19_THE_EVENT_EMANATES_THE_SUCCESSOR_THE_EXECUTOR_CANNOT_RECONSTRUCT_THE_MACHINE.md`.
This retirement does not remove the active grammar or any shared wire records. `current`,
`holon`, and `presentation` remain in `soma-abi` with their current tests and separate disposition.

## Verification status

The moved action grammar tests passed 5/5; main membrane live-current tests passed 22/22; retained
`soma-abi` tests passed 19/19. The locked all-target check for `holonics` and `life` passed in 4m01s.
`cargo tree --locked -p holonics -e normal` shows only `holonics-portable` among the in-repository
dependencies and no `soma-abi` edge. Commands and outputs are recorded in
`docs/VERIFICATION_RECEIPTS.tsv`. `git diff --check` passed after rebase. CUDA/PTX sources are
unchanged; the existing CUDA wire and link gates remain the parity check for the separate wire
owner campaign.
