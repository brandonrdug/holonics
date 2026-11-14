# The lift (C3 of #603)

The plan's step is [THE_CONSOLIDATION](../../../../docs/plans/THE_CONSOLIDATION.md) §9, C3.

## The host part (commit `75b21a440`)

- **What moved.** `crates/engine` holds `field` (the law and its host reference, moved whole from `hnn::tower::field`) and
  `inherited`, the items the law borrowed. The borrowed items keep the file of the module they stood in:
  - from `hnn/tower.rs`: 45 items, 450 lines;
  - from `hnn/keyed_modes.rs`: 6 items;
  - from `receiver/coupling.rs`: 15 items;
  - from `compression/landmark/context.rs`: `wide_mul`;
  - `number/census.rs`, whole.
- **Text check.** A script compared each moved item's lines with the lines that left its source. They are equal but for the
  headers, the imports and the visibility (`pub` on each declaration, and on `Mass::of` and `Mass::log2`, which the coupling's tests
  call). Each moved engine file differs from its original only in paths.
- **The library.** `crates/holonics` imports everything back under its old paths (`pub use`), so no second copy stands. The engine
  crate depends on nothing in it.
- **Gate 1** passed (exit 0). It now runs the engine's 122 host tests on the new crate (41 s), and its guard lints and doctests.
- **Gate 3** (`gate3_host.txt`, the four-lane line's lap 6) printed `GATE_ENGINE EQUAL`:
  - parity on 3 sections;
  - 24 of 24 sections reproduced;
  - the lap's read equal byte for byte.

## The card part

The card part follows in its own pull request, and its receipt joins this one.
