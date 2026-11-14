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

## The card part (branch `claude/card-image`)

The plan named the card, the driver and the card realization as moves. Reading them showed three facts that stood in the way, so
three alterations came first, and the move last.

**The three alterations.**
1. **The card opens with no image.** `Card::open` had loaded the October image (`hnn.ptx`) on every open, and the field never
   launches from it, because it loads its own. `Card::open_with_image` serves the owners that launch from the card's image, and the
   October owners open through `hnn::open_hnn`. The line's binary no longer embeds the October image: it is 14.2 MB, against 15.5 MB
   for the binary of C2.
2. **The card's refusals become `CardError`.** These are `Driver`, `NoKernels`, `Census`, `ForeignBuffer`, `Launch` and `Shape`,
   each with its message unchanged. The October `DeviceError` converts from it case for case, and the October adapters take either
   error.
3. **The October card methods become extension traits.** Five `impl Card` blocks in October files became `CardLatticeRead`,
   `CardOuterUpdate`, `CardExactWord`, `CardInverseExact` and `CardEpochFlow`, because an inherent impl cannot stand outside the
   type's crate.

**The move.**
- `cuda.rs`, `ffi.rs`, `hnn/card.rs` and `hnn/field.rs` move to `crates/engine-cuda`. They differ from their originals only in
  visibility (`pub(crate)` becomes `pub`) and paths.
- The three field kernel sources move byte for byte.
- The field image's part of the build script moves with them, with the same `nvcc` arguments.
- The engine card crate depends on the engine and on nothing in `crates/holonics` or `crates/holonics-cuda`.

**Gates.**
- **Gate 1** passed (exit 0).
- **Gate 3** (`gate3_card.txt`) printed `GATE_ENGINE EQUAL`:
  - parity on 3 sections;
  - 24 of 24 sections reproduced;
  - the lap's read equal byte for byte.
- **The GPU suites** of both card crates passed: 144 tests in one hold, ending at 21:45 UTC.
  - `holonics-cuda`: 69 library tests, and 51 in its integration files.
  - `holonics-engine-cuda`: 24 library tests.

  This covers the October owners that now open the card through `open_hnn` and reach it through the traits.

**Timing** (`timing.txt`). One hold ran a declared warm-up, then control, C3, control, C3, control, C3, on 24 of the line's
sections. The control is main before C3, the binary of C2.

| Build | Run | Run | Run | Mean |
|---|---|---|---|---|
| Control (C2) | 713.4 ms | 713.2 ms | 711.8 ms | 712.8 ms |
| C3 | 714.3 ms | 713.7 ms | 712.3 ms | 713.4 ms |

The difference is 0.6 ms a section (0.08%), inside the controls' own spread of 1.6 ms, so it is no difference. The plan's guess
(§8: within the spread) held. Every run's section lines equal the first's.

**A finding for the line.** Laps 7 and 8 of the four-lane line stopped at 2,899 and 2,864 sections, at their projection (2,100 s).
They ran beside this step's builds, which share the host's cores with the deposit's per-entry loops (#812). Lap 9, with no build
beside it, ran its 3,000.

## C4: the codec, the region and the passage (branch `claude/consolidation-c4`)

- **One alteration first.** The store's `Slice` held a file, and the guards keep the file system out of the engine. A slice now
  reads through `PieceBytes`, and the store's file (`SliceFile`) stays in the harness. The reads and their bytes are the same.
- **The move.** Four modules come into the engine:
  - `codec.rs`: `FieldCodec`, `question_text`, `RECORD`, `UNIT`, and the `count` parser it reads its text with;
  - `region.rs`: `TrainRegion` and its views;
  - `passage.rs`: the problems, the masks, the held read and the store's cut;
  - `units.rs`: `hnn/units.rs`, whole.

  A script compared the moved lines with the lines that left the harness. They are equal but for headers, imports and visibility.
  The harness keeps what reads files and prints lines, at its root. `store_train.rs` imports nothing from `field_train.rs` or
  `tower_train.rs`.
- **Gate 1** passed (exit 0).
- **Gate 3** (`gate3_c4.txt`) printed `GATE_ENGINE EQUAL`:
  - parity on 3 sections;
  - 24 of 24 sections reproduced;
  - the lap's read equal byte for byte.
