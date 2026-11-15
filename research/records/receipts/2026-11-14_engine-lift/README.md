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

## C5: the cut by object (branch `claude/consolidation-c5`)

- **The host cut.** `field.rs` is cut into 18 modules by object (THE_CONSOLIDATION §5):
  - width, ratio, declaration, constitution, founding, region, navigator, moment, contact;
  - carry, face, adjoint, deposit, release, level, realization, learner, ruler.

  The large `impl Field` and `impl FieldLearner` are split by method, one block per object. The pass's place (`StorePass`) goes to
  `learner.rs`, because its text reads the tower's `Result`.
- **The card cut.** `hnn/field.rs` is cut into 8 modules (§6): resident, moment, contact, carry, clock, adjoint, level, profile.
- **Text check.** A script read every line of each original file in the new modules, normalised for visibility. No line is missing.
  Private items reached across modules are `pub(crate)`.
- **Paths.** `field` keeps its module text and re-exports every module whole, so every path into it holds.
- **Gate 1** passed (exit 0).
- **Gate 3** (`gate3_c5.txt`) printed `GATE_ENGINE EQUAL`:
  - parity on 3 sections;
  - 24 of 24 sections reproduced;
  - the lap's read equal byte for byte.

### Timing (`timing_c5.txt`)

**The first hold.** It alternated control and build after a warm-up, as C3's had. It read C5 at 723.3 ms a section against the
control's 703.8, a 2.8% gap outside the control's 1.5 ms spread.

**Two more reads.** They showed the gap was the order's and not the build's:
- **The card sits in one of two states, run by run**, about 703 and about 722 ms a section, with one run at 741. Each build ran in
  both states.
  - A phases read (`FIELD_PHASES`) put the whole difference in the card's return: 16.46 s against 16.90 s over the 24 sections.
  - The host's deposit parts were equal between the builds.
- **The first hold's alternation put every C5 run on the slow state.**
- **A balanced hold** (warm-up, then c4 c5 c5 c4 c4 c5 c5 c4) gives these runs:

  | State | C4 | C5 |
  |---|---|---|
  | Fast | 703.4, 704.0 ms | 702.7, 703.5 ms |
  | Slow | 722.8, 741.0 ms | 722.7, 721.5 ms |

  State for state, C5 equals C4 within 0.7 ms on the fast state and within 1.3 ms on the slow, apart from C4's one run at 741 ms.

**The verdict.** The plan's guess for C5 (§8: within the spread) holds once the order is balanced. The first hold's reading of a 2.8%
gap was the order's. The timing rule now asks for a balanced order (CLAUDE.md).

## C6: the commands (branch `claude/consolidation-c6`)

- **The move.** `store_train.rs` is `athena::store`, `store_parity.rs` is `athena::parity` and `field_pass.rs` is the binary
  `athena`, whose words are field_pass's (`athena train complete-language train-store ...`). The exterior items the store line
  shared with the harness are `athena::exterior`, imported back by the harness until it retires (C8). `read-cavity`, the line's
  one live reading, sits in `athena::ruler::cavity`. `athena` depends on `holonics-engine`, `holonics-engine-cuda` and `rayon`.
- **What retired.** The October field line: `field_train.rs` (5,241 lines) and `field_parity.rs` (655 lines) with `train-field`,
  its 24 other commands, `parity-field` and `time-field`, held at `7a1eb3ce7`. Then 22 store readings and foundings, each built
  for one guess and each guess read, held at `264161d8e`. Kept: `train-store`, `read-cavity`, `write-store`, `found-lane`,
  `next-pass` (C1's inventory of the line's scripts), `parity-store`, and the card's measures (`yardstick`, `attributes`,
  `reserve`, `FIELD_PROFILE`, `FIELD_PHASES`). `crates/athena/src` holds 1,703 lines.
- **Gate 1** passed whole at `a584b5257` (59 steps), with athena's guard lints and tests among them. Its first run failed the
  guard lints: the harness's dev-dependency on athena reached the card crate, whose yardsticks owe their float lints, and clippy
  lints a workspace member it compiles as a dependency. The lints now name their crates with `--no-deps`.
- **Gate 3** (`gate3_c6.txt`) printed `GATE_ENGINE EQUAL` on the line's lap 13, its last saved state, with the athena build:
  parity on 3 sections; lap 13's first 24 sections reproduced from lap 12's stopped state; lap 13's read equal byte for byte.

### Timing (`timing_c6.txt`)

One balanced hold, a warm-up and then c5 c6 c6 c5 c5 c6 c6 c5, 24 sections from lap 12's stopped state. Every run's section lines
are equal. The card's two states stand again:

| State | C5 (field_pass) | C6 (athena) |
|---|---|---|
| Fast | 699.9 ms | 702.3, 700.0 ms |
| Slow | 718.8, 719.4, 717.8 ms | 717.0, 732.5 ms |

State for state, C6 equals C5 within 2.4 ms on the fast state and within 1.8 ms on the slow, apart from one run at 732.5 ms, as C4
held one at 741 in C5's hold. The plan's guess (§8: within the spread) holds; no engine code changed.

### The line on athena

The four-lane line goes on from lap 14 on the athena build (`chain8.sh`, private), which starts only once gate 3 printed EQUAL.
