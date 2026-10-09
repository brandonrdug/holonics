# Publication note

This directory publishes the compact receipts of one diagnostic of #73: a second observation learned
beside the first (Refs #73).
- Source `6fd119c0d` (`6fd119c0ddc95`, full `6fd119c0ddc951c906f8dc3d09aa27077ed782ed`, tree
  `9aaf0f3ed7711981b24a44e12e257596efc09c7c`), one test-only commit above the second-publication
  evidence `5230a4c44`. It adds the fixture
  `hnn::tests::physical_communication::a_second_observation_is_learned_beside_the_first`: 190 added lines
  in `crates/holonics/src/hnn/tests/physical_communication.rs`, no deleted line, no other file.

- **The diagnostic at `6fd119c0d`** ([handoff](diagnostic-v1/HANDOFF.md),
  [validation](diagnostic-v1/VALIDATION.json)).
  - Grade: diagnostic, trust checks passed. The fixture ran once, by exact name: 1 passed, 0 failed,
    1,160 filtered out. `learning_acceptance_certified` is false.
  - Call 1 teaches observation A at Rest (source `[0, 1]`, observed `[0, 1, 3]`). Call 2 teaches a
    different observation B at the received opening call 1 left (source `[1, 0]`, observed `[1, 0, 2]`).
    Station 2 is the compared station of both.
  - Both landings read `Phase` (`Some(Ok(Phase))` for call 1 and for call 2).
  - Call 2 committed all three families against A's material (3 of 3), each with one nonzero `q` at one
    of 36 entries and none vanished:
    - C: `q = −1` at entry 32, `η = 1/4096 = 2⁻¹²`;
    - K: `q = +1` at entry 25, `η = 1/2048 = 2⁻¹¹`;
    - D: `q = −1` at entry 0, `η = 1/16384 = 2⁻¹⁴`.
  - Six blind reads, each through a fresh `PhysicalReceiver` entering at the opening call 2 left, with the
    same current: A's source on three materials (both learned, A only, initial), B's source on two (both
    learned, A only), and A's source on A only a second time.
  - Four station-2 contrasts, each the learned reading minus the control over the station's eight logits,
    and each with all eight coordinates nonzero:
    1. B's learned response: both learned minus A only, on B's source;
    2. A's own learned response: A only minus initial, on A's source;
    3. what learning B did to A's response: both learned minus A only, on A's source;
    4. A's response with both learned: both learned minus initial, on A's source.

    The exact rational vectors are in `diagnostic-v1/stages/cross-observation-diagnostic-20261009-v202.stdout`
    and in `VALIDATION.json`. The floor of log₂ of the coordinates' magnitudes lies in −23 to −19 for
    contrast 1, −21 to −17 for 2, −22 to −20 for 3 and −26 to −17 for 4.
  - The trust asserts held: each family's applied factor reaches the resident unchanged, every movement
    lies on its family's lattice, all six reads close, A's source read twice on A only gives identical
    boundaries, and A's and B's sources read differently on A only.
- **Provenance** (re-checked when packaging).
  - `diagnostic-v1/FILE_HASHES.json` lists 430 files (91,225,514 bytes). All 430 were re-hashed and match
    in sha256 and size.
  - `VALIDATION.json` records 347 frozen native inputs. Each matches its git blob at `6fd119c0d` byte for
    byte (347 of 347). Against the accepted physical publication `8121219ef`
    (`8121219ef7f32a0cf94b5efcdfb74a3e0fecedd8`), exactly one input differs,
    `crates/holonics/src/hnn/tests/physical_communication.rs`; the other 346 are unchanged.
- **Stages** ([validation](diagnostic-v1/VALIDATION.json)). Each stage was accepted, quiescent and released,
  finished within its fixed projection, ran under the 8,589,934,592 B group memory cap, and no limit was
  raised after launch.
  - `actual-cross-prep8-20261009-v201` (preparation, one core, no compiler launched): wall 9,095,399,562 ns
    against a projection of 17,000,000,000 ns (ratio 9,095,399,562/17,000,000,000); aggregate CPU
    6,534,332,000 ns under a 17,000,000 µs cap; group peak 7,543,115,776 B; child peak resident set
    39,828 KiB.
  - `actual-cross-build-20261009-v201` (`cargo test -p holonics --lib --no-run`, four cores): wall
    31,836,610,483 ns against 65,000,000,000 ns (ratio 31,836,610,483/65,000,000,000); CPU
    39,875,807,000 ns under 128,000,000 µs; group peak 2,471,559,168 B; child peak resident set
    2,176,900 KiB. It finished with one `dead_code` warning, `HeldContactVariation::advanced`
    (`crates/holonics/src/hnn/word/variation.rs:473`).
  - `cross-observation-diagnostic-20261009-v202` (the fixture, one core): wall 5,129,254,831 ns against
    31,223,102,736 ns (ratio 5,129,254,831/31,223,102,736); CPU 5,032,101,000 ns under 31,223,103 µs;
    group peak 30,855,168 B; child peak resident set 33,960 KiB.
  - Committed: the handoff, the validation, every stage's stdout and stderr (the largest is 28,588 bytes;
    whole, except the host paths projected below) and `diagnostic-v1/FILE_HASHES.json`.
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). Two committed files carry absolute host
  paths in their original bytes: the build stage's stdout and stderr.
  - They are published with the host prefixes replaced by `<queue-admission>/` (58 times) and
    `<cargo-registry>/` (50 times). The third placeholder declared in PROJECTION.json,
    `<repository>/research/records/receipts/`, does not occur here. No other byte changes.
  - Each original's sha256 and size stand beside its projected pins, and in the unchanged
    `diagnostic-v1/FILE_HASHES.json`.
  - The placeholders do not occur in the originals, so substituting the prefixes back restores the pinned
    bytes (checked for both files before commit).
- **Hashed only:** [diagnostic-v1/OMITTED.md](diagnostic-v1/OMITTED.md), 422 files (91,134,146 bytes):
  the 347 frozen source copies (9,893,723 bytes), the compiled test executable (75,869,712 bytes), seven
  admission records (580,766 bytes), 48 stage provenance files (4,659,024 bytes), 17 queue tools
  (126,723 bytes) and two mailbox handoffs (4,198 bytes). The source-review clearance, one of the admission
  records, and the two handoffs were read and withheld, not projected: they embed agent-to-agent message
  text, and the clearance names a mailbox path outside the three host prefixes.
- **Scope.**
  - Library compilation and one diagnostic, read once. The four contrasts are response-change readings at
    one compared station: a moved response is reported as moved.
  - Not graded, and not claimed: improvement, retention, masking versus erasure, unseen-family
    generalization, World-sensitive choice, and any learning acceptance.
  - No full test suite, clippy, doctest or workspace gate was rerun.

## The joined-source compilation at `089e126fa`

The diagnostic's acceptance is pinned to `6fd119c0d`, whose base predates main's later crates. Its join onto
published main `0d87efb27` was compiled before publication.
- Source `089e126fa` (full `089e126fa47d206fe27ee2b75d8274e582c8180e`, tree
  `2de53b2e9e4e0c59830d5b34e144a2714118d42b`), the merge of the packet `16752c791` onto `0d87efb27`.
- **Compilation** ([handoff](integration-compile-v1/HANDOFF.md),
  [validation](integration-compile-v1/VALIDATION.json)). `cargo test -p holonics --lib --no-run` freshly built
  the library-test executable from 350 frozen native inputs; compiler exit 0. Its only warning is the
  pre-existing `dead_code` method `HeldContactVariation::advanced` (`hnn/word/variation.rs`).
  - `diagnostic-join-prep-20261009-v211` (one core, no compiler): wall 9,354,248,328 ns against a projection
    of 17,000,000,000 ns; aggregate CPU 7,016,377,000 ns; child peak resident set 39,676 KiB.
  - `diagnostic-join-build-20261009-v211` (one Cargo job, four codegen CPUs, the 4 GiB reservation): wall
    37,280,624,560 ns against 65,000,000,000 ns; aggregate CPU 38,164,822,000 ns; group peak 2,385,571,840 B;
    child peak resident set 2,126,380 KiB.
  - Both stages ended quiescent and released; no limit was raised after launch.
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)): the build stage's stdout and stderr, over
  `<queue-admission>/` (57 and 1 times) and `<cargo-registry>/` (50 times in the stdout); checked as above.
- **Hashed only:** [integration-compile-v1/OMITTED.md](integration-compile-v1/OMITTED.md); the manifest lists
  404 files (92,147,618 bytes), among them the frozen sources, the executable and the withheld mailbox
  handoffs.
- **Scope.** A compilation of the joined library tests only: no fixture ran (`runtime_fixtures_executed` 0),
  the runtime diagnostic is not extended to the joined tree, and no learning acceptance is certified.
