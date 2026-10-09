# Publication note

This directory publishes the compact receipts of the helical code's step 3:
- loops 1 and 2: one forward pair deposit taking an equivariant port off its subspace, and the paired
  deposit that learns a located pair on both strands (source `ec92b6ea4`, Lean successor `9ba6fe000`;
  Refs #386 #73 #62);
- the changed read of the two period-60 release consumers (`f8ac14ba6`, tests only);
- loop 3, the paired source law (source `5c50803b1`, rebased unchanged onto this evidence).

The joins are [NATIVE_LEAN_JOIN.v1.json](NATIVE_LEAN_JOIN.v1.json) at `9ba6fe000`,
[NATIVE_LEAN_JOIN.v2.json](NATIVE_LEAN_JOIN.v2.json) at `f8ac14ba6`, and
[NATIVE_LEAN_JOIN.v3.json](NATIVE_LEAN_JOIN.v3.json) at `5c50803b1`.

- **Native at `9ba6fe000`** ([handoff](native-v1/HANDOFF.md), [validation](native-v1/VALIDATION.json)).
  - The gate passed: the build, the workspace check, the guard clippy and all 57 guard doctests.
  - 37 of 39 required fixtures passed: `hnn::paired` 18 (loop 1's measurement and loop 2's
    acceptance among them), `hnn::tests::executed` 11, three of the five pair tests of
    `hnn::tests::prediction`, and `tests/source_entrance.rs` 5.
  - The two period-60 release consumers were stopped by the aggregate-CPU guard at its stop
    threshold of 16,000,000 µs, within the 17,000,000 µs cap (a 1,000,000 µs margin). They had no
    completed test result and no reported failed assertion, so they were incomplete.
  - Committed: the handoff, the validation, every stage's stdout and stderr of at most 200,000 bytes
    (whole, except the host paths projected below), and `native-v1/FILE_HASHES.json`. The guard
    clippy's stdout (2,737,547 bytes) and the rest of the packet are hashed only in
    [OMITTED.md](native-v1/OMITTED.md).
- **Loop 1.** On the period-5 paired field, one forward `pair_deposit` of the located pair `0 → 2`
  moves column 2 and leaves its partner column 3. The partner read then refuses
  `Equivariance{ring 0, column 2, partner 3}`.
- **Loop 2, the acceptance, run once.** Both terrains were located by loop closure on the period-4
  paired field.
  - The alternating strand: located `(1, [(0, 2), (2, 0)])`.
    - The forward deposit alone is refused `Equivariance{ring 0, column 0, partner 1, row 0}` (the
      control).
    - The paired deposit reads the dyad images `[(1, 3), (3, 1)]` at `−δ`. Its slip goes from 8 to 0
      at `η = 2`, the consumer holds, the successor certifies and the partner face is exact.
  - The stepping strand: located `(1, [(0, 1), (1, 2), (2, 3), (3, 0)])`.
    - Three paired deposits certified, each equivariant with an exact partner face.
    - The slip fell from `16` to `10 + 715827883/2³⁰`, then `10 + 57264483/2³¹`, then
      `10 + 5260321/2³⁰`; the consumer did not hold.
    - Each column is one pair's consequence and another pair's dyad image, so the slip approaches
      the law's incompatibility with the pairing.
- **The changed read at `f8ac14ba6`** ([handoff](release-read-v2/HANDOFF.md)).
  - The two consumers were split into one drawn request per test, each phase's time printed, every
    acceptance unchanged. All four passed once, each below the unchanged guard (the 16,000,000 µs
    stop threshold within the 17,000,000 µs aggregate-CPU cap).
  - Generation took 13,354,665,257 to 14,584,650,014 ns a seed, and the whole test 13,595,929,000 to
    15,031,311,000 CPU ns.
  - The old two-seed tests held two generation units each. No limit was raised.
- **Lean** ([owner](lean-owner-v1/HANDOFF.md), [import](lean-import-v1/HANDOFF.md)).
  - `HNN/PairedDeposit` (source sha256 `ba6e3c0b`, 9,850 bytes) was kernel-checked: `lift_pow`,
    `reversal_identity`, `mul_commuting_stays`, `deposit_stays_equivariant`, `symmetrized_commutes`,
    `symmetrized_residual`, `rowNorm_smul_le` and `symmetrized_rowNorm_le`.
  - Its `HNN` import was checked too: 8 queries each, on standard axioms only.
  - Committed: each handoff, validation, kernel result, compiler stdout and stderr, and hash
    manifest.
- **Loop 3, the paired source law at `5c50803b1`** ([handoff](loop3-native-formal-v1/HANDOFF.md),
  [validation](loop3-native-formal-v1/VALIDATION.json)).
  - The development check, the fresh build, the guard clippy and all 57 guard doctests passed.
  - All 44 requested fixtures passed: the new fixture once, `hnn::paired` 18,
    `hnn::tests::executed` 11, three fast `hnn::tests::prediction` pair tests, the four period-60
    per-seed reads, `tests/source_entrance.rs` 5, and two `hnn::tests::constitution` save/restore
    tests.
  - `HNN/PairedDeposit`, with `projection_equivariant` and `projection_pairing` among its 10
    theorems, and its `HNN` import were kernel-checked: 10 queries each, on standard axioms only.
  - Committed: the handoff, the validation, every stage's stdout and stderr of at most 200,000 bytes,
    each Lean compiler output and kernel result, and the manifest. The guard clippy's stdout
    (2,734,827 bytes) and 1,141 other files are hashed in
    [OMITTED.md](loop3-native-formal-v1/OMITTED.md).
- **Loop 3's reading, once.** On the period-4 field founded with the paired source law:
  - the forward pair deposit alone keeps the port on the subspace, its slip falling from 4 to
    `7635570237/2³⁴`, just above `4/9`;
  - the paired deposit closes both strands (8 to 0 at `η = 2`);
  - the release's closed contacts, read through the founding prior, are `[1, 3]`, while the image's
    slip read against the field's declared port alone is nonzero;
  - general features at the normal law leave the successor on the subspace, with the chart at
    lattice `2⁻⁴¹` and certificate `761227/2⁵⁸` under the target `2⁻³⁵`;
  - the same samples on a plain law are refused at column 0 against partner 1.

  The general features reach the normal law directly; this is no end-to-end comparison through
  `compose_return` in a participating world.
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). Twenty-one committed files carry
  absolute host paths in their original bytes: the three joins, eight native and release-read stage
  files and eight of loop 3's, the Lean owner's compiler stdout and the import validation.
  - They are published with three host prefixes replaced by `<queue-admission>/`,
    `<repository>/research/records/receipts/` and `<cargo-registry>/`. No other byte changes.
  - Each original's sha256 and size stand beside its projected pins. For files inside a
    subdirectory, they are also pinned in that subdirectory's unchanged `FILE_HASHES.json`.
  - The placeholders do not occur in the originals, so substituting the prefixes back restores the
    pinned bytes.
- **Hashed only:** each subdirectory's `OMITTED.md`.
- **Scope.**
  - The paired deposit is claimed on the pair route, at located pairs, on a paired field whose port
    and prior are equivariant.
  - The paired source law is claimed at the normal law on the pair routes and on general features,
    with one founding prior across save and restore.
  - Not claimed: an end-to-end participating world's comparison, the quadratic's invariance in
    Lean (#62), the card's parity (#76) and the linking reading of closed strands.
  - The partner face keeps its carrier conditions (a unit transport, a unit tick, one source, no
    pair offsets).

## The quadratic at `54192a0ec` (Refs #386 #62)

This section publishes the compact receipts of the Lean statement loop 3 left owed (#62): the symmetrized
arrivals keep the normal law's quadratic.
- Source `54192a0ec` (`54192a0ecb3d3`, full `54192a0ecb3d3b4a6cc98afa648c072357326271`, tree
  `8fe82a01e70c7458834817c657b903d6bd46f533`, parent `5864e4f58`). It adds the theorem
  `HNN/PairedDeposit.projection_quadratic`. Its other changes are documentation: the module prose and one
  table row of the Lean owner, a `//!` block of `crates/holonics/src/hnn/paired.rs`, one atlas row and one
  record. The ten earlier theorems are untouched and operational Rust is unchanged (checked in the git
  diff against the parent).
- **Owner and `HNN` import** ([handoff](quadratic-owner11-import11-v1/HANDOFF.md),
  [validation](quadratic-owner11-import11-v1/VALIDATION.json)).
  - `HNN/PairedDeposit` (submitted source sha256 `58b9b720`, 13,285 bytes, equal to the git blob at the
    pin; 11 theorem declarations) was kernel-checked. The compiled source is the submitted source followed
    by 669 bytes, the 11 `#print axioms` queries (13,954 bytes, sha256 `9e3966f7`); nothing else is added.
    Compiler exit 0, compiler wall 10,548,438,889 ns, 11 of 11 queries reached
    ([kernel result](quadratic-owner11-import11-v1/owner/KERNEL_VALIDATION.json),
    [stdout](quadratic-owner11-import11-v1/owner/compiler.stdout)).
  - The 11 are the eight theorems named under Lean above (`lift_pow` to `symmetrized_rowNorm_le`), loop 3's
    `projection_equivariant` and `projection_pairing`, and the new `projection_quadratic`. Each depends on
    `propext`, `Classical.choice` and `Quot.sound` only. The compiler printed four unused-section-variable
    linter warnings (`reversal_identity`, `mul_commuting_stays`, `projection_pairing`,
    `projection_quadratic`) and no error.
  - The exact `HNN` import was checked too. The root `lean/Holonics/HNN.lean` of the pin (45,829 bytes,
    sha256 `3d446fe6`, equal to the git blob) has `import Holonics.HNN.PairedDeposit` at line 11. The
    consumer `PairedDepositImportConsumer` (703 bytes, sha256 `45fc8610`) imports that module and queries
    the same 11 selectors: compiler exit 0, compiler wall 6,977,577,603 ns, 11 of 11 queries reached, the
    three standard axioms only ([kernel result](quadratic-owner11-import11-v1/import/KERNEL_VALIDATION.json),
    [stdout](quadratic-owner11-import11-v1/import/compiler.stdout)). The full `HNN` or `Framework`
    aggregate was not compiled.
  - The current `HNN/FiniteDecrease` is joined as an accepted provider and not rebuilt. Its raw git source
    has sha256 `3a911d53f07a16df0e90c6ff47f1e12fd7600771501c8ecfda9b0af97c10ad4d`
    (`current_FiniteDecrease_raw_SHA256`, equal to the git blob at the pin); the provider copy is that
    source followed by `#print axioms` queries only. The imports are source-matched
    (`source_matched_imports_only`, `unchanged_dependency_rebuilt` false).
- **The statement.** `projection_quadratic`, graded in `VALIDATION.json` as the kernel-checked conditional
  restricted normal-law quadratic: over a commutative ring, with `Bᵀ = B`, `Σᵀ = Σ`, `B² = 1` and an
  admissible change `B D = D Σ`, `tr(D (Σ F Σ) Dᵀ) = tr(D F Dᵀ)`. Those four are its only premises;
  `Σ² = 1` is not one. The file's docstring reads it as the normal law's quadratic on the subspace
  reading `F_s = ½(F + Σ F Σ)` as it reads `F`. It is the statement the Scope above lists as not claimed,
  "the quadratic's invariance in Lean (#62)", now in this conditional form.
- **Stages** ([validation](quadratic-owner11-import11-v1/VALIDATION.json)). The packet holds four stages,
  all Lean (two preparations, two compilations) and no native stage. Each was accepted, quiescent and
  released, finished within its fixed projection, ran on one core under the 8,589,934,592 B group memory
  cap, and no limit was raised after launch.
  - `paired-deposit-lean-20261009-v203-prep`: wall 6,642,917,799 ns against a projection of
    17,000,000,000 ns (ratio 6,642,917,799/17,000,000,000); aggregate CPU 5,355,110,000 ns under a
    17,000,000 µs cap; group peak 579,121,152 B; child peak resident set 198,600 KiB.
  - `paired-deposit-lean-20261009-v203-compile`: wall 12,576,611,237 ns against 21,132,554,884 ns
    (ratio 12,576,611,237/21,132,554,884); CPU 7,429,071,000 ns under 17,000,000 µs; group peak
    4,666,949,632 B; child peak resident set 3,793,292 KiB.
  - `paired-deposit-import-20261009-v204-prep`: wall 5,380,366,232 ns against 17,000,000,000 ns
    (ratio 5,380,366,232/17,000,000,000); CPU 4,852,792,000 ns under 17,000,000 µs; group peak
    307,671,040 B; child peak resident set 198,576 KiB.
  - `paired-deposit-import-20261009-v204-compile`: wall 9,035,862,789 ns against 21,132,554,884 ns
    (ratio 9,035,862,789/21,132,554,884); CPU 5,579,651,000 ns under 17,000,000 µs; group peak
    2,405,392,384 B; child peak resident set 3,636,576 KiB.
  - Committed: the handoff, the validation, each Lean compiler's stdout and stderr (the stderr files are
    empty) and kernel result, every stage's stdout and stderr (the largest original is 4,892 bytes; whole,
    except the host paths projected below) and `quadratic-owner11-import11-v1/FILE_HASHES.json`.
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). Two further committed files carry absolute
  host paths in their original bytes: the owner's compiler stdout and the owner compile stage's stdout.
  - They are published with the queue admissions directory replaced by `<queue-admission>/` (4 times in
    each). No other byte changes. PROJECTION.json now lists 23 files: the twenty-one above, unchanged, and
    these two.
  - Each original's sha256 and size stand beside its projected pins, and in the unchanged
    `quadratic-owner11-import11-v1/FILE_HASHES.json`.
  - The placeholders do not occur in the originals, so substituting the prefix back restores the pinned
    bytes (checked for both files before commit).
- **Hashed only:** [quadratic-owner11-import11-v1/OMITTED.md](quadratic-owner11-import11-v1/OMITTED.md), 491
  files (302,542,125 bytes): the copied sources (130 files, 2,287,252 bytes), the compiled objects (262
  files, 195,993,863 bytes), the admission and sealed-import records (15 files, 101,429,455 bytes, of which
  the two `current-imports.json` are 49,728,414 and 51,234,175 bytes), 64 stage provenance files
  (2,699,295 bytes), 17 queue tools (126,723 bytes) and three withheld files (5,537 bytes): the
  source-review clearance for this commit and tree and the two mailbox handoffs. Those were read and
  withheld, not projected: they embed agent-to-agent message text, and the clearance names a mailbox path
  outside the three host prefixes.
- **Scope.**
  - Claimed: the conditional restricted normal-law quadratic, as the Lean statement above, kernel-checked
    in the owner (11 queries, standard axioms only) and read through the exact `HNN` import (the same 11
    queries, the same axioms).
  - Not claimed: World/material second variation, the full World comparison, the whole `HNN` or
    `Framework` aggregate, the card's parity (#76) and the linking geometry. The queue closed no issue or
    checklist.
  - The half in `F_s = ½(F + Σ F Σ)` is not part of the statement: the theorem is the trace identity
    over a commutative ring.
