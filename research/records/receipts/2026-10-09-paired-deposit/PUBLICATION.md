# Publication note

This directory publishes the compact receipts of the helical code's step 3, loops 1 and 2: one
forward pair deposit taking an equivariant port off its subspace, and the paired deposit that learns
a located pair on both strands (source `ec92b6ea4`, Lean successor `9ba6fe000`; Refs #386 #73 #62).
It also covers the changed read of the two period-60 release consumers (`f8ac14ba6`, tests only).
The joins are [NATIVE_LEAN_JOIN.v1.json](NATIVE_LEAN_JOIN.v1.json), at `9ba6fe000`, and
[NATIVE_LEAN_JOIN.v2.json](NATIVE_LEAN_JOIN.v2.json), at `f8ac14ba6`.

- **Native at `9ba6fe000`** ([handoff](native-v1/HANDOFF.md), [validation](native-v1/VALIDATION.json)).
  - The gate passed: the build, the workspace check, the guard clippy and all 57 guard doctests.
  - 37 of 39 required fixtures passed: `hnn::paired` 18 (loop 1's measurement and loop 2's
    acceptance among them), `hnn::tests::executed` 11, three of the five pair tests of
    `hnn::tests::prediction`, and `tests/source_entrance.rs` 5.
  - The two period-60 release consumers stopped at the unchanged fixed bound of 17 CPU seconds
    before any assertion, so they were incomplete.
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
    acceptance unchanged. All four passed once, each under the unchanged 17 CPU seconds.
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
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). Twelve committed files carry
  absolute host paths in their original bytes: both joins, eight native and release-read stage
  files, the Lean owner's compiler stdout and the import validation.
  - They are published with three host prefixes replaced by `<queue-admission>/`,
    `<repository>/research/records/receipts/` and `<cargo-registry>/`. No other byte changes.
  - Each original's sha256 and size stand beside its projected pins. For files inside a
    subdirectory, they are also pinned in that subdirectory's unchanged `FILE_HASHES.json`.
  - The placeholders do not occur in the originals, so substituting the prefixes back restores the
    pinned bytes.
- **Hashed only:** each subdirectory's `OMITTED.md`.
- **Scope.** The paired deposit is claimed on the pair route, at located pairs, on a paired field
  whose port and prior are equivariant. The general route's projection (loop 3), the card's parity
  (#76) and the linking reading of closed strands are not claimed. The partner face keeps its
  carrier conditions (a unit transport, a unit tick, one source, no pair offsets).
