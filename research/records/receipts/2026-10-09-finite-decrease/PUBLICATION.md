# Publication note

This directory publishes the compact receipts of the finite-decrease landing law (source `d81d39d3b`,
tree `c130586f`; Refs #73 #62).

- **Native** ([handoff](native-v1/HANDOFF.md), [validation](native-v1/VALIDATION.json)). Committed:
  - the gate's handoff and validation (check, guard lints, all 57 guard doctests);
  - every one of the 11 finite-decrease and 21 physical-communication fixtures' whole stdout and
    stderr, and the development read;
  - `native-v1/FILE_HASHES.json`.

  The actual 0279 complete return admitted the phase candidate at `η = 2⁻¹⁰`. All four learned-change
  criteria read PASS on that fixture
  ([stdout](native-v1/stages/actual-l-physical-21-20261009-v156.stdout)).
- **Lean** ([handoff](lean-owner-v1/HANDOFF.md)). `HNN/FiniteDecrease` (247 lines) kernel-checked, with
  twelve axiom queries, all standard. Committed: its handoff, validation, compiler stdout and stderr,
  and its hash manifest.
- **Import** ([handoff](lean-import-v1/HANDOFF.md)): the `lean/Holonics/HNN.lean` import consumer is
  kernel-checked, with twelve standard axiom queries.
- **Hashed only:** each subdirectory's `OMITTED.md`.
- **Scope:** one declared comparison on one fixture, admitted by its own same-Rest re-read. This is
  neither general learning nor a uniform-curvature certificate. Received openings, held variation
  and charted operands still refuse.
