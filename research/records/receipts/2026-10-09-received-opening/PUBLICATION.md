# Publication note

This directory publishes the compact receipts of the finite-decrease landing at a received opening
(source `2c5943c23`, tree `38c5e083`, a comments-only successor of the reviewed `3b888e599`; Refs
#73 #62). [NATIVE_LEAN_JOIN.v1.json](NATIVE_LEAN_JOIN.v1.json) joins the source, proof, native and
resource controls and outcomes.

- **Native** ([handoff](native-v1/HANDOFF.md), [validation](native-v1/VALIDATION.json)). The gate
  (check, guard clippy, all 57 guard doctests, build) and all 14 finite-decrease and 21
  physical-communication fixtures passed. Committed: the handoff and validation, the whole stdout and
  stderr of every stage at most 200,000 bytes, and `native-v1/FILE_HASHES.json`. Three stdouts are
  hashed only in [OMITTED.md](native-v1/OMITTED.md): the clippy stage (2,743,015 bytes) and two
  physical fixtures (218,996 and 400,329 bytes); their stderr is committed.
- **The received reading.** On 0279's carry after a full first Word (3 ticks, one contact moving),
  the landing re-entered the Word's own received opening through `θ′` at held momentum and admitted
  the candidate on its phase part, `Ok(Phase)`. Declared first reaches: C `2⁻¹¹` (certified `2⁻³³`),
  K `2⁻¹⁰` (certified `2⁻³²`), D `2⁻¹¹` (certified `2⁻³²`), reaching 2, 9 and 2 entries. The held
  momentum `C(θ′) w′ = π` and the finite crossing identity held exactly at every contact. The fixture
  reads the candidate and does not publish it
  (the development read, which is that fixture:
  [stdout](native-v1/stages/actual-received-development-20261009-v170.stdout)).
- **Lean** ([owner](lean-owner-v1/HANDOFF.md), [import](lean-import-v1/HANDOFF.md)).
  `HNN/FiniteDecrease` (source sha256 `3a911d53`, 15,377 bytes) and its `HNN` import were
  kernel-checked, 15 queries each, all on standard axioms only. Committed: each handoff,
  validation, kernel result, compiler stdout and stderr, and hash manifest.
- **Hashed only:** each subdirectory's `OMITTED.md`.
- **Scope.** The proposal is the existing fixed-rate covector; the exact finite admission alone
  decides. The opening's held-crossing term `J_open` with its initial-state certificate, an
  improvement over repeated learned publications, and the World, bank release and card are not
  claimed. The Lean identity at the producing constitution assumes `C` injective; the finite crossing
  identity needs no invertibility, and the Rust `held_rate` short circuit covers a singular `C`.
