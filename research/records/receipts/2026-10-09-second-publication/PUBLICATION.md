# Publication note

This directory publishes the compact receipt of the second learned publication's reading (source
`8121219ef`, tree `6caa819c`: one fixture added atop the received-landing evidence `2a0976472`; Refs
#73). [SECOND_PUBLICATION_JOIN.v1.json](SECOND_PUBLICATION_JOIN.v1.json) joins the source, native
and resource controls and outcomes.

- **Native** ([handoff](native-v1/HANDOFF.md), [validation](native-v1/VALIDATION.json)). A fresh
  build, the affected check and the guard clippy passed, and the fixture
  `a_second_learned_publication_is_read_at_its_received_opening` ran once
  ([stdout](native-v1/stages/actual-second-runtime-20261009-v175.stdout)). The production source and
  the Lean owner are the received-landing pin's, unchanged, so its 35 fixtures, 57 doctests and Lean
  checks were not rerun. Committed: the handoff, validation, every stage's stdout and stderr of at
  most 200,000 bytes, and `native-v1/FILE_HASHES.json`; the clippy stdout and the rest of the packet
  are hashed only in [OMITTED.md](native-v1/OMITTED.md).
- **The reading: 4 of 4.** On 0279's own task the first call landed at Rest and published; the
  second call repeated the observation at the received opening the first left, landed (both
  `Ok(Phase)`) and published, at first reaches C `2⁻¹³`, K `2⁻¹⁴`, D `2⁻¹³`.
  1. Each family committed exactly one lattice unit of 36 against the first publication's material:
     C at entry 26 by +1, K at entry 28 by −1, D at entry 25 by −1.
  2. The compared station's later response differs from the control holding the first publication's
     material at the same entering end, in 8 realified coordinates.
  3. The world and material energy closes exactly; the held-work and chain residuals are 0.
  4. A cold restore reproduces the material, carry and current, and the same later response and
     difference.
  The returned `e` is nonzero in all 40 coordinates at tick 6.
- **Time and memory.** The fixture's complete stage took `3,777,887,842 ns` under the fixed
  `17,000,000,000 ns` stage projection, a measured/projected ratio of exactly
  `3,777,887,842 / 17,000,000,000`; group peak `41,435,136 bytes`, child peak RSS `34,180 KiB`. No
  limit was raised.
- **Scope.** One declared fixture with two publications on one observation. It is not general
  learning or generalization across families, and it claims neither the opening's held-crossing
  term `J_open` with its certificate, nor the World, bank release, card or generation.
