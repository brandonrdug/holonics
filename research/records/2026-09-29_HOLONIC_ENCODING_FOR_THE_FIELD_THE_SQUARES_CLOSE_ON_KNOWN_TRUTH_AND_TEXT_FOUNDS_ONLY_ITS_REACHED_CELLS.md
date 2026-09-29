# Holonic Encoding for the field: the squares close on known-truth terrain, and text founds only its reached cells

**Date:** 2026-09-29. Refs #73, #63. **Scope:** the `hnn::encoding` loop of
[THE_REBUILD U6](../../docs/plans/THE_REBUILD.md#u6-the-text-chart), run against the acceptance
[pinned before it](2026-09-29_HOLONIC_ENCODING_FOR_THE_FIELD_PINNED_BEFORE_ITS_RUN.md) (`e0a957db`).
The build is `38cf65ac` and `397de664`. **Grade:** [proved-derived; formal-checked] for the squares
and the window-free read, [measured] for the terrain dimensions and the text receipts,
[agent-inferred] for the placement rule.

The computational object is the helical pair interaction. Of the winding guide's six objects the loop
touches four: the **helix** (the rotor steps and the selective clock, on which cells enter and
constituents are placed), the **pair** (the offset moment, now read whole), **faces and placement**
(`D`, each constituent's ports and its placement on a ring) and the **tower thread** (the carry chain
the selective clock and the crib's chart carry across rings). The cell holonomy and the tube stay
attached through `Field::holarchy` and the word.

## 1. What was built

- **The founding law**, `hnn::encoding::{PassageChart, Encoding}`. A passage chart is a finite chart,
  its admitted transports (known), the injection of the exterior cells, the receiving forms and the
  openings. Its minimal realization is founded by `receiver::population::birth::Closure` used twice,
  with no second copy of its algebra: forward from the openings under `T_a` (the closure over `T_aᵀ`,
  whose "forms" are the reached states), then backward from the receiving forms restricted to the
  reached span under `T_a` there. It returns the constituents with their ports and incidence, `U_a`,
  `D`, the founded injection `J = E B`, the Preimage Fibre (the reached directions `E` merges, and the
  cells no reached state separates) and a separator for a reading that does not factor.
- **The consumers' equations**, checked exactly on every reached basis state, every admitted
  transport and every founded cell (`Encoding::squares`): `D E = ρ`, `E T_a = U_a E` and the injection
  square `E(T_a x + B e_u) = U_a E x + J e_u`. The reduced recurrence `Encoding::reduced_moment` runs
  the encoded moment in the founded chart alone.
- **The port chart**, `hnn::field::PortChart`, read by `Ring::port`, by the card's lock chart (mounted
  from the host owner) and by the receiving letters' reader (which kept its own copy of
  `code mod d_g`; it now reads the chart). `hnn::encoding::found_ports` founds a text field's chart
  (§4). The residue chart stays only as the declared chart of synthetic fields.
- **The founded `E`**: a field on a founded chart opens `E_g` at the founded injection, each cell's
  column one half at its constituent's placement node (the real quadrature), and moves it only by
  deposition (`Constitution::initial`). A field on the residue chart keeps the sign sequence.
- **No window**: the open reads the pair port over the whole offset moment, normalized by its pair
  population, on the host (`SourceMoment::{offset_table, encode}`, `PairPort::apply_table`), in the
  reference's pullback and on the card (`hnn_pair_weights` over every earlier cell). The description
  codes the open's law as 2 and the port chart's kind.
- **Lean** `HNN/Encoding`: `injection_square` (composing
  `Physics/ReflectedBoundaryMemory.boundary_reduction_with_forcing`), `encoding_reduced_recurrence`
  and `moment_reduced_recurrence` (composing `Transport/SourceMoment.moment_append_one`),
  `encoding_separator` with `separator_refutes_factoring`, `encoding_descends_iff` and
  `factor_of_ker_le`, and the window-free read `whole_pair_read_{counts, offset_moment,
  population_invariant, tape_free, zero}` over `HNN/IndexedOpen`'s `pairPopulation` and
  `pairNormalized`. `HNN/Moment.SelectiveDecl` now declares its port chart as a field, so every
  selective-stepping law holds for the founded chart as for the residue.

## 2. Acceptance 1: the squares on known-truth terrain

Every square held exactly on every reached basis state (`hnn::tests::encoding`). The three terrains
are autonomous (they inject no exterior cell), so their injection square is empty; it is checked on a
source ring's moment chart, where each of the 7 cells is injected under each of the advances by 0, 1
and 2 ticks, on all 35 reached states. The founded dimension equals the rank of the emission's block
Hankel matrix, computed from the terrain's own emitted cells, on every terrain and draw:

| Terrain | Chart | Reached | Founded | Hankel rank | Observability alone |
|---|---|---|---|---|---|
| moiré `1/3, 1/4`, parity (one orbit) | 12 | 12 | 7 | 7 | 7 |
| moiré `1/4, 1/6`, parity (two orbits) | 24 | 12 | 7 | 7 | 7 |
| moiré `1/4, 3/5`, parity | 20 | 20 | 11 | 11 | 11 |
| copy ring `L = 8`, drawn over `|A| = 4` | 32 | 8 | 8 | 8 | 32 |
| copy ring `L = 8`, a period-4 word | 32 | 4 | 4 | 4 | 32 |
| rotor crib, ring 0 (`d = 5`), four draws | 25 | 3–6 | 3–6 | 3–6 | 9 |
| rotor crib, ring 1 (`d = 7`, under ring 0's carries), four draws | 245 | 16, 16, 32, 40 | the same | the same | 81–86 |

Disclosed: the crib's field declares the locks `{0, 1, 2}` and `{0, 3, 5}`, fixed in the test after a
first draw on the single notch `{0}` closed on a two-cycle that never stepped ring 0 (reached 2,
founded 2, Hankel 2); with four draws a ring the cribs step their rings.

"Observability alone" is Birth's closure of the receiving forms on the whole chart. On the moirés the
receiving forms are silent on no reached direction, so it already meets the emission; on the copy ring
and the crib it exceeds the emission by forms silent on the reached orbit, and the reached restriction
removes exactly them. This is the reachable quotient the Birth record found missing. The encoding also
reads every emitted cell (`D E Tᵗ x_0` is the cell's one-hot at every tick, carried by `Uᵗ` alone), and
on a source ring's moment chart the chart-level moment of a 200-cell passage stepped by the field's own
clock equals the reduced recurrence and `SourceMoment`'s phase counts carried to the lift.

## 3. Acceptance 2: no window

- **What the register was.** A shift register of the last `max Δ` raw cells (one cell on campaign 1,
  `Δ = {1}`). It entered the counts only as the earlier cell of each pair, and it entered the open as
  the address at which the pair port read one column of the offset counts: the open conditioned the
  source on its last `max Δ` raw cells, a depth-limited context window on the read. The counts
  themselves never discarded anything.
- **What it is now.** The same buffer, the offset moment's one-step state (Lean
  `Transport/SourceMoment.streamStep`'s previous value): a cell stays until its pairs are counted, and
  no receiver reads it. The open reads the whole offset moment.
- **The tests** (`hnn::tests::moment`). A drawn source of 4,096 cells on the chain field gives one
  moment (every phase count, offset count, buffer, lift point and open storage) ingested whole, cell by
  cell, at every split point of its first 128 cells and across 32 drawn splits. Over the same source,
  4,096 times the buffer's length, every cell is counted once (the phase counts' symbol totals are the
  source's histogram), every adjacent pair once (the offset counts' totals are its pair histogram), the
  pair population is `4,095`, and a source that differs only in its first cell has another moment.

## 4. Acceptance 3: text

[measured] The passage is the pin's: 6,148 bytes of the U6 choosing role (sha256 `39621d52…7fbc`),
4,096 development cells and 2,052 held out; no reserve, no evaluation window.

- **The founded constituents.** The exterior founding reaches the development part's 65 distinct
  cells, each its own constituent (founded dimension 65 = reached 65: the field knows no transport on
  the exterior chart but the identity, so no two reached cells merge). The plural fibre holds the 191
  codes the founding passage never met.
- **Their recurrence** (sorted anonymous counts; each hash is the SHA-256 of the list's text,
  `[587, 421, …]`):
  - development, 4,096 cells: the largest count 587, 56 of the 65 recur (a count of at least 2), 9
    occur once; `af85c0ca…ae0a`;
  - held out, 2,052 cells: 2,044 in 51 of the 65 constituents (47 recur), 8 in the fibre;
    `8cba155d…9a2c`.
- **Their placement** (constituents at each port, and those in the lock `{0}`):
  - ring 0 (`d = 5`): `[6, 11, 21, 10, 17]`; 6 in the lock, on 210 of the 4,096 development cells;
  - ring 1 (`d = 7`): `[2, 21, 15, 7, 11, 8, 1]`; 2 in the lock, on 188;
  - ring 2 (`d = 11`): `[2, 10, 11, 9, 1, 13, 0, 4, 9, 4, 2]`; 2 in the lock, on 193;
  - ring 3 (`d = 13`, no lock): `[31, 15, 5, 4, 2, 1, 0, 1, 0, 0, 1, 1, 4]`;
  - the fibre at port 1 on rings 0–2 and port 0 on ring 3.

  So the locks of rings 0, 1 and 2 admit 210, 188 and 193 of the 4,096 development cells, where the
  residue chart admitted 842, 413 and 522 (the bytes `≡ 0` mod 5, 7 and 11). The joint clock closed 2
  aeons over the passage (the first at cell 2,591) against 6 before, and located keys once against 4;
  every key fell back in both runs.
- **The moment's capacity** is unchanged, `n* = 6,148 = 2²·29·53`: the moment counts the exterior
  chart, so the port chart does not enter it. It is lossless by counting at 6,147 cells and lossy at
  6,148 (Lean `HNN/Moment.moment_capacity`; the test
  `campaign_one_capacity_is_certified_at_its_crossover`).
- **The charged code** of the field, the receiver's face on campaign 1's field (`hnn_exposure`, host):

| Reading | Before (`ac81f266`) | After (`38cf65ac`) | After − before |
|---|---|---|---|
| held out (2,052 cells), the field's face | `5463 + 7/16 + ε` | `5463 + 9/16 + ε` | `0 + 1/16 + ε` |
| held out, the tree's face alone | `5476 + 3/16 + ε` | the same | the same enclosure |
| held out, the field's part (field − tree) | `−13 + 4/16 + ε` | `−13 + 5/16 + ε` | |
| development (4,096 cells), the field's face | `13070 + 5/16 + ε` | `13069 + 2/16 + ε` | `−2 + 12/16 + ε` |
| `Kt`, the whole passage charged | `19995 + 12/16 + ε` | `20022 + 11/16 + ε` | `26 + 14/16 + ε` |

  Every reading is at the grain `L_R = 16`, `ε ∈ [0, 1/16)`. `Kt` charges the description, 1,439 bits
  before and 1,467 after: the founded chart's rule and the open's new law code add 28 bits; the chart
  itself is a causal function of the development cells the exposure codes, so its rule is its
  description.
- **The attribution** (a third run beside the pin, not in it: the after binary on the residue chart,
  `ports residue`, so only the open changed). It separates two opposite moves:

| Reading | Residue chart, window-free open | Its move against before | The founded chart's move against it |
|---|---|---|---|
| held out, the field's face | `5459 + 13/16 + ε` | `−4 + 6/16 + ε` | `3 + 11/16 + ε` |
| held out, the field's part (field − tree) | `−17 + 10/16 + ε` | | |
| development, the field's face | `13069 + 5/16 + ε` | `−1 + 0/16 + ε` | `−1 + 12/16 + ε` |
| `Kt`, the whole passage charged | `19992 + 3/16 + ε` | `−4 + 6/16 + ε` | `30 + 7/16 + ε` |

  The open without a window codes the held-out cells between `3 + 9/16` and `3 + 10/16` bits shorter
  than the window read (6 aeons and 4 key locations, as before). The founded chart with its founded
  `E_0` gives most of that back. The two parts of the founded change were not run apart: the chart
  (ring 0's lock admits 210 development cells against 842) and `E_0` (each code opens at one of `d_g`
  port directions, where the sign sequence gave each code its own).
- **Work and memory.** Before: 343,765 ms, peak 375,365,632 bytes. After: 563,095 ms, peak
  335,527,936 bytes, above the six-minute projection and below the twelve-minute stop. The host was
  shared (a load near 12 to 16 of its 24 cores from other work, and part of the run beside this loop's
  own attribution run and Lean build). The attribution run took 521,796 ms, peak 359,288,832 bytes,
  on the same shared host. By phase, the after run's word refine read took 120,578 ms against
  42,932, the re-read 131,072 against 51,631 and the pullback's compose 45,684 against 15,099: the
  whole offset moment's read touches every observed pair, where the indexed read touched one column.

## 5. Parity and the named changes

**The named changes.**
1. **The open's pair read**, on every field, host and card: the whole offset moment over its pair
   population, not the column at the buffer's address (the description's open law, code 1 → 2). The
   standing cut's recorded receipts (THE_REBUILD U1, U5) were measured on the indexed open; they are
   not re-measured here (a whole-cut exposure is hours, past this loop's projection), so they stand as
   the indexed open's readings.
2. **A text field's step classes**: the founded chart (`hnn_exposure`'s default `ports founded`).
   Every field declared without one, `FieldDeclaration::campaign_one` included, keeps the residue
   chart, and every synthetic test field reads it as before.
3. **`E_0` on a founded field**: the founded injection instead of the sign sequence. A residue field
   keeps the sign sequence.
4. **The letters' reader** reads the field's chart instead of its own residue. Nothing changes on a
   residue field, and campaign 1's letter family is cells-only, so its exposure does not read it.

**Parity.** The host suite passes (925). The GPU suite passed alone on the card under the lock (32 of
32), the card's open and word against the host reference on campaign 1's field among them, with the
whole-moment read in the kernel `hnn_pair_weights`. The card mounts its lock chart from `Ring::port`,
so a founded chart reaches it by construction; no card test runs a founded chart yet.

## 6. The verdict

- **Acceptance 1 holds.** Every square closed exactly, and the founded dimension equals the
  emission's Hankel rank on every terrain and draw. Where observability alone exceeds the emission
  (the copy ring, the crib), the reached restriction removes exactly the silent forms.
- **Acceptance 2 holds.** The moment is one across every split, and nothing of a source 4,096 times the
  buffer's length is discarded. The register is no longer read by the open.
- **Acceptance 3, reported plainly: unchanged overall.** The field's held-out code moved by
  `0 + 1/16 + ε` bits and its part against the tree by one sixteenth of a bit. The attribution run
  shows two opposite moves under it: the open without a window earns `−4 + 6/16 + ε` held-out bits,
  and the founded chart with the founded `E_0` costs `3 + 11/16 + ε` against the codec's residue chart
  and sign sequence. The founded chart relabels the passage's 65 reached bytes by their first arrival
  on the rings' clocks and merges the 191 it never met; the codec's byte values no longer choose the
  step classes, and the rings tick more rarely.
- **The blocker, by its measurement.** The founded chart with the founded `E_0` codes the held-out
  cells `3 + 11/16 + ε` bits above the residue chart with the sign sequence under the same open. On the
  exterior chart the field knows no transport but the identity, so the founding of a text passage
  reaches exactly its 65 cells and founds no class a recurring transformation would; it places them
  where the rings stood at first arrival, and it opens `E` at `d_g` port directions. The founding law
  is right where the transports are the field's own (the terrains); on text the recurring
  transformations are not transports the field knows, and must be located from the passage (keys by
  loop closure, the continuing motion `hnn::prediction` builds), not founded by closing forms under
  the rotor steps alone.

## 7. Owed

Two statements are owed in #62 (the text is in §8):
- the Hankel identification of the reach-restricted founding, which extends Birth's;
- the founded chart's causality over `HNN/Moment.SelectiveDecl`.

## 8. The #62 text

**HNN/Encoding (U6, `hnn::encoding`, `38cf65ac`), owed:**
1. *The reach-restricted founding meets the emission's Hankel rank.* For a passage chart with reached
   span `R` (the least `T_a`-invariant span of the openings) and founded forms `ψ` (the least
   `T_a*`-invariant span of the receiving forms restricted to `R`), `dim span ψ` is the rank of the
   emission's block Hankel matrix `[ρ(T_(w′) T_w x_0)]`. The route: the Hankel map is the observability
   map after the reachability map, its range is the observability map's image of `R`
   (`LinearMap.range_comp`), and the founded forms restricted to `R` span that image's dual. Measured
   on the moiré, a copy ring and the rotor crib (`hnn::tests::encoding`); it extends the Birth item
   (Birth's observability alone exceeds the emission by the forms silent on the reached orbit).
2. *The founded port chart is causal.* For the placement at first arrival
   (`hnn::encoding::found_ports`), each code's port on each ring is a function of the founding
   passage's cells before its first arrival alone, and the field reading the chart steps the founding
   passage exactly as the founding did; stated over `HNN/Moment.SelectiveDecl`, whose port chart is now
   a declared field. Tested in `hnn::tests::encoding`, not proved.
