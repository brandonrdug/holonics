# Holonic Encoding for the field (`hnn::encoding`), pinned before its run

**Date:** 2026-09-29. Refs #73, #63. **Scope:** the `hnn::encoding` loop of
[THE_REBUILD U6](../../docs/plans/THE_REBUILD.md#u6-the-text-chart), under the record
[the text chart is the one machine's field](2026-09-29_THE_TEXT_CHART_IS_THE_ONE_MACHINES_FIELD_TORI_HELICES_EGGS_AND_TUBES_ARE_ONE_FAMILY.md)
§3 and the governing law "No catered machinery"
([antipattern record](2026-09-29_ANTIPATTERN_CATERED_MACHINERY_A_TASKS_SOLUTION_ROUTINE_NEVER_STANDS_IN_FOR_LEARNING.md)).
The claim and its acceptance (§2) and the text run's passage and projection (§3) are committed
before any measured run. The receipt is a later record.

The computational object is the helical pair interaction. Of the winding guide's six objects the
loop touches four: the **helix** (each ring's winding with carry, on which the source enters), the
**pair** (the pair port and its offset moments), **faces and placement** (the readout `D` and each
constituent's placement on a ring) and the **tower thread** (the carry chain across the rings, which
the selective step reads). The cell holonomy and the tube stay attached through `Field::holarchy`
and the word.

## 1. What falls short, and the smallest form

[source-inspected] Two things fall short today (Brandon, September 29: "Why is there a context
length? That's contamination"):
- the field's `E_g` is a learned linear map of the one-hot exterior chart, opened at a declared sign
  sequence (`hnn::constitution::Constitution::initial`), and its step classes are
  `code mod d_g` (`hnn::field::Ring::port`): the codec chooses the classes;
- the open reads the pair port only at the address the moment's shift register supplies
  (`HNN/IndexedOpen`, ruling B): the open conditions on the last `max Δ` raw cells, a depth-limited
  context window on the source's read.

[definition; agent-inferred] The smallest form built in this loop:
1. **The founding law** (`hnn::encoding`): a passage chart (a finite chart `ℚ^n`, the admitted
   transports `T_a`, which are known, the injection `B` of the exterior cells, the receiving forms
   `ρ`, the openings `x_0`) founds its minimal realization with the one owner of the closure,
   `receiver::population::birth::Closure`, used twice: forward from the openings and the injection
   under `T_a` (the reached span `R`), then backward from `ρ` restricted to `R` under `T_a|_R` (the
   founded forms). It returns the founded constituents with their ports (the chart states they read)
   and incidence (the pattern of `U_a`), `U_a`, `D`, the founded injection `J = E B`, and the
   Preimage Fibre (the reached directions `E` merges, and the exterior cells no reached state
   separates). Its consumers' equations are checked exactly on every reached basis state:
   `D E = ρ`, `E T_a = U_a E` and the injection square `E(T_a x + B e_u) = U_a E x + J e_u`.
2. **The port chart**: the field's step classes are read from the founded constituents of the
   exterior chart on a founding passage, not from `code mod d_g`. On the exterior chart the field
   knows no transport but the identity, so the founding reaches exactly the passage's classes, and
   the codes the passage never separates are one plural fibre. Each founded constituent is placed
   on each ring at the ring's phase class at its first arrival, read on the field's own selective
   clock as the chart is founded (the placement of the winding guide; causal: a code's port reads
   only the cells before its first arrival). The plural fibre is placed at the least port outside
   each ring's lock, so it steps no ring by its lock (it carries no founded transport). The codec
   supplies only the exterior alphabet and its decoder. `code mod d_g` stays the declared chart of
   the synthetic test fields whose drawn codes carry no source structure; it is never the text
   chart again.
3. **The founded `E`**: on a field whose port chart is founded, `E_g` opens at the founded injection,
   each code's column one half at its constituent's placement node (the real quadrature), and moves
   only by deposition. The moment is `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹ E_g(u_k)` read through it.
4. **No window**: the open's pair term reads the whole oriented offset moment over its pair
   population (Lean `HNN/IndexedOpen.{pairPopulation, pairNormalized}`), never a column at a raw
   cell's address. The shift register stays only as the offset moment's one-step buffer (Lean
   `Transport/SourceMoment.streamStep`'s previous value): it holds a cell until its pairs are
   counted and is read by no receiver.
5. **Lean** `HNN/Encoding`: `injection_square`, `encoding_reduced_recurrence`, `encoding_separator`
   and the window-free read, or each owed statement named in #62.

## 2. The acceptance

1. **The squares close exactly on known-truth terrains**, each built of the field's own objects:
   - the moiré (`holarchy::terrain::Moire`'s gratings, through `TransportBirth::moire`'s chart),
     at rates `1/3, 1/4` (one orbit of the joint torus) and at rates `1/4, 1/6` (two orbits);
   - a copy terrain: a closing rotor ring of period `L = 8` whose nodes hold drawn cells over
     `|A| = 4`, and one whose stored word repeats with period 4;
   - the rotor crib (`holarchy::terrain::rotor_crib`) on ring 0 (`d = 5`) and on ring 1 (`d = 7`,
     read under ring 0's carries) of a declared field, under a drawn key and plugboard.

   On each, `D E = ρ`, `E T = U E` and the injection square hold exactly on every reached basis
   state, and the founded dimension equals the emission's observable dimension: the rank of the
   emission's block Hankel matrix, computed from the terrain's own emitted cells and not from the
   founding. On the two-orbit moiré the observability-only founding (Birth's closure on the whole
   chart) is reported beside it, so the reachable quotient's effect is read.
2. **No window.** A test shows that the moment of a long source equals the moment accumulated
   across any split of it (counts, offset counts, the lift point and the open), and that nothing of
   the source is discarded by length: every cell is counted once in every source ring's phase
   counts, and every pair at every declared offset in its offset counts, over a source longer than
   the register many times over.
3. **On text**, the U6 split's choosing role only (never `--read-reserve`, never the evaluation
   window), the passage of §3:
   - the founded constituents' count and their recurrence, as counts and hashes;
   - the moment's capacity `n*`;
   - the charged code of the field on the passage's held-out cells, and beside it, not as a control,
     the field's code before the change on the same passage.

   Illegible or unchanged is reported plainly. No claim beyond these readings is made.

## 3. The text run's passage and projection

- **The passage** (`.local/cuts/u6-encoding-probe.bin`, owner-only): 6,148 bytes of the U6 choosing
  role's flat cut (`curated-u6-choosing-flat-cut.bin`, sha256 `eab73259…5dd2`), bytes
  `[453655, 459803)`: the last 4,096 development bytes before that cut's held-out range and its
  first 2,052 held-out bytes. Its sha256 is `39621d52…7fbc`; the development part's `25bcc994…a94b`,
  the held-out part's `88474d87…5e80`. Its manifest names the reserve as excluded. Counts only: the
  development part reaches 65 distinct bytes; 6 held-out bytes are unreached by it, on 8 held-out
  cells.
- **The founding passage** of the port chart is the passage's own development part, read on the
  field's own clock from its declared initial configuration.
- **The runs**: `hnn_exposure -- cut-file <passage> cells all` on campaign 1's field, on the host:
  before the change at the base commit `ac81f266`, and after it with the founded port chart. The
  population is `n* = 6,148` either way.
- **Projection** (F2's host exposure of 6,148 cells took 363,330 ms): about six minutes a run and
  within the probe budget of 20 GB. A run past twelve minutes is stopped and reported incomplete.
