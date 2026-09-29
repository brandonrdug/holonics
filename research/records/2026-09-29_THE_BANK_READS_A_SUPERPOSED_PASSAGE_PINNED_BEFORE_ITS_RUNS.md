# The bank reads a superposed passage, pinned before its runs

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the construction and the pins; [measured] for the development reads (§4), which
used development seeds and the text's choosing role only.

**Occasion.** The [parametron record](2026-09-29_THE_PARAMETRON_RE_DERIVED_THE_PUMP_READS_RELATIVE_PHASE_AND_THE_FLOQUET_CERTIFICATE_DECIDES_THE_LOCK.md)
§6 left open: the bank read two cells, each pumping its own section crossing, not the superposed
passage; the passage's reading is the monodromy through every crossing cell's pump, its spectrum at
the ring's parametric resonance. The [order repair](2026-09-29_THE_ORDER_REPAIR_ORDER_REACHES_THE_SECTION_ON_KNOWN_TRUTH_AND_TEXT_STAYS_AT_THE_BYTE_MARGINAL.md)
located its blocker there: a linear readout of superposed placed data separates them only when
`2D ≥ (n + m − 1)(|A| − 1)`, and their cross-spectrum needs the square law, which is the pump. This
loop builds that reading and uses it for generation.

## 0. The recorded failures this work could repeat, and how each is avoided

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **1, an authored routine.** No class is computed by a routine. The bank's members are the
  parametron record's declared bank, unchanged (one node, axis `1`, steps `i^j`, `p = 5/8`); the
  cells enter through the constitution's source port `E` at its cut; a station's class is the
  candidate whose placement the bank's own Floquet growth reads strictly highest. Nothing names a
  lag, a class shift or the terrain's rule.
- **2, recitation or an index.** The bank reads the receiving ring's storage: the source moment's
  placement (phase-binned counts through `E`), never the cells as a tape; no window, no pair table,
  no copier. The held-out requests are fresh draws.
- **3, text as the exception.** Every stream enters as the ring's storage through `E` at its residues;
  an image's pixels at their scan ticks and an acoustic stream's samples at theirs cross the section
  as a text's bytes do, and a periodic component of any stream is a spectral line (§1, known truth).
  The text run changes only the declared period (`D = 35`, where only the standing member's period
  divides the turn).
- **4, the byte marginal.** Named before the run as text's expected blocker (lesson 3): the request's
  moment is normalized over its population, so at `n ≫ D` its 35 residue bins hold the byte
  marginal's image, "the table without its index"; the bank reads that superposition, so text's
  sections are expected to read little of their requests.
- **7, bits read as progress.** No code length is reported for the bank's sections (it has none);
  the training code is the order repair's own, beside the runs.
- Also **5** (nothing new is deposited; the training is the certified deposition as committed),
  **6** (fresh requests), **9** (every bound fixed here, none moved), **11** (the reading is stated
  in residues, modes and spectral placement: the ring's turn, its crossings, its monodromy).

## 1. What is built (`e70e992f`)

`hnn::ring`'s header, "The passage's monodromy", and `hnn::prediction`'s, "The bank reads the
superposed passage", state it whole.

- **The pump.** The receiving ring holds the passage superposed, `Σ_k P^(τ − c_k) E u_k`. As the ring
  turns on, node `d − 1 − t` crosses the section at tick `t` (the passage in its own time order
  around the turn), and each crossing pumps each member: the reflection at the node's placed
  amplitude, scaled by it (`PumpSchedule::placed`), each tick certified by its signed form.
- **The monodromy.** The ordered product of the turn's pumped ticks, carried as `N/Δ` on integers
  (`ReceivingBank::read_turn`). Its growth is enclosed exactly on either side of one
  (`lower ≤ ρ < upper`, relative width `2^(−g)`), each bisection step the Schur–Cohn test on
  `det(Δμ − N)`; the bracket is attained on a shifted copy and certified by two exact tests. The
  certificate (`certify_turn`) attains the metric on a rounded monodromy and certifies it by inertia
  on the exact one, and runs the executed turn with every balance checked.
- **What it reads.** Lean `HNN/FloquetPassage`: two crossings separated by the ring's transport
  compose to the turn by their relative phase less the transport, `R_u Rot_v R_w = Rot(u v̄ w̄)`; one
  crossing more pairs the new crossing with every earlier one; at a whole turn the second order's
  trace is the passage's power spectrum, `2 Re Σ_t w_t conj(Σ_(s<t) w_s) = |Σ w|² − Σ |w|²`.
- **The bank.** Members whose pump's period divides the turn; the joint growth is the largest
  member's. Known truth (the owner's tests): on a line of unit cells stepping one quarter-turn class
  a crossing, the lock pattern names the class (the half-turn partner certified silent), and with a
  crossing left open the candidate completing the line reads the joint growth strictly above every
  other: the lock's flip continues a spectral line.
- **Generation** (`generate_by_bank`). Each refinement reads, for every unlocked station and every
  class, the bank's joint growth with that candidate and the locked data placed
  (`BankPlacement::storage`, held to `injection` exactly); a station's reading is the lock's flip
  (its top strictly above every other candidate, `θ = a/(a + K) > ½ ⇔ a > K`, and the bank locked);
  the stations of the largest gap lock, each certified; the section is released at width zero
  through `receiver::release`, or held.
- **The learning path.** The training is the order repair's certified deposition, unchanged; the
  bank reads its trained `E`. [agent-inferred] The bank's reading enters no comparison: no covector
  of the lock's decision reaches `E` or a member's pump, and the field's words run their resonators'
  declared pumps, never one the passage modulates. The certified step reading a pumped ring's reach
  (main, `57b1d9a8`) does not change that: its path is linear in the data. The run measures what
  the training reaches in the bank's reading (§2, acceptance 2's diagnostic).

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects the loop touches four:
- **the helix**: the pump's clock `a² s^t` and the placed phases (the residues' rotations);
- **the cell holonomy**: the passage's monodromy over one turn;
- **faces and placement**: the bank's locked faces and the section's placement;
- **the tube**: the section's span, the turn's `d` ticks.

The pair (two crossings composing through the transport) and the tower thread (the growth enclosed
at a dyadic grain) stay attached.

## 2. The pins

Every run runs once, on the host, in release, sequentially, at the build `e70e992f`, each bounded
externally at its projection's upper end.

**Acceptance 1: the exact checks.** On every training refinement the balance closes, the pairing is
exact, the commit's balance closes, the committed energy bound holds, and every unreached locus is
unchanged at every deposit (the order repair's checks). On every lock of the bank's generation,
every member's Floquet certificate holds at the locked reading's growth and every tick of the
executed turn closes. **Passes** when every count equals its total.

**Acceptance 2: known truth** (`hnn_prediction -- order2 bank`). The order-2 terrain as the order
repair pinned it: `x_t = x_(t−2) + 1 (mod 4)` after 40 drawn cells, 512 training requests
(`Draw::new(2_026_092_901)`, partitions `2_026_092_904`), 256 fresh requests
(`Draw::new(2_026_092_902)`), the field of `D = 60 = 3·4·5`. The continuation stations read by the
bank's locks, reported as exact counts (stations right of 2,048, exact sections, released, by
station) against:
- the order repair's 866 of 2,048 (its linear readout; the same run reports its generation on the
  same constitution as a control);
- the static marginal's 512 and the per-station marginal's 520.

The bank is the parametron record's (`p = 5/8`), all four members (every step's order divides 60),
the turn read at the relative grain `2^(−16)`. Beside it, the diagnostic of the learning path: the
first 32 held-out requests generated by the bank on the declared opening (`Constitution::initial`),
the stations equal to the trained constitution's, and right.

**Acceptance 3: text** (`hnn_prediction -- text .local/cuts/curated-u6-passage-cut.bin <owner-only
file> bank`). The U6 split's choosing role (`development_families.py U6`; the cut `c6e51a35…0816`):
its 385 request relations, two passes (the pinned bound 1,024 exceeds them), the order repair's text
declaration (`D = 5·7 = 35`, `|A| = 257`, `m = 32`). No `--read-reserve` is passed, and the
evaluation window is never read. The 8 validation requests F0's rule selects
(`RELEASE_SEED = 20_260_929`) are generated by the bank (its standing member alone: no other
member's period divides 35), their sections written whole to the owner-only file and shown in the
conversation only, with nothing beside them. Bits (the training code) are reported beside the run,
never as its success.

**Acceptance 4: the projections** (from §4). A run that reaches its bound is reported incomplete
with its partial evidence and is not rerun with a larger bound.

| Run | Projection | Internal stop | External bound | Peak resident set |
|---|---|---|---|---|
| `order2 bank` | training 150,000–300,000 ms; the order repair's generation 60,000–150,000 ms; the bank's generation 900,000–1,400,000 ms; the opening's diagnostic 100,000–200,000 ms | training 540,000 ms; the bank 1,500,000 ms, read between chunks of 32 | 2,400,000 ms | about 1,200,000,000 bytes |
| `text … bank` | training 350,000–540,000 ms; the bank's 8 sections 600,000–1,500,000 ms | training 540,000 ms; the bank 1,500,000 ms, read between chunks of 4 | 2,400,000 ms | about 1,000,000,000 bytes |

## 3. What is expected, named before the runs [agent-inferred]

- **The order-2 terrain's rule is not in the passage.** The request is 40 uniform cells; the rule
  relates a station to the cell two back. A declared bank reads the passage's own spectral lines and
  continues them (§1); nothing in the request's spectrum names the rule, and locating which relative
  phase at which lag the continuation keeps is learning, which does not reach the bank (§1). The
  count is expected near the marginals.
- **Text reads its byte marginal** (failure 4's located cause, named above).

## 4. The development reads (development seeds 21 and 22; the text's choosing role only)

Order-2, 64 training requests, 32 evaluated (256 stations), the order repair's training:

| Bank | Stations right | Released | Every lock certified, every turn closed | The order repair on the same | Marginals | Bank's generation |
|---|---|---|---|---|---|---|
| `p = 1` | 63 | 32 of 32 | 1,024 of 1,024; 61,440 of 61,440 | 109 | 64, 64 | 125,486 ms |
| `p = 5/8` | 63 (by station 6, 8, 4, 6, 9, 7, 13, 10) | 32 of 32 | 1,024 of 1,024; 61,440 of 61,440 | 109 | 64, 64 | 133,605 ms |

At `p = 5/8` the locked readings' growth ran from `43621/2048` to `128407`, the least margin over a
runner-up `7891/4096`; the peak resident set was 898,322,432 bytes. [agent-inferred] **The
choices**: `p = 5/8`, the parametron record's declared bank unchanged (the two strengths read alike);
the relative grain `2^(−16)`, every lock decided far inside it.

Text, one pass over 32 choosing pairs, then the bank's sections for the first two choosing requests
(already read; bytes to an owner-only file, not reported): training 12,115 ms; both released at 32
bytes; 64 refinements, 271,392 turn readings, 64 locks certified and 2,240 of 2,240 ticks closed, in
180,305 ms; peak 613,830,656 bytes. The 8 validation sections are about four times its readings.

The realization was measured before the pin: on a 60-tick turn with 40-bit placed amplitudes the
exact half-plane count took 5,967 ms a turn of four members; the Schur–Cohn test on integers with an
attained bracket, 796 ms; on the integer product and characteristic polynomial the reading costs
about 10 ms a member and the certificate about 1,500 ms a lock of four members. The enclosures were
equal on every path.
