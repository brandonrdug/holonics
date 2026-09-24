# Lessons from the workbench and Athena prototypes

**Date:** 2026-09-24. **Retired code:** readable at `14cfb22a` (§5). **Issues:** restructure
[#63](https://github.com/brandonrdug/holonics/issues/63); measured outcomes in
[#16](https://github.com/brandonrdug/holonics/issues/16), [#17](https://github.com/brandonrdug/holonics/issues/17), [#18](https://github.com/brandonrdug/holonics/issues/18) and [#61](https://github.com/brandonrdug/holonics/issues/61).

[project-postulate] Brandon, September 24: the Holonics workbench "was never perfectly
functional or useful", and the Athena examples are "drafts or prototypes" that "have not
produced anything perfect". Any later workbench or Athena application is rebuilt on the
restructured library. The code is retired; this record keeps what did and did not work. It adds
no measurement: every number comes from the cited record, issue or source at `14cfb22a`. Object
names follow [ELEMENTARY_OBJECTS](../../docs/ELEMENTARY_OBJECTS.md).

## 1. The prototypes

| Prototype | Dates | Purpose | Last state |
|---|---|---|---|
| `holonics` CLI, `applications/holonics-workbench` | Sep 1–24 | Local command application: variant workspaces and a Ratatui TUI (Sep 1), `hna run/infer/train` over inherited Gemma/SKE material (Sep 4), then JSONL stream sessions | `hna {native,mathematical,wave,coupled-wave,field}-session`, `hna wave-control`, `diagnostic {status,capabilities,soulkiller}`. The TUI was rejected; workspaces left in `814157ad`, the `hna` model commands in `a69b505f` |
| `HnaStream`, `crates/holonics-hna/src/stream.rs` | Sep 5–24 | JSONL delivery over one continuing native session per process | 24 actions shared by five session kinds |
| `athena_field` | Sep 14 | First constituted-field model: D/M training on a joint quarter-turn of three complex boundary coordinates, rest and remount | Returned its scoped task |
| `athena_geometric_spec`, `support/linked_torus_field.rs` | Sep 20 | Linked-torus `FieldSessionSpec`: one ring junction per source cell, `Utf8Nibbles` or Unicode-scalar codec | Superseded by the generator machine; kept as a legacy control |
| `helical_field_generator` | Sep 20 | Source-conditioned field on the `se(3)` screw bracket | Returned the exact held bracket and its reuse |
| `athena_exposure_field`, `src/alpha/exposure.rs` | Sep 20–22 | Walk the private conversation exposure through the field session, with the cursor in the checkpoint and exterior bit readings | Ran the full-capacity and generator-machine charts; no useful reply |
| `athena_generator_spec`, `support/generator_machine.rs` | Sep 21 | Declare the fixed generator machine: generators, source capacity, receiving phases and terminal phase | Six-cycle control 0/6 |
| `athena_boundary_material` | Sep 21 | Cold inspection of persisted E_in/R_text normal laws before and after an observed return | Located the 18/388 retention failure |

## 2. What worked

**W1. Delivery that never repeats native work.** [established-bounded; measured] `HnaStream`
reads one complete request, executes it, and drains and flushes the event before reading the
next. Packet boundaries create no occurrence. A failed write keeps the encoded response; a new
connection replays the pending event under its sequence number; an incomplete input tail
survives restart. The [HNP3 return](2026-09-05_HNP3_THE_STREAM_RETAINS_PARTIAL_INPUT_AND_REPLAYS_OUTPUT_WITHOUT_REPEATING_DEVELOPMENT.md)
compared complete successors after normal streaming, split-input restart and a broken pipe with
replay. Object: **Receipt**: one reception returns one receipt, delivered once.

**W2. Byte-identical resume as the durability check.** [established-bounded; measured] Split
and uninterrupted exposure walks produced identical 3,594,009-byte checkpoints (Sep 20) and
identical 2,441,477,554-byte full-capacity checkpoints (Sep 21), each with exactly one paired
update. The generator session resumed to byte-identical state after intervening learning and
codec growth. A source frame was acknowledged only after its native use, and the cursor was
saved in the same checkpoint as the model. Object: **Deposition**: the constitution changes
once for each comparison that reached it.

**W3. A cold, source-qualified conversation source.** [established-bounded; source-inspected]
`alpha/exposure.rs` frames one occurrence at a time, never a request with its future response.
The recorded reply arrives later as an observed comparison, never as gold, and evaluation
targets never chose the codec or priors. `recorded_context` resolves parents through an
incremental prior-prefix index (4,092 wire bytes scanned, two parents fetched on resume). A
request larger than the aperture is counted (`request-over-aperture`), not trimmed. Reports
count fifteen declared outcome labels and never quote a native refusal; private diagnostics
are opt-in and owner-only; `episode.py` keeps `input.json` and `assessment.json` apart.
Object: **Receiver and receipt**: a report is a field of counts over a declared partition.

**W4. Mathematics through the same field.** [established-bounded; computational-witness] The
mathematical session streamed exact bilinear construction, application, receiver binding,
composition and product release as JSONL. `helical_field_generator` returned the exact held
screw bracket `(-24,-22,7,47,52,6)`, a plural condition family with two free directions, and
reuse of the formed generator at another condition
([record](2026-09-20_NATIVE_INCIDENCE_FORMS_AND_REUSES_THE_HELICAL_GENERATOR.md)). Through the
76,599-site field, code emitted from the inferred three-product factor graph compiled and
passed four exact complex-product cases. Objects: **Generator** (inferred, then reused under a
changed condition) and **Pair contact** (the screw bracket).

**W5. Phase-carried moments instead of a tape.** [established-bounded; measured] After the
retention audit the source accumulated in closed form, `q_N = U^N q₀ + Σ_k L^(N−1−k) I E(u_k)`,
and the incident word ran once. One pending comparison kept 3 resident sections and 2,936 bytes
at N = 2, 8, 32 and 128. The source-covector radius at N = 128 was 3.6e-10, where step-wise
application had refused. `Transport/SourceMoment.lean` proves the closed form and the tape-free
adjoint ([record](2026-09-22_THE_SOURCE_ENTERS_AS_A_MOMENT_AND_THE_FIRST_RETURN_IS_MEASURED_IN_BITS.md)).
Objects: **Generator** (the source word is a phase-carried address) and **Deposition**
(retention is a quotient).

**W6. Pair material as fixed template plus current amplitude.** [established-bounded; measured]
Positive amplitudes `D_a = ρ_a B_a`, rebuilt from one template, held the field rest at 6,830
bytes across repeated updates with zero completed return records; stale publication was refused
([record](2026-09-22_PAIR_MATERIAL_LEARNS_WITHOUT_A_COMPLETED_UPDATE_ARCHIVE.md)). Objects:
**Pair contact** and **Deposition**.

**W7. Fixed receiving ports and phase receiving.** [established-bounded; measured] Placing
response slots after the source extent made 120 of the first 129 returned characters match old
source cells. A `response_port_start` independent of request length removed that (slots
76,087–76,598 for both short and full sources). The generator machine read an aperture A at
A+1 receiving phases with one shared stop map and no per-position material block. Object:
**Receipt**: a response position is a receiving phase.

**W8. Numerical repairs that kept the certificate.** [established-bounded; measured] Selecting
on real support potentials rather than midpoints of [0,1] faces turned 513 identical midpoints
(an empty response) into a length-388 reply. Chebyshev semi-iteration under the independent
residual certificate cut the response radius from about 40,158 to 0.00154 on the same
material. A factor-ball journal replaced a scalar bound that overflowed the signed-128 carrier
at grain 96. Reusing repeated `(W_row,B_row)` witnesses completed remount in 99.483 s, where an
earlier attempt was unfinished after 396 s. Object: **Ratio**: an exact representation keeps its
remainder.

**W9. Full-size runs found defects small tests missed.** [established-bounded; measured] A
1,231-row request exposed row buffers sized for one i64 where `upstream_refused` writes a
16-word `SLOT_WORDS` receipt. A pageable upload returned before its device transfer completed.
Row inspection reread the whole section once per row; one read cut egress from 1,996,735,168
to 4,145,856 bytes with identical text. Object: **Receipt**: complete per-row receipts.

**W10. Small tasks returned inside their scope.** [established-bounded; measured] `athena_field`
trained its quarter-turn and survived rest and remount. The three-word text edit reached 27/27,
including all six edits, after eight passes (434 targets; one pass gave 21/27 and 0/6 edits),
with 23 ms median generation. The partial-field application returned 45/45 missing values while
preserving 63/63 supplied values over 39 responses. These are regression controls, not
conversation. Object: **Constitution**: D/M learned from observed targets.

**W11. The instrument contract.** [definition; source-inspected] `PRODUCT.md` asked for one
explicit root, the written files named by every mutation, create-new immutable writes, atomic
replacement, refusals that keep the last admitted state, and consequence-first human output over
a complete JSON wire. The workspace family implemented it over a superseded snapshot artifact,
not the HNN model. Object: **Receipt**.

## 3. What didn't work

**D1. No useful conversational output at any scale.** [established-bounded; measured]

- Linked-torus nibble chart, 438-byte request: 64 bytes beginning `ee ff`, invalid UTF-8, 2/128
  robust faces. Exact ancestry showed the request reached only 2/32 (development) and 2/128
  (evaluation) free coordinates ([record](2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md)).
- Full-capacity incident field, 76,599 sites: both retrospective requests (438 and 76,081
  characters) produced incoherent 388-character replies. One earlier reply was almost entirely
  one repeated character; after the port and precision repairs 113/388 and 15/388 positions
  were robust, and neither answered ([record](2026-09-21_THE_INCIDENT_FIELD_JOINS_ITS_GENERATOR_RECEIVER_AND_FROZEN_RETURN.md)).
- Replaying the one learned development response recovered 18/388 characters, at response
  cross-entropy 3.80983 against 3.82864 for a uniform 46-class face.
- Generator machine, six `ab`/`ba` cycles: 0/6 exact targets. It learned 0.085 bits; its best
  cycle was 0.045 bits better than uniform and about 1 bit worse than an order-0 count.
- Exposure sample (6 returns, 231 cells): 17.7–22.7 bits/row worse than uniform, then [0,1]
  enclosures from the fourth return; an observe was refused near frame 203.
- The earlier `text_hnp4` (Sep 5) additive law degraded into repetition and exceeded its
  126-octave carrier at the ninth operation
  ([record](2026-09-05_HNP4_NATIVE_TEXT_CONTINUES_BUT_UNCHECKED_ADDITIVE_CULTIVATION_DESTROYS_THE_RETURN.md)).

**D2. The codec was the architecture.** [established-bounded; source-inspected] `Utf8Nibbles`
and alphabet-derived one-hot channels set the channel count, junction slots and target alphabet.
The linked-torus chart allocated one ring junction per source cell (76,599 sites for a
76,081-character source). Codec growth admitted untrained classes whose initial biases dominated
a weak current: 288/388 emitted classes were untrained rows. No encoder E, induced action U and
decoder D with `D E = ρ`, `E_next T = U E` was built for the text path, and the session never
called `HelicalMomentReuse`. Violated: **Generator** (count independent of source length) and
[Holonic Encoding](2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md).

**D3. Retention by archive.** [established-bounded; source-inspected] The ordered-source path ran
the full nonlinear word (up to 128 iterates) once per source occurrence and kept every word in a
reverse tape until observe or release. It replayed frozen producing cuts and appended to a
`returns` journal on most paths. The exposure driver kept pending pairings in a
`.pairings.json` sidecar written separately from the checkpoint. The full-capacity pending
checkpoint was 4,436,880,359 bytes. A delayed observe read `p−q` from the frozen receiver and
pulled it back through contemporary material, mixing two cuts
([audit](2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md)).
Violated: **Deposition**: retention is a future-sufficient quotient, never a record.

**D4. Scalar readings pointed the wrong way.** [established-bounded; measured] One continuation
lowered the combined loss reading 3557.426 → 3531.015 while character agreement fell
187/388 → 153/388. An earlier 295/388 came from a poorly converged Richardson solve, not the
accurate field. Reported bits used the `ExponentialPotential` face, learning the `PacketModulus`
face and selection a third. Violated: **Ratio**: loss is the log of a Holon ratio, and a scalar
is one limit reading of it.

**D5. Enclosures swallowed the answer.** [established-bounded; measured] One update raised the
certified operator norm 4.640 → 11.814. Auto-selected Richardson ω fell 1/32 → 1/256 at a fixed
1,024 iterations; the response radius grew 0.001181 → 40,158 and every probability interval
widened to [0,1]. Independent-row recombination widens a radius by about √k. The generator
machine's joint radius grew 0 → 0.0612 over six cycles.

**D6. State and cost far beyond the data.** [established-bounded; measured] The six-cycle
control carried about 2.55 million bits of state for 19 source bits; 95% was reaction material M
(197,004 values) from `Φ(s,c)=s⊕c⊕(c⊗s)`. The dense support normal (1,537 sources × 513 targets)
held about 1.865 GB. The full-capacity run took 232 s to generate, with a 3.24 GB resident peak.
The process around a 3.7 s request took 132 s, mostly opening and validating the trained rest.
First-process runs of 228.91 s and 361.61 s included cold CUDA/PTX setup; four warm primitive
tests took 1.47 s.

**D7. The workbench never became the instrument.** [established-bounded; source-inspected] The
command surface churned through workspaces, a rejected TUI, inherited-model `hna` commands and
five stream kinds, each retired in turn. At `14cfb22a` the batch runtime refuses all five session
commands (only `wave-control` runs through it), so `main.rs` bypasses it with five near-identical
per-kind blocks, writing JSONL to stdout and a process receipt to stderr. One `HnaStreamCommand`
union of 24 actions serves five session kinds; each kind implements a subset, and the rest refuse
through `StreamTarget` defaults. Ten schema identifiers coexist (workbench request, response and
event; stream request and event; five process receipts), and checkpoint and rest wires were
versioned repeatedly with readers for older versions. The README and `diagnostic capabilities`
still advertise removed commands. The Athena drivers were `cargo run --example` programs with
hand-parsed flags (the exposure walk alone is 1,102 lines), never workbench commands.

**D8. The question changed at each new owner.** [interpretation; process-audit] The
[evaluation-history review](2026-09-15_ATHENA_EVALUATION_HISTORY_AND_SHARED_CONSEQUENCE_KIT.md)
found each new owner acquiring a new easy example (quarter-turn, three-word edit, `ab`/`ba`)
that became the next milestone while the retrospective episodes stayed failed. Brandon's
September 15 correction applies: a local test bounds its own claim and does not reset the
accumulated capability.

## 4. Requirements for the rebuild

[definition; agent-inferred] Each requirement cites the items in §2–3 it follows from.

1. **One session, one protocol** (W1, D7). The application projects the restructured library's
   HNN port: one session type, one request vocabulary in which every command is meaningful for
   every session, and human/JSON/JSONL as views of one result. No per-kind stream, and no batch
   path that refuses the main use.
2. **Encoding is the generator/receiver construction** (W5, W7, D2). The source enters as
   phase-carried moments on a fixed machine whose generator count is independent of source
   length. Response positions are receiving phases whose binding does not depend on request
   length. The codec sets no channels, sites or target alphabet. A text face reconstructs valid
   Unicode through its receiving relation, and the path states `D E = ρ`, `E_next T = U E` or
   its retained defect.
3. **Retention by quotient only** (W5, W6, D3). A pending comparison holds its moment, phases,
   covector and material identity; a late comparison reads contemporary material and returns
   its residual. No tape, frozen cut, update journal or sidecar. Report resident state against
   source length; the flat 2,936 bytes at N = 2–128 is the baseline.
4. **One face for learning, selection and report** (D4). Loss is the log of the Holon ratio,
   and reported bits lie on the face the adjoint consumes. Every run reports uniform, order-0
   and order-1 baselines; failing to beat order-0 is reported as a failure.
5. **Inspected consequences on the standing episodes** (W3, D1, D8). Keep the pinned exposure,
   the 773–776 development cut as the restart control, events 3406683 and 3398355 and the
   complex-product code case as retrospective applications, separate input and assessment
   files, and nongold recorded replies. Read the content, not only symbol validity or loss. A
   new small example does not replace them.
6. **Exactly-once durability in one file** (W1, W2, D3). Model, cursor and pending comparisons
   publish atomically in one checkpoint. A frame is acknowledged only after native use; output
   drains before the next read and replays without re-execution. Byte-identical resumed and
   uninterrupted state is a standing check.
7. **Numerical health in every response** (W8, D5). Each response carries its radius, robust
   count, operator bound and contraction. Refuse rather than emit from a face whose enclosure
   covers the simplex. Choose solvers under an independent residual certificate, and keep factor
   balls rather than collapsing them to a scalar.
8. **Costs by kind, on declared hardware** (W9, D6). Report cold setup and validation,
   generation, update, ingestion, resident state, rest size and egress separately, with state
   bits per source bit. Run full-size inputs under memcheck before trusting a layout.
9. **Private by construction** (W3). Public output carries counts, labels, bits and timings;
   private diagnostics are opt-in and owner-only; no raw conversation enters the repository.
10. **The surface documents itself** (W11, D7). Help, README and capability listings are
    generated from or tested against the command type. Each artifact has one wire version and
    no legacy readers (Brandon, September 23).

## 5. Where the retired code can be read

[established-bounded; source-inspected] At `14cfb22a6bc61c64812ad44c521eeb22f0bd51ba` on `main`
(2026-09-24):

- Workbench: https://github.com/brandonrdug/holonics/tree/14cfb22a6bc61c64812ad44c521eeb22f0bd51ba/applications/holonics-workbench
- Athena examples and support: https://github.com/brandonrdug/holonics/tree/14cfb22a6bc61c64812ad44c521eeb22f0bd51ba/crates/holonics-hna/examples
- Stream protocol: https://github.com/brandonrdug/holonics/blob/14cfb22a6bc61c64812ad44c521eeb22f0bd51ba/crates/holonics-hna/src/stream.rs
- Conversation source and cursor: https://github.com/brandonrdug/holonics/blob/14cfb22a6bc61c64812ad44c521eeb22f0bd51ba/crates/holonics-hna/src/alpha/exposure.rs

Earlier surfaces: `83416740` (CLI and Ratatui), `d1e78187` (variant workspaces) and `a69b505f^`
(the `hna run/inspect/infer/train/session` commands before retirement).
