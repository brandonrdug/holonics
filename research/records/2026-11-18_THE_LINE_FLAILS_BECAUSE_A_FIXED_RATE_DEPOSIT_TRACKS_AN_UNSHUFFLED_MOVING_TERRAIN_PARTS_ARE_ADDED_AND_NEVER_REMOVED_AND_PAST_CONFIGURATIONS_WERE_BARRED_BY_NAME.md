# The line flails because a fixed-rate deposit tracks an unshuffled, moving terrain; parts are added and never removed; and past configurations were barred by name

November 18, 03:00 UTC. An audit of the engine (`crates/engine`, `crates/engine-cuda`, `crates/athena`), `tools/runs.py`, the plans,
PRs #880 to #972 and the store line's laps 1 to 95, made at Brandon's request (November 18, 02:38Z: "there is clearly chaotic failing,
we're not hitting any real walls we're just flailing"). Read only: nothing was built, run on the card or changed in the engine, and no
run of the lead's was touched. Every number below was read from the code, the line's saved states and logs, or the records named; the
rulers are in [the receipts](receipts/2026-11-18_audit/). Held codes are nats a place at lap means unless marked bits.

## 1. The causes, ranked by how much of the flailing each explains

### 1.1 The deposit runs at a fixed temperature, and its state is a walk at its own noise floor

- The step is `((m ≪ grain) ≫ rate) / (⌊√v⌋ + 1)` ([`deposit.rs:506-518`](../../crates/engine/src/deposit.rs)), moments at `2^(−3)` and
  `2^(−8)` (`FIRST_RATE`, `SECOND_RATE`, "the classical 0.9 and 0.999 read as dyadic"): Adam with β₁ = 7/8, β₂ = 255/256 and a
  negligible ε, at `rate_bits = 12` on every lap from 1 to 95 (`STORE_DECLARATION` in every `lapN.log`).
- Nothing changes the rate. `RateParts::updated` ([`deposit.rs:186`](../../crates/engine/src/deposit.rs)) and `part_travel` have no
  caller outside tests; lap 94's state carries `parts 32 0 0 … 0`, no `rates` line and no leak. Its floor (`deposit.rs:191`,
  `saturating_sub(1)`) could not cool a part below the base rate even if it ran. THE_ENGINE §3 and §11 describe "a part's octave moved
  at a lap's end by its travel": on the line it does not happen.
- The trainer computes its own line search and ignores it: `octave=1` (the step should double) at all 262 `STORE_SAVE` lines of laps 1
  to 94 (`store.rs:479`, `store.rs:502`, `exterior.rs:53`); its curvature changes sign from save to save within a lap.
- The state is at noise. Over lap 94's end state, mean `|m| / (⌊√v⌋ + 1)` across the 388,671 entries with a second moment is **0.193**
  (RMS 0.260). For a covector with no consistent sign the ratio is `√(2/π)/√15 = 0.206` (RMS 0.258). Every dense block (q, v, a, b, w,
  read, carry, triad, temper, glue, level) reads 0.20 to 0.21; only the opening (0.34) shows a direction.
- The walk is measured. Displacements over successive thirds of lap 94 have cosines −0.13 to −0.53; lap-to-lap displacements of the mean
  read 0.11, 0.04 and −0.11 over laps 92 to 94; displacement over four laps is 2.0 to 2.5 times one lap's (a walk gives √4 = 2). In every
  1,000 sections about 382,000 of the 402,805 entries move (`moved=` on lap 94's saves).
- Lap 94's steps predicted −10.6 bits a place on their next sections summed over the lap; the lap's code moved −0.0007 bits a place,
  7×10⁻⁵ of it. Each step's gain on the next section is the restoring half of its own jitter.

This is the signature Brandon named: the state moves every section and goes nowhere, and every reading taken on it is a draw. Lap-mean
scatter is ±0.003 to ±0.01 nats a place (laps 74 to 77: GSM8K 0.7623, 0.7596, 0.7732, 0.7628), while the effects the records rule on are
0.001 to 0.005. Most rulings of November 11 to 17 on a part's worth were made inside that spread.

### 1.2 A section is a few documents read in order, the same order every pass

- `Cut::next` ([`passage.rs:385-426`](../../crates/engine/src/passage.rs)) takes the slice furthest behind its quota and reads that
  slice's pieces in order from its cursor; `next-pass` sets every slice back to piece 0 (`store.rs`, `next_pass`), so each pass meets the
  documents in the same order. Nothing shuffles stretches across documents.
- Pieces read a section at lap 94: code 1.9, web 0.96, science 0.66, wikidata 0.26, books 0.058 (one book spans 17 sections).
- In 85 to 89% of sections the step's first-order transfer to the next section is a fall, and the lap keeps about a thousandth of it: the
  steps fit the documents in hand, and the next documents take it back. With 1.1, a fixed rate on a correlated stream, this is a tracking
  filter, not a learner that settles.

### 1.3 The terrain changed six times in twenty-four laps, and each change cost more than all the laps between

- Regimes (chain19.sh to chain28.sh): A laps 60–70 five text slices; B 71–73 `join-store` adds arithmetic and word problems at 25% each
  (text falls to half of every section); C 74 the world's acts; D 75–76 ten crossing triads grown; E 77 the refined act; F 78–94 the
  arithmetic slice redrawn (536,521 pieces of about 932 bytes became 10,420,364 of about 48), acts one in 21; G 95 arithmetic dropped.
- Text paid at once and never recovered: lap 70 → 71 code 0.4901 → 0.5449, web 0.8494 → 0.9061, books 0.8131 → 0.8654; lap 94 code
  0.5492, web 0.9004, books 0.8574. Lap 94's text levels are laps 17 to 26's. Laps 1 to 70 took 33.0 hours of card and lowered the text
  mean by 0.080; laps 71 to 94 took 18.6 hours and left it where lap 71 put it.
- A stable stretch gains about 0.0012 bits a place a lap; a change of terrain costs about 0.08, sixty-odd laps of gain.
- Since lap 78 the held arithmetic and the forms read the old draw: `HELD_arithmetic` and `FORMS_arithmetic5.tsv` are byte-identical in
  store-16 and store-16b, and `forms24.sh` still reads `store-2026-11-16`. "The arithmetic is flat since lap 78" is partly a read of a
  draw the line stopped training on.

### 1.4 The comparison is spent away from the writer, and the states trained are not the states written

- The opening is compared at every place at unit weight (`moment.rs:334`, "no domain weight"), once a read, inside `returned_with`
  (`adjoint.rs:825`); the face covector is scaled by domain over open (`adjoint.rs:683-689`); both reads are summed and halved
  (`adjoint.rs:86-95`). Per section on lap 94: the opening is 40,120 places, 65% of all comparison weight; the face's domain of 21,233 is
  split half and half between the first read and the marked second read, so the face the writer draws from carries about 18%.
- They share rows: the tied encoding E is the readout of both lifts, and both faces add `p̂ − q` into the same class biases `c_a`
  (`adjoint.rs:701`, `moment.rs:336`). The opening reaches `x⁰` without the ticks, so it shapes the inputs.
- Training's writer states give the true end (`passage.rs:333`: only `t < q + a` is resolved, the void tail known); the release opens
  every place, the tail included (`release.rs:539`), and must place the end itself. Under the octave draw (`passage.rs:325`) about 92% of
  a writer state's compared places lie past the frontier the writer would be at in that state (from the law, not measured). Half of all
  states are scattered `τ = u²` masks the writer never meets, and resolved places hold true bytes where the writer's hold its draws.
- The held read (`cavity.rs:45`) is leave-one-out, the mask regime. So the code can fall while the writes stand, which is what Brandon
  read on November 17. Regimes also fight on the shared rows: fifteen passes compared at the boundary alone took the night's state to 76%
  of its words in the lexicon and its two-sided reading from 1.129 to 2.921 nats (the level's design record §12).

### 1.5 Parts are added and never removed, at the noise floor, at a real cost

- The declaration changed twice in 94 laps (lanes 3 → 4 before lap 6, triads 0 → 10 at lap 75) and nothing was ever taken out.
  THE_ENGINE §4 and §5 still give the line as `v14m … 0 32 0 1 0 1` with 392,505 entries; it trains `hnn-field-v14x … 32 10 1 0 1 0 1`
  with 402,805, and the field.rs header gives the strand triad where the line runs the site triad (`contact.rs:779`, `d.crossing`).
- The level and its glue are 149,776 entries, 37% of the material, all at the noise floor (0.19 to 0.21). 9,096 of the level's 50,640
  entries have never had a covector (its encodings, reads, paces and face; the level's moments are wired to zero at
  `field/scale.rs:437`). Its prolongation (`scale.rs:456-466`) adds an O(1) term at the split from material that wanders: an injected
  perturbation, not a learned scale. Its own readings (November 17) say its restriction keeps what a drawn one keeps.
- The ten crossing triads trained 20 laps (all 10,300 entries moved, RMS 1.28M → 2.02M) with held arithmetic at 1.2758, 1.2744, 1.2782
  bits at laps 74 to 76 and the units digit at 2.20 to 2.36 nats against their acceptance of 1.8.
- The world's acts take 51 to 59% of each section's card time (`regions_ms`) for 0.05 to 0.07% of its sites; a section went from 0.47 s
  to 1.0 s at lap 74, and laps from 1,425 s to 2,940–3,300 s. The kernel campaign's gains (#880 to #919, 38 PRs, laps 2,101 s → 1,425 s)
  were spent within four laps.
- The mark's second read opens on the first read's shares as data (`contact.rs:799-811`, strengths 0.22, 0.74, 0.745): the first read is
  never trained for its effect as a mark. It cost 585 against 412 ms a section when it entered and helps whole masks, not the one-place
  read the line is scored by.

### 1.6 No store relaxes, so norms ratchet

`Learner::leak` is `None` on every state of the line. From lap 10 to lap 94: RMS of w 0.129 → 0.169, read 0.128 → 0.171, a 0.120 →
0.153, the opening 0.084 → 0.165; the paces' RMS 2.50 → 3.77 and their maximum 12.9 → 19.9 (head 1 at `}` 11.8 → 19.9, at a newline
12.9 → 18.0), the one family whose third-to-third displacements agree (cosines 0.31, 0.51). The paces stretch the turned heads' clocks,
so every lap their skins cut those heads off past delimiters a little more. Steady growth with no saturation is what "no store is at
rest" forbids and the engine has.

### 1.7 The contact's far reach is gated and its turned heads favour distance

- A far source enters a receiver's support only where its key's shell class (the quadrant of each mode, `shell`, `contact.rs:257-260`;
  `class_of`, `contact.rs:505`) meets the probe's class or its seams within the band. The gate has no covector; descent acts only inside
  it. A far route forms where drawn shells happen to coincide.
- In the turned heads the score's `−D²|k̃|²/2` term (`contact.rs:286-291`, `z = T·base − ⌊log₂ d⌋` at `contact.rs:640`) costs a
  non-matching near source up to `nT ≈ 18` to 22 bits and a skin-decayed far one about 0, against a distance falloff of at most 11 bits.
  So far non-matches outscore near ones (computed from the code and the deposited temperatures, not measured), and a row falls back to an octave-weighted sea, consistent with rows holding 0.29 to 0.39 of
  their weight on the sources a sum's place needs. (The still heads' term is a constant and cancels.)

### 1.8 A third of the encodings take no step in a section

At grain 16 and rate 12 a face-grain step is `trunc(16 r)` grains: each section 38 to 47% of the entries of E, E₋, E₊ and the moment
encodings take no step, the median nonzero step is one grain, and the division truncates toward zero (about 10% of drift lost at
`σ_r = 0.26`, more on sparse rows), where the precision law releases to the nearest numerator. Material families resolve 1/4096 of a
step and are not affected. Moments also reopen at `m = g, v = g²` after a silence (`learner.rs:485`), a first step about four times a
typical one, again and again on sparse rows.

### 1.9 Capacity is small, and the lawful way to grow is unbuilt

402,805 entries (lap 94: 253,029 field, 50,640 level, 99,136 glue) over 701 MB read once. The largest gain of the whole line was a lane
(lane 3, 0.0266 nats one-place, growing through its pass; G188, G190). A fifth lane's price (0.0015 to 0.004) was a guess, never run, and
is quoted as a measurement in the phase review §4.3 ("no count of lanes writes a sentence"). Widths may not be doubled by rule, and the
founding law that would grow the machine is not in the engine (THE_ENGINE §10). Each new part is a small adjunct to a fixed-size state.
This explains why parts buy hundredths; it does not explain the walk, which 1.1 to 1.3 do.

### 1.10 The work became readings, and the readings were made inside the noise

- PRs #880 to #972 (93): 38 kernel speed (41%), 51 records, guesses, readings and rulers (55%), 2 that changed what the line trains, 2
  host-only attempts. From #800 to #972, 173 PRs in 3.6 days; about 270 distinct guess ids in the records of November 10 to 18, most of those scored missed.
- Each correction of Brandon's became a rule or a record within minutes (#917 five minutes after "speed is a steady background", #952
  minutes after "nothing compounds") while the practice it corrected ran on for 20 to 30 hours (the kernel campaign, nats-only reports,
  the arithmetic world: chain26 kept the world on for laps 91 to 94 after the side lap of #949 had read its cost). CLAUDE.md went from
  35 KB on October 5 to 107 KB on November 17.
- Withdrawn readings outlive their withdrawal where they justify code: the saddle (withdrawn by the dwell record) still heads `closed.rs`
  and stood behind the method rule that parts wait for a tension read; the level's "holds almost nothing" stands in the dwell record's
  §19 heading and THE_ENGINE §11; CONSTRUCTION_STATE's "What runs" still says laps are queued; its boxes are "met" on nat readings.
- The causes of one plateau were restated four times in four days (capacity, repetition, the drive halving, "never founds", then "never
  dwelt"), and none was tested against the deposit, the order of the stream or the mixture, which are 1.1 to 1.3.

### Checked and sound

Covector rounding (2⁻²⁴ a term, summed at 2⁻⁴⁰, released once to 2⁻³² unbiased; noise about 47 grains against medians of 10⁶ to 10⁸);
`toward` loses no mass; the step stays under its bound (9,165 grains against 17,200); `ratio_adjoint` matches `ratio_to_power`; the carry
circles are passive (`|γ| < 1`); no target leaks into a read (blank clocks, the cavity excludes the place's own row); the state tools
(`next-pass`, `join-store`, `move-store`, `set-world`) change only the pass line and keep moments and rates byte for byte;
`grow-crossings` maps every entry with its moments; the card refuses unsupported parts loudly and nothing is silently off; `runs.py`
never double-launched a lap (lap 34 was the one out-of-memory exit).

## 2. Configurations set aside that answer these

Each was set aside by name or by a short reading, and each bears on 1.1 to 1.7 (records under `research/records/`, the October machine at
`d5ed4adc1` and `d6bbd1644`):

1. **The lap law of October 24 and 25**: sufficient statistics summed at a held constitution, foundings from a pool under a description
   charge, a refounded bridge, no section steps. A founded ring wrote 308 of 495 held units; one stepped lap of the readouts took it to
   247, a full stepped pass to 55; held text 2.512 bits a byte at the lowest pass against 3.033 after the stepped pass. On November 17 the
   bridge-only replay held a units digit at 1.64 nats against the foil's 2.35 at a quarter of the stepped arm's cost to text (`b0fc6902d`).
   It answers 1.1 and 1.2 directly: what the fixed-rate step erases, a held constitution keeps.
2. **The replay finding of October 26** (the record "the summed covector does not read the pass"): a pass's starting covector predicted
   its change at the wrong sign and 20 to 50 times too large (+392,159 predicted, +8,025 measured on the blank-line clock). It is 1.1
   measured a month earlier, filed under the copier's withdrawal banner.
3. **The certified step** (lessons of September 29, lesson 6: a deposition step reads a bound on the covector reaching its locus and is
   enforced at the commit; the reread retired November 5). The engine's step is uncertified Adam; lesson 6 was never applied to it.
4. **The pool-founded clock of October 26** (`8147a5dd7`, `9b915dbe1`, `7f0921b4b`): founded from tension with no label (the blank line,
   363 parts per million), its certificate paid (22,588 bits below its twin against a charge of 11), its role read in 53 of 97 held answers
   and eroded to 43 by one stepped pass. The one founding ever built that acted on text, under the banner that called it a copy pointer.
5. **The coupled bank of October 26** (`tower/bank.rs` at `0934a25ff^`): a delta-rule store with dynamics and coupling, which passes the
   November 9 test of a store. 15,999 of 16,000 held recalls against 243; held bits a byte below its foil on prose (3.042 against 3.083),
   Lean (2.341 against 2.402) and Rust (2.079 against 2.117); zeroing its join returned each to the foil. It is the distant read 1.7 lacks.
6. **The located strands of October 26** (`de239160e`, `a4f168775`, `aac5cdfce`): keys closing 7,042 of 7,042 calculations in the largest
   groups; the comparison opened in four contacts a ring at 250 thousandths, zero in every final state after stepping. Again the step
   erased what founding located.
7. **The rotor tower** (`d9563cf20`): torsion {3, 11, 101} located by loop closure, held 1.779 against 1.869.

Every October founding was eroded by the fixed-rate step that followed it (308 → 55, 53 → 43, 250 → 0). The November line has the same
step and no founding. That is one mechanism, seen twice.

## 3. What to reconcile, in order

1. **Make the deposit's temperature a state.** Act on the line search the trainer already computes, or run the octave law with a floor
   below the base, and read each block's `|m|/√v` against 0.206 as the deposit's own measure of signal. Train from the lap's mean as well
   as reading it. Take up the lap law's sufficient statistics and the certified step (§2.1, §2.3) as the attempt beside it.
   [Added the same hour by the second audit: the line search is the transfer law of November 4, whose price read empty and which
   prints `octave=1`, the step doubled, at every save; that day's own reading is that cooling pays when it is read directly (0.043
   nats a place at once). The direct read and its guesses are in [the companion record](2026-11-18_COOLING_WAS_MEASURED_ON_NOVEMBER_4_AND_RETIRED_THE_LINES_LEVEL_IS_TRADED_BY_ITS_MIX_AN_OPEN_PLACE_IS_NEVER_A_SOURCE_AND_A_CHANGE_TO_A_LINE_RUNS_BESIDE_A_CONTROL.md) §4.]
2. **Shuffle the stream.** Draw stretches keyed across a slice's pieces within a pass (the key stream exists), and price a step's
   transfer on a section drawn from other documents.
3. **Hold one terrain for a declared number of laps.** Re-pin the held arithmetic and the forms to the draw that trains, or drop the
   redraw; read text by slice.
4. **Declare the comparison's weights and train the writer's regime.** Weigh the opening against the face by declaration, compare the
   writer's own states (an open end, the frontier distribution the release meets), and keep the mask regime at a declared share.
5. **Take out what reads nothing**, each removal read at lap means against a control of equal length: the crossing triads, the level and
   glue (or give the level its receipt), the mark on the one-place read. The world's acts are already off at lap 95.
6. **A leak** (`Learner::leak` exists) or a balance for the paces.
7. **The contact**: read the rows with the shell gate relaxed, and the turned heads' power term against the falloff; the bank (§2.5) as
   the distant read.
8. **Round face-grain steps to the nearest numerator.**
9. **The guides to the line as trained**: THE_ENGINE §4, §5 and §11 (v14x, 402,805 entries, no octave law running, rows for the deposit
   and for the training distribution); strike withdrawn readings where they still justify code.

## 4. The workflow policies, and what changed in the guides

Brandon asked (02:38Z) that every contaminating policy in Claude's own guidelines be found and removed, first the blacklisting of past
configurations. The guides hold these policies; each is kept, rewritten or retired as follows.

**Retired or rewritten (the blacklist and the gates built on it):**

| Policy | Where | Change |
|---|---|---|
| "Port … one law or kernel at a time … Never restore wholesale" | CLAUDE.md, after the reset | Port a law, kernel, part or whole configuration; a whole configuration may be restored as an attempt to be read |
| "Do not port" what the lessons retired | THE_REBUILD §4 | Restated as the laws' tests a port answers, never a list barred by name |
| "A choice that repeats one is refused before it is built" | CLAUDE.md, the lessons rule; lessons of September 29, lesson 1 | Refused only where it repeats a failure's mechanism under its conditions, by the law's test; resemblance proceeds |
| "A store addressed by content is an index whatever it overwrites" | lessons of September 29, lesson 4 | Read by the November 9 store test (balance over time, flux to read) |
| "Re-proposing a retracted mechanism … is a contamination" | RETRACTIONS.md | A retracted mechanism may be proposed again, citing its retraction |
| "Nothing here is a design to resume" | the banner on 21 records of October 23 to 26 | "Any piece of it may be taken up again as an attempt" |
| The October and November "left" lists | CONSTRUCTION_STATE | Headed as readings under their conditions, never a bar on a port |
| The names in "no catered machinery" applied as bans | CLAUDE.md | The reason judges a mechanism; a name does not |
| "A part … enters with located operands or waits" | CLAUDE.md method, the tension read (the lead's) | The gate is retired; its saddle premise was withdrawn by the dwell record. The read is an instrument beside a part |
| "The reason is recorded with the rule … the same day" | CLAUDE.md, how a rule is written | A correction changes the work first; it becomes a standing rule only when it recurs |

A new postulate, **a past configuration is an instruction, never a verdict** (`CLAUDE.md#past-configurations`), states the rule these
follow, with its reason and scope. The project memory carries it at the top of its index.

**Kept, with what the audit found beside them:** the governing laws (precision, retention, the covector, the loss, stores and caches,
no catered machinery by its reason); recover before implementing (it is the opposite of a blacklist); decide from the mathematics; short
loops; the method rules of Brandon's (a build is one attempt, judge by structure, a reference answer is one specimen, no run switches,
read the code and the decoded output, width is never a dial, a reading names its region, a size belongs to its part, a symbol is a word,
one law reads every stream, a temperature is a store's state, a comparison is an agreement, loudness beside nats, a face's top, speed as a
steady background, a step judged by its writes); the lead's rules on a premise's presence, a ruler's null and a learner's null held to a
length; GPU first; the waiting standard; the trunk contract; evidence; delegation; issues. Two of these are kept and flagged by what the
line shows: "a temperature is a store's state" is the law 1.1 breaks, and "a line's level is read at its lap's mean" reads a mean the line
never trains from. "Theory picks, and a run tests a stated prediction" is kept; its cost on the record is about 270 guesses in eight days, most
fixed on effects smaller than the lap-mean spread of 1.1.

The coordinator's own project memory is outside this machine's reach; it carries the same blacklisting only where it copied these texts.

## Receipts

`receipts/2026-11-18_audit/`: the rulers (`moments.py`, `travel.py`, `meanvs.py`, `trend.py`, `roots.py`, `pace.py`, `laps.py`,
`spread.py`, `cos.py`, `still.py`, `triads.py`, `ends.py`, with `layout.py`), run on the host from the line's saved states and logs under
the line's run directory, with no thread budget beyond one Python process each; and `prs_880_972.txt`, the PRs by kind. The `|m|/√v`
figure of 1.1 was read again by the lead of this audit on lap 94's `STATE.3000` (0.1933 over 388,671 entries; RMS 0.260).
