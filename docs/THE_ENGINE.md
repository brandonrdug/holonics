# The engine

The engine is the attempt that trains: the field law of `holonics_engine::field` in
[`crates/engine`](../crates/engine/src/lib.rs), its card realization `holonics_engine_cuda::hnn::field` in
[`crates/engine-cuda`](../crates/engine-cuda/src/hnn/mod.rs), and the store line's commands in
[`crates/athena`](../crates/athena/src/main.rs). This guide is the route through it, written against the cut of
[THE_CONSOLIDATION](plans/THE_CONSOLIDATION.md) (#603). It names each phase's object, its equations at their widths,
the files and kernels that realize it, its kind of computation, and its Lean and atlas owners. The objects are the
[elementary objects](ELEMENTARY_OBJECTS.md). The derivations are in the dated records each module's first lines link.
[THE_MACHINE](THE_MACHINE.md) states the line the engine serves, and [HNN_FORMULA](HNN_FORMULA.md) its
classical restrictions. A build of the engine is one attempt (CLAUDE.md, Method): this guide describes the attempt
that stands, never the law.

## 1. What it is

A **problem is one relatively complete region**: a stretch of a passage whose resolved sites carry the classes that
arrived and whose open sites are compared with what arrived there. **One constitution is iterated over all of its
sites at once**, `K` ticks, and a receiver's face is read at the open sites. A section is a batch of regions read
together. The learner reads a section, returns the comparison's covector through the operands that produced it, and
deposits it. The state it carries is its constitution, the deposit's two moments, its rates, and the pass's place
over its store ([§5](#5-the-learners-state)).

Every value is a word at a declared grain. Faces, charts and currents stand on `2^(−16)`, material on `2^(−24)`, frames and skins on
`2^(−30)`, a series row's exponential faces on `2^(−62)` with its shares on `2^(−63)`, covectors on `2^(−24)` and
the contact's on `2^(−40)` ([`width.rs`](../crates/engine/src/width.rs)). Every product's remainder below its grain
is released to the nearest numerator before the product enters a sum, and every sum keeps its terms, so the host
and any partition of the card give the same bits (CLAUDE.md, the precision law). The chains (the carry circles' scan,
the ticks) release at every step and run in their declared order, which is the law's
([the record of November 15](../research/records/2026-11-15_A_VALUE_IS_READ_AT_A_PLACE_A_SUM_IS_ORDERED_ONLY_WHERE_A_RELEASE_IS_A_SECTION_A_CENSUS_CONFIRMS_TO_ITS_OWN_SPREAD_AND_THREADS_RECONCILE_AT_THEIR_CONDITIONAL_INFORMATION.md) §6). The host realization (`Host`) is the reference the card's
bits are checked against. Learning runs on the card.

## 2. The one move

The engine runs one operation over five index sets ([THE_CONSOLIDATION §2](plans/THE_CONSOLIDATION.md#2-the-anchor-one-move)).
The object is the [Ratio](ELEMENTARY_OBJECTS.md#9-ratio): a mass `M` and a current `J` carried as an undivided pair
and divided once, at the receiver that reads it.

```text
step      (M, J) ← (γ M + m,  γ J + m c)        a term of mass m and content c arrives; γ carries what stood
compose   (γ₂, m₂, j₂) ∘ (γ₁, m₁, j₁) = (γ₂ γ₁,  γ₂ m₁ + m₂,  γ₂ j₁ + j₂)     associative for every γ
release   y = J / M                              once, at the receiver; never between steps
```

| Index set | In the engine | `γ` | Kind | Its chart in a discipline |
|---|---|---|---|---|
| the sources a site meets | the contact, `y_i = Σ e_ij D ṽ_j / Σ e_ij` | 1 | sum | attention (`resolvent.attention-chart`, `norm.mass-current-associative`) |
| the sites along a strand | the carry circle, `Q_t = κ_t b_t + γ_t Q_(t∓1)` | a rotor with a leak | chain | the selective scan (`resolvent.ssm-realization`, `tower.field-scan-gate-once-a-site`) |
| the ticks at a site | `x ← x + O y` | 1 | sum | a residual stream (`tower.field-tick-running-mean`) |
| the sections of a lap | the deposit's two moments | `1 − 2^(−r)` | chain | an optimizer's moments (`deposition.rate-temperature-standing-spread`) |
| the states of a lap | the lap's mean | 1 | sum | an average of iterates (`tower.field-lap-mean`) |

Lean holds the pair's associativity at `γ = 1`
(`Computation/AttentionModeCompression:weighted_summary_associative`). The ordered composition's statement and
whether the built carry keeps its bits when cut into blocks are the engine line's
([THE_CONSOLIDATION §11](plans/THE_CONSOLIDATION.md#11-what-the-campaign-leaves-to-the-engines-line)).

**Three kinds of computation.** A **sum** adds terms at `γ = 1` in integers on any partition of the card. A **gate**
is a function of one site alone (a lock's exponent, a carry's `γ` and `κ`), read once a site, every site at once. A
**chain** takes steps at `γ ≠ 1` along an order. Every phase below is one of the three.

## 3. The pipeline

The phases in the order a section runs them. The equations are `field.rs`'s first lines, which state the whole
forward; each module's own first lines carry its derivation. Kernels are named as `kernels/field.cu` names them.
The card module is under [`crates/engine-cuda/src/hnn/`](../crates/engine-cuda/src/hnn/mod.rs).

| Phase | Object and equation | Host module | Card module and kernels | Kind |
|---|---|---|---|---|
| cut | a stretch of the store's passage and its one state: a keyed draw (`state_of`) or the release's own state at a crossing of its octaves (`own_state_of`, the pass's word `own`) | [`passage.rs`](../crates/engine/src/passage.rs), [`region.rs`](../crates/engine/src/region.rs), [`codec.rs`](../crates/engine/src/codec.rs) | host only | |
| rings | turned ring sets on the solenoid's periods, `U_(t,m) = e^(2πi (t mod n_m)/n_m)`; still sets `U = 1`; paces and blank clocks | [`navigator.rs`](../crates/engine/src/navigator.rs) | `clock.rs`: `field_paces`, `field_skin_addresses`, `field_pframes`, `field_clock_fill`, `field_blank_*` | gate, a site |
| moment | `s_t = Σ_k ζ^(k−t) D(\|t−k\|) E±(u_k)` at a turned mode: the source enters as phase-carried moments | [`moment.rs`](../crates/engine/src/moment.rs), [`field/moment.rs`](../crates/engine/src/field/moment.rs) | `moment.rs`: `field_moment*`, `field_cavity_*`; `kernels/field_moment.cuh`, `kernels/field_cavity.cuh` | sum over a site's strand |
| open | `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + C s_t + b_s`; an open site opens on its moment, a marked site with its mark on the second read | [`moment.rs`](../crates/engine/src/moment.rs) | `resident.rs`: `field_open`, `field_echo_apply` | gate, a site |
| chart | `r̂_t = x_t/‖x_t‖_rms`, `k_t = W_k r̂_t + b_k`, `p_t = W_p r̂_t + b_p`, `v_t = V r̂_t + b_v`; framed `k̃ = U ⊙ k` | [`contact.rs`](../crates/engine/src/contact.rs), [`navigator.rs`](../crates/engine/src/navigator.rs) | `contact.rs`: `field_chart`, `field_affine_two_*`, `field_unit*`, `field_frame*` | gate, a site |
| classes and support | a key's and a probe's shells `Σ_l 3^l σ_l`; `S_i^h` the near field `0 < \|i−j\| < 6` and the far sources whose key's class meets the probe | [`contact.rs`](../crates/engine/src/contact.rs) | `contact.rs`: `field_classes`, `field_sums` | gate, a site |
| contact | `z_ij = 2^(−β) Σ_m [D_m Re(conj(p̃_im) k̃_jm) − D_m² \|k̃_jm\|²/2] − ⌊log₂ \|i−j\|⌋`, `e_ij = 2^(z_ij)`, `y_i = conj(U_i) ⊙ Σ e_ij D ṽ_j / Σ e_ij`, `x ← x + O y + b_o` | [`contact.rs`](../crates/engine/src/contact.rs), [`ratio.rs`](../crates/engine/src/ratio.rs) | `contact.rs`: `field_exponential`, `field_row_currents`, `field_held_rows`, `field_mark_shares`, `field_spread` | gate (the lock), then sum over the sources; sum over the ticks |
| strand | the pair `x_t ← x_t + W_c (a_t · b_(s(t))) + b_c`; the carry circles `Q_t = κ_t b_t + γ_t Q_(t∓1)`, `γ = γ̂(q)/(1 + d)`; the triad | [`carry.rs`](../crates/engine/src/carry.rs) | `carry.rs`: `field_pair`, `field_pair_gamma`, `field_carry_gates_read`, `field_pair_scan`, `field_triad` | gate, then chain along the strand |
| level | a level on its news: epochs led by sites, the landmarks of the news below (`ρ_t ≥ σ`), run on their own clock | [`level.rs`](../crates/engine/src/level.rs), [`field/scale.rs`](../crates/engine/src/field/scale.rs) | `level.rs`: `field_level_news`, `field_level_chart32`, `field_level_chart64`, `field_level_unchart` | gate, then sum over an epoch |
| face | `z_t(a) = ⟨E(a), R r̂(x^K_t) + b_R⟩ + c_a`, `p̂_t(a) = 2^(z_a) / Σ_b 2^(z_b)` at the open sites; the loud face where declared | [`face.rs`](../crates/engine/src/face.rs) | `resident.rs`: `field_face*`, `field_tied_face*` (the tile form), `field_loud_beta`, `field_gather_rows32` | gate, an open site |
| comparison | the joint code `(m/K) Σ −log₂ p̂_t(u_t)` over a state's `K` open sites among `m`; a port compared through its coupling | [`face.rs`](../crates/engine/src/face.rs), [`region.rs`](../crates/engine/src/region.rs) | `adjoint.rs`: `field_face_covector`, `field_face_weigh`, `field_face_set` | sum over the open sites |
| return | the covector `p̂ − q` returned through the `K` ticks by the operands that produced each carrier | [`adjoint.rs`](../crates/engine/src/adjoint.rs) | `adjoint.rs`: `field_ratio_adjoint`, `field_current_back`, `field_pair_back`, `field_pair_scan_back`, `field_pair_gate_back`, `field_triad_back`, `field_unit_back*`, `field_unframe`, `field_tied_back_*`, `field_loud_back`, `field_mark_back`, `field_outer_bound_*`, `field_wide_add`, `field_add`; the moments' and paces' returns | the forward's kinds, reversed |
| deposit | the two moments of the covector at `2^(−3)` and `2^(−8)`, each entry's step at its own rate, `m/(⌊√v⌋ + 1)` at `2^(−rate)` | [`deposit.rs`](../crates/engine/src/deposit.rs), [`learner.rs`](../crates/engine/src/learner.rs) | host, beside the card | chain over the sections |
| mean | the lap's mean of states, the state a line's level is read from | [`deposit.rs`](../crates/engine/src/deposit.rs) (`MaterialMean`) | host | sum over a lap |
| release | the writer: every answer place opened beside the known prompt, resolved by octaves of distance from it, each drawn from its face on the read of the region as it stands | [`release.rs`](../crates/engine/src/release.rs) | the forward's kernels, one read a place | chain over the reads |

The card's resident realization ([`resident.rs`](../crates/engine-cuda/src/hnn/resident.rs)) opens a region batch,
uploads it, holds the pools and implements `Realization`; [`card.rs`](../crates/engine-cuda/src/hnn/card.rs)
owns the context, the module, the stream and the census; [`profile.rs`](../crates/engine-cuda/src/hnn/profile.rs)
holds the launch records and the yardsticks (`field_yard_*`). A ruler ([`ruler.rs`](../crates/engine/src/ruler.rs))
reads the machine without changing what the state carries or the deposit consumes.

The Lean owners of the phases stand under `lean/Holonics/HNN/`: `Moment`, `RangedMoment` and `ReframedMoment` (the
moment), `Contact` and `ContactBreak` (the contact), `CarryGate` (the carry circle's passivity), `TriadGauge` (the
triad), `TickBlocks`, `TickFamily` and `TickStanding` (the ticks), `ReleaseRun` (a read that releases a run), and
`lean/HolonicsResearch/HNN/ReadsTwice` (the second read).

## 4. The declaration

The declaration is the field's head line, read by [`declaration.rs`](../crates/engine/src/declaration.rs). The line
that trains declares `hnn-field-v14m 244 128 4 8 2 128 4 4 3771 4 0 32 0 1 0 1` (lap 17's mean). Each word with the
part it sizes (CLAUDE.md, Method: a size belongs to its part):

| Word | Value | What it sizes |
|---|---|---|
| alphabet | 244 | the codec's classes, the rows of the encodings `E`, `E₋`, `E₊` and the face's classes |
| width | 128 | one row length every block shares: four lanes of 32, each added by a copy ([THE_CONSOLIDATION §10](plans/THE_CONSOLIDATION.md#10-declared-extents-that-stand-in-for-laws)) |
| heads | 4 | the contact's heads |
| modes | 8 | the complex modes of a head's chart |
| still | 2 | the still ring sets among the heads (`U = 1`); the rest turn |
| contacts | 128 | the strand's contacts, half of them complex pairs |
| ticks | 4 | `K`, the applications of the constitution (five states `x⁰` to `x⁴`) |
| frames | 4 | the ring frames a turned head reads |
| reach | 3771 | the longest region a declaration admits, which sets the contact's gain `β` and the class trits |
| lanes | 4 | the lanes of 32 |
| depth | 0 | the depth rings, which turn by located increments alone |
| carry | 32 | `C`, the carry circles among the complex contacts |
| triads | 0 | `J`, the triad junctions |
| opening | 1 | the opening's comparison |
| junction | 0 | the junction's word |
| mark | 1 | the second read, which marks the engine's own placements |

The loud face writes `hnn-field-v14l` with one word more. The level is declared on a line of its own (`level 6 2`:
six harmonics, the split after two ticks), followed by its own field's head line. Four extents stand in for laws the theory gives (depth from settling,
width from the capacity price, reads until agreement, a size belonging to its part); the table of
[THE_CONSOLIDATION §10](plans/THE_CONSOLIDATION.md#10-declared-extents-that-stand-in-for-laws) names each with the law
and where the tree already holds it.

## 5. The learner's state

A saved state is text, written and read by `Learner::to_text` and `from_text`
([`learner.rs`](../crates/engine/src/learner.rs)) and `Constitution::to_text`
([`constitution.rs`](../crates/engine/src/constitution.rs)). Lap 17's end state reads, line by line:

1. the learner's line: `hnn-field-learner-v3`, the rate bits, the count of key draws, the laps and the held step;
2. the field's head line ([§4](#4-the-declaration));
3. the field's material, 242,729 entries;
4. `level 6 2`, the level's harmonics and split;
5. the level's own head line (`hnn-field-v14 2 64 4 8 2 128 2 4 3771 2 0`);
6. the level's material, 50,640 entries;
7. the glue between the level and the field, 99,136 entries;
8. and 9. the deposit's first and second moments, one entry each for the 392,505 above;
10. the parts' rates (`parts`), where they are founded, and each entry's own rate (`rates`) where it is;
11. the pass line ([`StorePass`](../crates/engine/src/learner.rs)): `pass ROLE STORE STRETCHES LEAST OCTAVES PAIRS
    SITES [own]` and four words a slice (its name, piece, cursor and places taken). A section is the unit a deposit consumes, so its two bounds
(pairs of sites and sites) are law and are carried here. A state is never an archive of what crossed it (CLAUDE.md,
retention is a quotient). A tool that writes a state judges every line it does not mean to change (`next-pass`,
`own-states`, `found-lane`, `found-loud`).

## 6. Where a section's time goes

Read from lap 17's own lines (3,000 sections in 2,009 s on the RTX 4080 SUPER under `.local/gpu.lock`): a section
of about 41,000 sites in about 200 regions takes about 0.66 s, of which the cut and its regions take 2 to 6 ms on the
host and the card's run with the deposit about 650 ms (`regions_ms`, `deposit_ms` on each `STORE_SECTION` line). A
read of the held passage at a lap's mean (100,508 places one open, 3,717 whole masks) takes about 262 s. `FIELD_PHASES`
and `FIELD_PROFILE` print the host's part by phase and the card's launches; a timing difference between builds is read
only inside one balanced hold of the card (CLAUDE.md, waiting).

## 7. The commands

`athena train complete-language WORD …` ([`main.rs`](../crates/athena/src/main.rs)); every command pins its inputs by
SHA-256 and prints one line a unit of work.

| Word | What it does | Its lines |
|---|---|---|
| `train-store` | trains sections over the store from a state, saving states and means | `STORE_SECTION`, `STORE_PASS`, `STORE_STOPPED`, `FIELD_CARD`, `FIELD_SKIN` |
| `read-cavity` | reads the held passage at a state: one place open (`P` rows) and whole masks (`W` rows) | `cavity.tsv`, `CAVITY_LAW`, `CAVITY_SLICE`, `CAVITY_DONE` |
| `read-loudness` | the loudness of each region's places beside their surprise (`tools/loudness_table.py` reads it) | `LOUDNESS_LAW`, `LOUDNESS_SLICE`, `LOUDNESS_DONE` |
| `write-store` | the release from held prompts | `STORE_WRITE`, `STORE_WRITE_DONE` |
| `found-lane`, `found-loud` | found a part at zero on a state, every other line judged | `FOUND_LANE`, `FOUND_LOUD` and a verdict a line |
| `next-pass`, `own-states` | a state's next pass; a state whose training states are its own | `NEXT_PASS`, `OWN_STATES` |
| `parity-store` | every read asked of the card and of the host, compared whole | `STORE_PARITY_DONE` |
| `read-tension`, `read-tension-store` (host) | the covector at the strand's return beside the pair chart, the gathered current and the triads' products, by tick: at the places a forms table names (with `all`, every site, the tick's opening chart and the open row's sources, shares and locks at unit gain), or over the sections a lap meets next (`tools/tension_ruler.py` reads them) | `TENSION_LAW`, `TENSION_TEMPER`, `TENSION_BLOCK`, `TENSION_SECTION`, `TENSION_DONE` |
| `grow-crossings`, `zero-triad-return`, `found-crossing` | crossing triads grown with drawn legs and a zero return; a ruler's state with the return zeroed; the triads' legs set from a ruler's located file, the return at zero (a founding) or the ruler's (a ruler's state) | `GROW_CROSSINGS`, `ZERO_TRIAD_RETURN`, `FOUND_CROSSING` |
| `try-passes` and `write-next` (under `train`, the card; under `host` beside it), `set-leak`, `hold-families`, `found-closed` (under `host`) | passes over a small forms table by the learner's own section step, each run a keyed half open, with reads of a second table every few passes (a sum's last digit open alone, with its whole run open, its first digit; a plain row's keyed half, whole run and next place), saves, and a stream word under which no row is met twice (`ruler/tension.rs`; the long trial of November 17); a ruler's writer of one place a read, each place the last of its region, for a field compared on the next place alone; a learner with the store's leak set ([`Learner::leak`](../crates/engine/src/learner.rs)); a learner whose deposit moves named families alone; the closed face founded from a ruler's words (`crates/engine/src/closed.rs`, an attempt whose reason was withdrawn the same day, refused by the card). A study's states: no line's lap trains from one | `TRIAL_PASSES`, `TRIAL_PASS`, `TRIAL_READ`, `TRIAL_DONE`, `SET_LEAK`, `HOLD_FAMILIES`, `FOUND_CLOSED` |
| `move-store` | a state's pass moved to a store whose slice was redrawn: the slice set to the first piece at or past the places the pass has taken of it, its cursor zero, every other line of the state byte for byte (`join-store` adds slices at a new pass and sets every slice back) | `MOVE_STORE` |

Gate 3 for the engine is `bash tools/gate_engine.sh LINE BIN OUT`: parity on 3 of the line's sections, 24 sections
reproduced, and the lap's read byte for byte (CLAUDE.md, the gates).

## 8. A reading route

1. [`field.rs`](../crates/engine/src/field.rs)'s first lines: the object and the whole forward in one block.
2. [`ratio.rs`](../crates/engine/src/ratio.rs) and [`width.rs`](../crates/engine/src/width.rs): the pair, its release and the grains.
3. [`declaration.rs`](../crates/engine/src/declaration.rs) and [`constitution.rs`](../crates/engine/src/constitution.rs): what is declared and what is stored.
4. The phases in [§3](#3-the-pipeline)'s order, each module with its card module beside it.
5. [`learner.rs`](../crates/engine/src/learner.rs) and [`deposit.rs`](../crates/engine/src/deposit.rs): a section read, returned and deposited.
6. [`passage.rs`](../crates/engine/src/passage.rs) and [`store.rs`](../crates/athena/src/store.rs): what a section is made of.
7. [`release.rs`](../crates/engine/src/release.rs): the writer.

## 9. The guards

The October machine's twenty-two guards each keep one of three ends (C8c of #603). Where a guard holds on the
engine, gate 1 runs it. Where it holds as a practice rule, CLAUDE.md states it with its reason. Where its object
retired, the law it guarded stands in the guide, Lean or the atlas row named; THE_MACHINE's
[guards section](THE_MACHINE.md#guards-that-make-the-rejected-forms-impossible) keeps the constructions as their record.

| Guard | End | Where it holds now |
|---|---|---|
| 1. No tape in the moment; capacity counted | retires with its object (`SourceMoment`) | CLAUDE.md, retention is a quotient; Lean `HNN/RangedMoment`, `HNN/LeakyCapacity` |
| 2. No word outlives its return | retires with its object (`Word`) | the engine has no word: a region's read is one pass, and its temporaries end with it |
| 3. A pending ratio holds operands only | retires with its object (the resident's pending ratio) | CLAUDE.md, retention is a quotient |
| 4. No journal | practice rule | CLAUDE.md, retention is a quotient: the learner's state holds its constitution and moments, no list of deposits |
| 5. Retention only by the collapse, at aeon boundaries | retires with its object (`close_aeon`) | the aeon's law in ELEMENTARY_OBJECTS and Lean |
| 6. No clock outside the lift point and the hop clock | retires with its object; the time words stay a practice rule | CLAUDE.md: aeon, epoch and cycle, and no program counter called one |
| 7. No Lean, no file system or process in the pipeline | holds on the engine as a lint | gate 1's guard lints on `holonics-engine` (`disallowed_types`, `disallowed_methods`); `athena` is the exterior and allows them by name |
| 8. No templates | practice rule | CLAUDE.md, no catered machinery |
| 9. The codec is not the architecture | practice rule, with its repair owed | CLAUDE.md, a symbol is a word and one law reads every stream; the engine's codec is the codec's sheet until the symbol's line replaces it (`codec.rs`'s first lines) |
| 10. No scalar operand | retires with its object (`Word::pull_back`) | CLAUDE.md, loss is the logarithm of a ratio of Holons |
| 11. Learning is locating keys and depositing covectors | practice rule | CLAUDE.md, keys and navigation; learning uses the covector of a declared comparison |
| 12. No floats | holds on the engine as a lint | gate 1's guard lints on `holonics-engine` (`float_arithmetic`, `f32`/`f64` disallowed); a reading printed at the exterior allows it where it writes |
| 13. No compatibility | practice rule | CLAUDE.md, ownership and retirement |
| 14. No global solve | retires with its object (`propagation.rs`) | the atlas rows of junction-local solves, repinned to their files |
| 15. Declared charts and residuals; no free tolerance; budgets refuse | practice rule | CLAUDE.md, the precision law |
| 16. No change outlives its word | retires with its object (`Word`, the reception carry) | the reception carry's record of October 3 |
| 17. No catered machinery | practice rule | CLAUDE.md, no catered machinery |
| 18. A release reads the field, never the receiving storage | practice rule | CLAUDE.md, stores and caches |
| 19. One release per request, shown whole | practice rule | CLAUDE.md, short loops: a product's output shown whole |
| 20. The receiver's families are sealed | retires with its object (`receiver::population`) | CLAUDE.md, no catered machinery |
| 21. Seen material is never graded as unseen | practice rule | CLAUDE.md, the lessons (seen material graded as unseen) |
| 22. A run's limits are a committed pin's | practice rule | CLAUDE.md, waiting, deadlines and concurrency: never raise a limit |

## 10. What is owed

- **A founding law, and a lock that closes** (November 16, [the record](../research/records/2026-11-16_THE_LINK_THAT_SLIPS_IS_THE_LOCK_A_FAR_DIGIT_ARRIVES_AT_A_TENTH_OF_ITSELF_THE_SUMS_LAW_SITS_IN_A_PRODUCT_NO_READING_REACHES_UNTIL_THE_LOCK_CLOSES_AND_A_PART_ENTERS_BY_A_TENSION_READ_ALONG_ITS_CONSUMERS_EQUATION.md)). Every part
  of the engine enters at zero or with drawn operands; the founding law of October 24 (`contact.pool-founding`) stands in a host ruler
  (`tools/tension_ruler.py`) and in `found-crossing`, unused. A lock's temperature is one entry a head and receiver kind (`Loci::temper`),
  the open row's weights are formed afresh at every tick, and the readings of that day place the line's missing step there.

- **The cut's second part** (C5): the kernels' headers (one header a phase). The October items stand in their objects' modules. The renames stand (`Constitution`, `Declaration`, `Loci`, `Learner`, `Realization`, `Host`, `Resident`,
  `Codec`, `Forward`, `ReadLogits`, `Next`, `Receipt`, `OwnedRegion`); the module paths `field` and `hnn::field` stay.
- **The headers** (C7): every module and kernel header in §5's form (object, equations, kind and index, kernels, Lean,
  atlas, records), its dated reasoning moved to the records. Most of the cut modules still open with a line naming
  the cut; this guide's §3 is their map until then.
- **The engine line's builds** ([THE_CONSOLIDATION §11](plans/THE_CONSOLIDATION.md#11-what-the-campaign-leaves-to-the-engines-line)):
  the symbol's word in place of the codec's sheet, the extents of §4 read from their laws, and one family of sum and
  scan kernels for the five index sets of §2, each with its guess fixed first.

## 11. The theory's laws against the engine

Read before any design on how the machine learns, and kept current by it (the guide's method rule of November 17). Each row names a law
the theory states, its owner in the records or the objects, and what the engine holds in its place, by its source. The reading of
November 17 is [the record of the step back](../research/records/2026-11-17_ATHENA_DOES_NOT_COMPOUND_NOTHING_BINDS_NOTHING_TEMPERS_AND_ONE_COMPARISON_TRAINS_EVERY_PART_THE_PLAIN_ENGINE_DOES_NOT_TAKE_A_HELD_SUM_IN_TEN_PASSES_AND_A_PART_WITH_ITS_OWN_FACE_DOES.md),
corrected the same day by [the record of the dwell](../research/records/2026-11-17_ATHENA_TAKES_HELD_SUMS_WHOLE_WHEN_SHE_DWELLS_ON_ONE_WORLD_AND_THE_LINE_NEVER_DWELT.md):
the engine takes a pair law by its own descent when one world is dwelt on, and the line never dwelt.

| The theory's law | Its owner | What the engine has (November 17) |
|---|---|---|
| Every receiver has its own receipt; no global scalar or gradient; learning per contact | the objects' receiver and receipt; #405; the lens of October 24 (a difference gauged from the part's own place) | one comparison at the readout's face and one at the opening (which does take a pair law by its own descent when a world is dwelt on: the record of the dwell, below); every lock, value, product and return is trained through all that follows it (`adjoint.rs`). The closed face (`closed.rs`) is the one part whose rows are compared themselves |
| Learning is locating keys by loop closure; a founding where the tension cannot be bridged; learning steps at each founding | the keys and navigation postulate; [October 24](../research/records/2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT.md); [October 25](../research/records/2026-10-25_A_LAP_OVER_THE_SAME_TEXT_FOUNDS_ONLY_WHAT_THE_LAST_LAP_MADE_REACHABLE_SO_LEARNING_CLIMBS_STAIRCASES_AND_STEPS_AT_EACH_FOUNDING.md); atlas `contact.pool-founding`, `key.ring-closed-from-rows-menu` | no founding law. Growth is by hand (`found-lane`, `grow-crossings`, `found-closed`), its operands drawn or solved by a host ruler |
| No store is at rest: a store stands by upkeep, relaxes and has a finite quality; retention is a quotient | the stores-and-caches law (November 11); the retention contract; atlas `store.finite-quality` | the deposit's leak is a state of the learner since November 17 (`Learner::leak`: each entry relaxes by `2^(−leak)` of itself after its step), absent from every line's state and unread on anything but a small world; nothing is pruned or merged |
| A temperature is a store's state | the method rule of November 13; atlas `deposition.rate-temperature-standing-spread` | the deposit's rate is constant but for a part's octave moved at a lap's end by its travel; every part stood at octave 0 in lap 94's state. No cooling |
| A lock binds: past its bifurcation a row commits to its sources | the parametron (the Ising lock, the pump as inverse temperature) | a row is a soft mixture; its temperature is one deposited entry a head and receiver kind. The rows of November 17 hold 0.29 to 0.39 of their weight on the sources a sum's place needs |
| A symbol is a word: a located turn on a few coprime rings, its rows shared at a residue | the method rule of November 12; the located transport of October 5; [October 26](../research/records/2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES.md) | a class indexes free rows of the encoding (three tables of `A + 1` rows of `D`); a symbol enters a carry circle as its drive and never as its turn |
| A composite is its factors' strand, composed by the machine; a level reads units the level below committed | the same rule; the level on its news (November 13) | the level's sites are landmarks of news, and no unit is founded as a symbol; a higher level reads mixtures |
| A lap rereads: learning passes again over the same composition, and the machine's own navigation chooses what it reads next | the staircase record (October 25) and its lens (one can pass over any sample again and keep deriving); the keys and navigation postulate; Brandon, November 17 16:08Z | the cut takes the slice with least progress against its quota, each slice's pieces in order, before any forward, and never returns (`passage::Cut::next`): 701 MB taken once by lap 94, every section a mix of all seven slices. About 160 to 200 thousand records of one law, in any arrangement tried, took a held sum ([the record](../research/records/2026-11-17_ATHENA_TAKES_HELD_SUMS_WHOLE_WHEN_SHE_DWELLS_ON_ONE_WORLD_AND_THE_LINE_NEVER_DWELT.md)); the line met 1.6 million such sums at a hundredth of each section's places, under states that often open an answer with its operands, and never did (unexplained by the pass alone) |
| Generation refines a joint field and releases its boundary | the generation and action law | the release draws a run of places from one read's faces, each from its own face (`release.rs`) |

