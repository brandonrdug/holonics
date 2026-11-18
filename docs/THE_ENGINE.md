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
| cut | a stretch of the store's passage and its one state: a keyed draw (`state_of`), the release's own state at a crossing of its octaves (`own_state_of`, the pass's word `own`), or the frontier's (`frontier_state_of`, the pass's words `frontier E`: the context known and the next place alone open, the region ending there; atlas `tower.store-frontier-state`) | [`passage.rs`](../crates/engine/src/passage.rs), [`region.rs`](../crates/engine/src/region.rs), [`codec.rs`](../crates/engine/src/codec.rs) | host only | |
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
part it sizes (CLAUDE.md, Method: a size belongs to its part). From lap 75 the store line's state declares
`hnn-field-v14x 244 128 4 8 2 128 4 4 3771 4 0 32 10 1 0 1 0 1`: ten crossing triads, and 402,805 entries with the level and the glue
(253,029, 50,640 and 99,136 at lap 94); this section's table and §5 and §6 below still describe lap 17:

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
11. where they are carried, the leak (`leak`) and the steps' carried remainders (`remainder`, one an entry on `2^(−16)` of its grain,
    November 18: without it a rate cooler than 12 truncates a face-grain step to nothing);
12. the pass line ([`StorePass`](../crates/engine/src/learner.rs)): `pass ROLE STORE STRETCHES LEAST OCTAVES PAIRS
    SITES [own]`, four words a slice (its name, piece, cursor and places taken), and where set the world's clause and, last, the
    frontier's share (`frontier E`, of every eight stretches). A section is the unit a deposit consumes, so its two bounds
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
| `read-cavity` | reads the held passage at a state: one place open (`P` rows), whole masks (`W` rows), and each place at the frontier, every place before it known and the region ending there (`F` rows of `frontier.tsv`, its place the count of places known) | `cavity.tsv`, `frontier.tsv`, `CAVITY_LAW`, `CAVITY_SLICE`, `CAVITY_FRONTIER`, `CAVITY_DONE` |
| `read-loudness` | the loudness of each region's places beside their surprise (`tools/loudness_table.py` reads it) | `LOUDNESS_LAW`, `LOUDNESS_SLICE`, `LOUDNESS_DONE` |
| `write-store` | the release from held prompts | `STORE_WRITE`, `STORE_WRITE_DONE` |
| `found-lane`, `found-loud` | found a part at zero on a state, every other line judged | `FOUND_LANE`, `FOUND_LOUD` and a verdict a line |
| `next-pass`, `own-states` | a state's next pass; a state whose training states are its own | `NEXT_PASS`, `OWN_STATES` |
| `set-frontier`, `set-rate`, `zero-level-return` (under `host`) | a state whose pass reads a share of its stretches at the frontier; a state with the deposit's rate set and, on request, its steps' remainders carried; a ruler's state with the level's prolongation at zero | `SET_FRONTIER`, `SET_RATE`, `ZERO_LEVEL_RETURN` |
| `parity-store` | every read asked of the card and of the host, compared whole | `STORE_PARITY_DONE` |
| `read-tension`, `read-tension-store` (host) | the covector at the strand's return beside the pair chart, the gathered current and the triads' products, by tick: at the places a forms table names (with `all`, every site, the tick's opening chart and the open row's sources, shares and locks at unit gain), or over the sections a lap meets next (`tools/tension_ruler.py` reads them) | `TENSION_LAW`, `TENSION_TEMPER`, `TENSION_BLOCK`, `TENSION_SECTION`, `TENSION_DONE` |
| `grow-crossings`, `zero-triad-return`, `found-crossing` | crossing triads grown with drawn legs and a zero return; a ruler's state with the return zeroed; the triads' legs set from a ruler's located file, the return at zero (a founding) or the ruler's (a ruler's state) | `GROW_CROSSINGS`, `ZERO_TRIAD_RETURN`, `FOUND_CROSSING` |
| `try-passes` and `write-next` (under `train`, the card; under `host` beside it), `read-level` (with `links`, every link of the level's equation and the covector at its locus, for `tools/level_links_ruler.py`), `set-leak`, `hold-families`, `found-closed` (under `host`) | passes over a small forms table by the learner's own section step, each run a keyed half open, with reads of a second table every few passes (a sum's last digit open alone, with its whole run open, its first digit; a plain row's keyed half, whole run and next place), saves, and a stream word under which no row is met twice (`ruler/tension.rs`; the long trial of November 17); a ruler's writer of one place a read, each place the last of its region, for a field compared on the next place alone; a region's level written out for a ruler (its epochs' anchors, each place's news, each epoch's state); a learner with the store's leak set ([`Learner::leak`](../crates/engine/src/learner.rs)); a learner whose deposit moves named families alone; the closed face founded from a ruler's words (`crates/engine/src/closed.rs`, an attempt whose reason was withdrawn the same day, refused by the card). A study's states: no line's lap trains from one | `TRIAL_PASSES`, `TRIAL_PASS`, `TRIAL_READ`, `TRIAL_DONE`, `SET_LEAK`, `HOLD_FAMILIES`, `FOUND_CLOSED` |
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

- **A passage read at its boundary by two streams** (November 18, [the frontier record](../research/records/2026-11-18_THE_WRITERS_FRONTIER_IS_THE_PASSAGES_CODE_IN_PLACE_ORDER_THE_LINE_NEVER_READ_IT_IT_GAINS_OUT_TO_HUNDREDS_OF_KNOWN_PLACES_AND_A_SHARE_OF_STRETCHES_THERE_TRADES_THE_FILL_IN_READING_FOR_IT.md) §6; the record of the dwell §13). The frontier's code is the passage's code in place order, and a
  frontier region compares one place for its whole read (atlas `tower.store-frontier-state`). The build that compares every place of
  a passage at its own frontier in one forward stands so far on the host alone:
  - built on the host: the known stream (`Sided::Before` in the tick: every site hears only what stands before it; a ruler's forward
    at `3`, `Constitution::ruler_far`) and its return, checked by the code's difference; the two streams read by one tick
    (`Constitution::strand_pass`, `Sided::Strand`: the open places are sites of the known stream's batch, each at the place of the
    known site of its index, `ClassLists::twins_from`; a site's near field, falloff, plain skin, strand mate and circle are read by
    its place, and an open place is heard by no one), whose faces are the same bits at every place as the open last place of the
    region that ends there; and its return (`Constitution::strand_returned`, the same `tick_return` over the joined sites), checked
    by the code's difference on 224 probes and standing within 18 millionths of the sum of the frontier regions' covectors. A second
    tick written for the open places (`Constitution::strand_faces`) is kept as the joined tick's oracle, and the chart's single
    stream of veiled sources (`Constitution::chart_faces`) as a reading (two and a half nats from the state as trained; the two
    streams half a nat).
  - built on the card, its first step (November 18, 13:20 UTC): the known stream. It is a batch's word (`FieldWords::before`): a support
    entry and a crowd on the after side meet no site, a still head shares a class's face among its members before the receiver, the
    opening and the moments read no after row, an odd strand contact has no mate, a circle scanned from the right stays at rest, and a
    region's first site is a row not computed; the level is unheard and the field reads once. It is the host's forward under a ruler at
    `3` and, as a region's own word (`Region::before`, atlas `tower.region-known-stream`), a law of the region: a section's known
    streams run as a second group on the card, each one's return standing for both reads where the field reads twice, and the faces
    and the training path's words stand in the regions' order. The opening is compared there as the retarded one (the opening an open
    place of the second stream begins from). Card against host, bit for bit, on four fields read once and twice, under the ruler at
    `3` and `4` and in sections of the law holding known streams (`the_known_stream_on_the_card_reads_the_hosts_bits`, 24 cases). The
    pass carries it for the frontier's stretches (`frontier E before`, `StorePass::before`, set by `set-frontier … before`), the held
    read writes the frontier's rows read so (`K` rows, where the pass says so or on the word `known`), and the one-place writer writes a
    state whose pass says so in that regime.
  - owed, in order: the open places as the batch's second region and its return, bit for bit against `Constitution::strand_pass` and
    `strand_returned`; a word of the pass for stretches read by two streams and the learner's section taking them; the held read; then
    the level and the second read's mark made one-sided, which the known stream leaves out and which are worth 0.16 nats at the
    frontier's place.
  - the card's form for the second stream (read in the kernels, November 18; `agent-inferred` until its parity holds): a passage is
    two regions of the batch. The known region's sites hear only what stands before them (built, above). Its open
    places are a second region of as many open sites whose source side is the known region's (its keys, values and class lists, its
    mate's `b` at the place before, its circle as it stands at the place), heard by no one. A site's position stays its place in both
    regions, and a region's block of scores stays its square, so a passage costs two regions' pairs where the host's joined batch
    would cost four. The open places' covectors on what they heard land on the known region's sites, and a circle's covector takes
    the open place's term beside the known site's. The open places' clocks, read from their faces after each tick, and their retarded
    moments on those clocks are the cavity kernels' with no after rows. The host's joined tick is its reference: a row is one
    receiver's, and a row's sum is the same bits in either layout.
  - why it is the next build: the frontier's fall under the control is 0.1603 + 0.0458 ln(sections / 3,000) over six laps with
    the share, a fifth lane of 32 buys nothing there in its first lap, and a frontier comparison costs a region's whole read today
    (the frontier record §5 and §7).

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
| A temperature is a store's state | the method rule of November 13; atlas `deposition.rate-temperature-standing-spread` | the deposit's rate is one constant: `2^(−12)` in every state of the store line from lap 1 to lap 94, every part at octave 0, no `rates` line. `RateParts::updated` has no caller outside tests and cannot go under the base, and the step's transfer is printed each section and never acted on (`store.rs:5`). The state is a walk at that step's noise (mean `|m|/√v` 0.19 where noise alone gives 0.21; successive moves point against each other; the field's material moves 2% of its rms a lap at lap 21 and at lap 93). A cooling law is owed and is what the rule asks for: on November 4 a constant step's floor read 0.032 to 0.053 nats a place and cooling released 0.043 at once, and the law was retired that day because its price read empty ([the audit](../research/records/2026-11-18_THE_LINE_FLAILS_BECAUSE_A_FIXED_RATE_DEPOSIT_TRACKS_AN_UNSHUFFLED_MOVING_TERRAIN_PARTS_ARE_ADDED_AND_NEVER_REMOVED_AND_PAST_CONFIGURATIONS_WERE_BARRED_BY_NAME.md) §1.1; [its companion](../research/records/2026-11-18_COOLING_WAS_MEASURED_ON_NOVEMBER_4_AND_RETIRED_THE_LINES_LEVEL_IS_TRADED_BY_ITS_MIX_AN_OPEN_PLACE_IS_NEVER_A_SOURCE_AND_A_CHANGE_TO_A_LINE_RUNS_BESIDE_A_CONTROL.md) §4, with a direct read's guesses fixed) **November 18:** the rate was read as a state for one lap from lap 70 (`set-rate`, with the step's remainder carried so a cool rate still moves a face-grain entry): at `2^(−12)` successive thousand-section moves point against each other (cosines −0.195, −0.171) and the end state reads 0.017 nats a place above its lap's mean; at `2^(−16)` they align (+0.227, +0.130) and the end reads as the mean; at `2^(−14)` the cosines stand at zero. The level at the mean moves by 0.003 at most and the writes not at all ([the record](../research/records/2026-11-18_A_COOLER_DEPOSIT_STOPS_THE_STATES_WALK_AND_LEAVES_THE_LEVEL_AND_THE_WRITES_WHERE_THEY_WERE_AND_THE_LEVEL_IS_WORTH_A_SIXTH_OF_A_NAT_WHERE_THE_WRITES_ARE.md)). A law that rests the rate where its travel's cosine is zero is owed as upkeep; it is not what holds the level. |
| A lock binds: past its bifurcation a row commits to its sources | the parametron (the Ising lock, the pump as inverse temperature) | a row is a soft mixture; its temperature is one deposited entry a head and receiver kind. The rows of November 17 hold 0.29 to 0.39 of their weight on the sources a sum's place needs |
| A symbol is a word: a located turn on a few coprime rings, its rows shared at a residue | the method rule of November 12; the located transport of October 5; [October 26](../research/records/2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES.md) | a class indexes free rows of the encoding (three tables of `A + 1` rows of `D`); a symbol enters a carry circle as its drive and never as its turn |
| A composite is its factors' strand, composed by the machine; a level reads units the level below committed | the same rule; the level on its news (November 13) | the level's sites are landmarks of her own news (an epoch 8.6 places and 9.5 nats on the night's state, 36% of them led by a word's first letter), and the level's state of an epoch holds under a tenth of any of its symbols, 17% of its identity and nothing of the epoch before: it has no comparison at its own grain ([the record](../research/records/2026-11-17_ATHENA_TAKES_HELD_SUMS_WHOLE_WHEN_SHE_DWELLS_ON_ONE_WORLD_AND_THE_LINE_NEVER_DWELT.md) §19; `read-level`, `tools/level_ruler.py`). Read against the tree, a level is a codec that carries its decoder and closes a scale square, both read at the symbols' face; the built one was founded on a saddle, has no receipt at its grain and folds a winding epoch ([the design record](../research/records/2026-11-17_A_LEVEL_IS_A_CODEC_THAT_CARRIES_ITS_DECODER_AND_CLOSES_A_SCALE_SQUARE_BOTH_READ_AT_THE_RECEIVERS_FACE_THE_BUILT_LEVEL_WAS_FOUNDED_ON_A_SADDLE_HAS_NO_RECEIPT_AT_ITS_GRAIN_AND_FOLDS_A_WINDING_EPOCH.md), nothing built; atlas `tower.level-receipt-codec-and-square`). Read link by link on November 18 (its §9; `read-level ... links`, `tools/level_links_ruler.py`): the moment holds a unit's strand (its bag at 721 thousandths, its order at 522), the built restriction keeps what a drawn one keeps (480 and 169 against 410 and 218), and nothing linear in the units relieves the fine comparison at the level's locus, so the one comparison gives a level no slope (atlas `tower.level-restriction-is-its-draw`, `deposition.no-linear-tension-at-the-levels-locus`). The chart addresses a place by its news phase, so three quarters of the places under one nat share their sixth of a turn with the place before and a level cannot hand a dark place its own turn; her excess stands there, and it waits on the place level's binding order, about four symbols (its §10; atlas `tower.news-phase-chart-blind-to-dark-order`). A face fitted at each tick: the opening codes like a count of two symbols, the ticks before the split do not bind at the compared place, each tick after it binds one symbol, and what the level prolongs enters before those ticks; what the written places it reads hold at the split is unread (its §11; `tools/tick_face_ruler.py`; atlas `tower.field-place-binds-one-symbol-a-late-tick`) **November 18:** with the level's prolongation zeroed the line's own means read 0.15 to 0.21 nats a place higher with one place open and 0.23 to 0.29 at whole masks (laps 70 and 94), so the field as trained leans on the level's return, with a restriction that keeps what a drawn one keeps. |
| A lap rereads: learning passes again over the same composition, and the machine's own navigation chooses what it reads next | the staircase record (October 25) and its lens (one can pass over any sample again and keep deriving); the keys and navigation postulate; Brandon, November 17 16:08Z | the cut takes the slice with least progress against its quota, each slice's pieces in order, before any forward, and never returns (`passage::Cut::next`): 701 MB taken once by lap 94, every section a mix of all seven slices. About 160 to 200 thousand records of one law, in any arrangement tried, took a held sum ([the record](../research/records/2026-11-17_ATHENA_TAKES_HELD_SUMS_WHOLE_WHEN_SHE_DWELLS_ON_ONE_WORLD_AND_THE_LINE_NEVER_DWELT.md)); the line met 1.6 million such sums at a hundredth of each section's places, under states that often open an answer with its operands, and never did (unexplained by the pass alone) |
| Generation refines a joint field and releases its boundary | the generation and action law | the release draws a run of places from one read's faces, each from its own face (`release.rs`) The line's training states (`passage::state_of`) are half writer states in the octave order of distance, every open place compared and a true end given, and half masks at `τ = u²`; a place at a place-order frontier with everything before it known was compared only among those. **November 18:** the frontier's state is a share of the pass (`frontier E`, atlas `tower.store-frontier-state`), the held read cuts it on held text, and the writer that meets it is one place a read in place order (`write-next`); its first lap's guess is G-1118-3 (`research/records/receipts/2026-11-18_frontier/`). |

