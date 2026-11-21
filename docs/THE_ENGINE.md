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
`2^(−30)`, a series row's exponential faces on `2^(−62)` with its shares on `2^(−63)`, covectors on `2^(−24)`,
the contact's on `2^(−40)` and the deposit's on `2^(−32)`, and a code's reading on `2^(−20)` bits
([`width.rs`](../crates/engine/src/width.rs)). Every product's remainder below its grain
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
forward; each module's own first lines carry its derivation. Kernels are named as the kernel sources name them. Every
kernel stands in `kernels/field.cu` but the cavity's six, which stand in `kernels/field_cavity.cuh`;
`kernels/field_moment.cuh` holds the moment kernels' helpers; `field.cu` includes both headers, and the build compiles
one image. The card module named before a kernel is the file under
[`crates/engine-cuda/src/hnn/`](../crates/engine-cuda/src/hnn/mod.rs) that launches it, and a trailing `*` stands for
every kernel of that stem.

| Phase | Object and equation | Host module | Card module and kernels | Kind |
|---|---|---|---|---|
| cut | a stretch of the store's passage and its one state: a keyed draw (`state_of`), the release's own state at a crossing of its octaves (`own_state_of`, the pass's word `own`), or the frontier's (`frontier_state_of`, the pass's words `frontier E`: the context known and the next place alone open, the region ending there; atlas `tower.store-frontier-state`) | [`passage.rs`](../crates/engine/src/passage.rs), [`region.rs`](../crates/engine/src/region.rs), [`codec.rs`](../crates/engine/src/codec.rs) | host only | |
| rings | turned ring sets on the solenoid's periods, `U_(t,m) = e^(2πi (t mod n_m)/n_m)`; still sets `U = 1`; paces and blank clocks | [`navigator.rs`](../crates/engine/src/navigator.rs) | `resident.rs` (a batch's base): `field_paces`, `field_twin_clocks` (the open places of a second stream), `field_skin_addresses`, `field_pframes`; `clock.rs`: `field_clock_fill`, `field_skin_fill`, `field_blank_rates` | gate, a site |
| moment | `s_t = Σ_k ζ^(k−t) D(\|t−k\|) E±(u_k)` at a turned mode: the source enters as phase-carried moments | [`moment.rs`](../crates/engine/src/moment.rs), [`field/moment.rs`](../crates/engine/src/field/moment.rs) | `moment.rs`: `field_moment_strands_all`, `field_moment_admit_paced_all`, `field_moment_prefix_paced_all`, `field_moment_paced_all`, `field_moment_scatter_all`, `field_cavity_moment_all`; `resident.rs`: `field_twin_moment`; `contact.rs`: `field_moment_add*` (a tick's values take their site's moment) | sum over a site's strand |
| open | `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + C s_t + b_s`; an open site opens on its moment, a marked site with its mark on the second read; where the opening is compared, the cavity opening through its own lift | [`moment.rs`](../crates/engine/src/moment.rs) | `resident.rs`: `field_open`, `field_echo_apply`, `field_mark_shares`; `moment.rs`: `field_cavity_open` | gate, a site |
| chart | `r̂_t = x_t/‖x_t‖_rms`, `k_t = W_k r̂_t + b_k`, `p_t = W_p r̂_t + b_p`, `v_t = V r̂_t + b_v`; framed `k̃ = U ⊙ k` | [`contact.rs`](../crates/engine/src/contact.rs), [`navigator.rs`](../crates/engine/src/navigator.rs) | `contact.rs`: `field_chart`, `field_affine_tiled_*` (on 32-bit inputs `field_affine_tiled_tc_x32`: each operand's words as four digit planes of eight bits, `field_tc_planes`, summed on the card's integer tensor units, the same integers), `field_affine_two_*`, `field_unit`, `field_unit_probe`, `field_frame`, `field_frame_probe` | gate, a site |
| classes and support | a key's and a probe's shells `Σ_l 3^l σ_l`; `S_i^h` the near field `0 < \|i−j\| < 6` and the far sources whose key's class meets the probe | [`contact.rs`](../crates/engine/src/contact.rs) | `contact.rs`: `field_classes`, `field_sums` | gate, a site |
| contact | `z_ij = 2^(−β) Σ_m [D_m Re(conj(p̃_im) k̃_jm) − D_m² \|k̃_jm\|²/2] − ⌊log₂ \|i−j\|⌋ − ψ_(h,k) ⌊log₂ \|i−j\|⌋` (a still head's falloff the octave of its class's count; `ψ` each head's friction of distance where declared, atlas `contact.friction-of-distance`), `e_ij = 2^(z_ij)`, `y_i = conj(U_i) ⊙ Σ e_ij D ṽ_j / Σ e_ij`, `x ← x + O y + b_o` | [`contact.rs`](../crates/engine/src/contact.rs), [`ratio.rs`](../crates/engine/src/ratio.rs) | `contact.rs`: `field_exposure` (a row's carrier, read before the launch), `field_contact_l3` to `field_contact_l20` (the contact, one kernel a count of the row's limbs), `field_echo_trips`; `resident.rs`: `field_exponential` (the exponential's resident face, once at the upload) and the rows' readings `field_row_currents`, `field_held_rows` | gate (the lock), then sum over the sources; sum over the ticks |
| strand | the pair `x_t ← x_t + W_c (a_t · b_(s(t))) + b_c`; the carry circles `Q_t = κ_t b_t + γ_t Q_(t∓1)`, `γ = γ̂(q)/(1 + d)`, or with the declaration's pump word `Q_t = κ_t b_t + γ_t Q_(t∓1) + η_t conj(Q_(t∓1))` with `γ = γ̂(q)/(1 + d + n)`, `η = p/(1 + d + n)`, `κ = N₀ d/(1 + d + n)` (`carry_gate_pumped`, atlas `contact.pumped-carry`); the triad, on the strand's mates `p_k(t) = α_k(t) β_k(t−1)`, `c^T_k(t) = p_k(t) γ_k(t+1)`, or with the declaration's crossing word every leg at the site, `p_k(t) = α_k(t) β_k(t)`, `c^T_k(t) = p_k(t) γ_k(t)` (`triad_products`) | [`carry.rs`](../crates/engine/src/carry.rs) | `contact.rs`: `field_pair`, `field_pair_gamma`, `field_pair_scan`, `field_pair_scan_face`, `field_triad`; `resident.rs`: `field_carry_gates_read` (a reading). The card's `carry.rs` points a tick's words at the triads' carriers and launches nothing | gate, then chain along the strand |
| level | a level on its news: epochs led by sites, the landmarks of the news below (`ρ_t ≥ σ`), run on their own clock | [`level.rs`](../crates/engine/src/level.rs), [`field/scale.rs`](../crates/engine/src/field/scale.rs) | `resident.rs`: `field_level_news`, `field_level_news_strand` (the news the host cuts the epochs from); `level.rs`: `field_level_chart32`, `field_level_chart32_spans`, `field_level_unchart` | gate, then sum over an epoch |
| face | `z_t(a) = ⟨E(a), R r̂(x^K_t) + b_R⟩ + c_a`, `p̂_t(a) = 2^(z_a) / Σ_b 2^(z_b)` at the open sites; the loud face where declared | [`face.rs`](../crates/engine/src/face.rs) | `resident.rs`: `field_tied_face_tiled`, `field_tied_face_sharp`, `field_face`, `field_face_at_class`, `field_loud_beta`, `field_gather_rows32` (a reading's gather) | gate, an open site |
| comparison | the joint code `(m/K) Σ −log₂ p̂_t(u_t)` over a state's `K` open sites among `m`; a port compared through its coupling | [`face.rs`](../crates/engine/src/face.rs), [`region.rs`](../crates/engine/src/region.rs) | `adjoint.rs`: `field_face_covector`, `field_face_weigh`, `field_face_set` | sum over the open sites |
| return | the covector `p̂ − q` returned through the `K` ticks by the operands that produced each carrier | [`adjoint.rs`](../crates/engine/src/adjoint.rs) | `adjoint.rs`: `field_ratio_adjoint`, `field_current_back`, `field_pace_current_back`, `field_contact_rows`, `field_contact_columns`, `field_spread`, `field_pair_back`, `field_pair_scan_pre`, `field_pair_scan_back`, `field_pair_gate_back`, `field_triad_back`, `field_unit_back`, `field_unit_back_probe`, `field_unframe`, `field_pace_frame_back`, `field_pace_skin_back`, `field_pace_kappa_back`, `field_pace_c_back`, `field_tied_back_e`, `field_tied_back_y_tiled`, `field_loud_back`, `field_mark_back`, `field_mark_rows`, `field_encoding`, `field_moment_accumulate`, `field_twin_take_wide`, `field_twin_clock_back`, `field_add`; `contact.rs`: `field_transposed_tcs` (the tensor units' route; `field_transposed`, the tile form, beside it), `field_outer_*`, `field_outer_bound_*` (the material's covector); `resident.rs`: `field_wide_add`; `moment.rs`: `field_moment_ds_all`, `field_moment_skinned_all`, `field_moment_return_paced_all`, `field_moment_strand_return_all`, `field_moment_pace_back_all`, `field_cavity_terms_all`, `field_cavity_scan_all`, `field_cavity_return_paced_all`, `field_cavity_pace_back_all`; `clock.rs`: `field_blank_dz`, `field_blank_live_scan`, `field_blank_bias_enc`, `field_blank_dy`, `field_blank_lift_read`, `field_blank_dx`; `level.rs`: `field_level_chart64`, `field_level_chart64_spans`, `field_level_unchart` | the forward's kinds, reversed |
| deposit | the two moments of the covector at `2^(−3)` and `2^(−8)`, then each entry's step `m/(⌊√v⌋ + 1)` at `2^(−rate)`. The rate is the learner's one `rate_bits`, unless its state carries a `parts` line (a founded part's octaves under it) or a `rates` line (an entry's own); no command and no law moves a part's octave (`RateParts::updated` and `part_travel` are called by tests alone). Where the state carries them, a step's remainder under the entry's grain is kept for the next section (`remainder`) and each entry relaxes by `2^(−leak)` of itself after its step (`leak`) | [`deposit.rs`](../crates/engine/src/deposit.rs), [`learner.rs`](../crates/engine/src/learner.rs) | host, beside the card | chain over the sections |
| mean | the mean of the states after each section since the last save, the state a line's level is read from (`MEAN.k`) | [`deposit.rs`](../crates/engine/src/deposit.rs) (`MaterialMean`) | host | sum over a lap |
| release | the writer: every answer place opened beside the known prompt, resolved by octaves of distance from it, each drawn from its face on the read of the region as it stands | [`release.rs`](../crates/engine/src/release.rs) | the forward's kernels, one read a place | chain over the reads |

The card's resident realization ([`resident.rs`](../crates/engine-cuda/src/hnn/resident.rs)) opens a region batch,
uploads it, holds the pools and implements `Realization`; [`card.rs`](../crates/engine-cuda/src/hnn/card.rs)
owns the context, the module, the stream and the census; [`profile.rs`](../crates/engine-cuda/src/hnn/profile.rs)
holds the launch records and the yardsticks (`field_yard_*`, `field_series_check`). A ruler
([`ruler.rs`](../crates/engine/src/ruler.rs)) reads the machine without changing what the state carries or the deposit
consumes.

The Lean owners of the phases stand under `lean/Holonics/HNN/`: `Moment`, `RangedMoment` and `ReframedMoment` (the
moment), `Contact` and `ContactBreak` (the contact), `CarryGate` (the carry circle's passivity), `TriadGauge` (the
triad), `TickBlocks`, `TickFamily` and `TickStanding` (the ticks), `ReleaseRun` (a read that releases a run), and
`lean/HolonicsResearch/HNN/ReadsTwice` (the second read).

## 4. The declaration

The declaration is the field's head line, written and read by `Declaration::to_text` and `from_text`
([`declaration.rs`](../crates/engine/src/declaration.rs)). Its head word names the last part the field declares, and
each head word's line is the line before it with one word more:

| Head word | Words after it | The word it adds |
|---|---|---|
| `hnn-field-v14` | 11 | alphabet, width, heads, modes, still, contacts, ticks, frames, reach, lanes, depth |
| `hnn-field-v14e` | 12 | carry `C`, more than zero |
| `hnn-field-v14f` | 13 | triads `J`, more than zero; `C` is written even at zero from here on |
| `hnn-field-v14g` | 14 | the opening's word, `1` |
| `hnn-field-v14j` | 15 | the junction's word, `1`; the opening's is `0` or `1` from here on, as each later line writes the flags before its own |
| `hnn-field-v14m` | 16 | the mark's word, `1` |
| `hnn-field-v14l` | 17 | the loudness's word, `1` |
| `hnn-field-v14x` | 18 | the crossing's word, `1`; it needs triads |
| `hnn-field-v14c` | 19 | closed `E`, more than zero; the crossing's word is `0` or `1` |
| `hnn-field-v14p` | 20 | the pump's word, `1`; closed `E` is written even at zero |
| `hnn-field-v14q` | 21 | the lane leak's word, `1`; the pump's is `0` or `1` |
| `hnn-field-v14r` | 22 | the friction's word, `1`: each head's friction of distance (`ψ`, two a head, `Loci::friction`); the leak's is `0` or `1` |

A field writes the first of these lines that holds everything it declares. `hnn-field-v13` (ten words, no depth) is
read as a field with no depth ring. `hnn-field-v14k` and `hnn-field-v14t` are refused: their states are receipts.

Each word with the part it sizes (CLAUDE.md, Method: a size belongs to its part). The value is the store line's, in
the state its laps start from since November 18 (lap 70's): `hnn-field-v14m 244 128 4 8 2 128 4 4 3771 4 0 32 0 1 0 1`.

| Word | Value | What it sizes |
|---|---|---|
| alphabet | 244 | `A`, the face's classes; each encoding (`E`, `E₋`, `E₊`) carries one row more, the open place's |
| width | 128 | `D`, one row length every block shares, read in `lanes` registers of `D/lanes`; reached by copies ([THE_CONSOLIDATION §10](plans/THE_CONSOLIDATION.md#10-declared-extents-that-stand-in-for-laws)) |
| heads | 4 | `H`, the contact's heads; head `h` is of ring set `h mod frames` |
| modes | 8 | `n`, the complex modes of a head's chart |
| still | 2 | the first ring sets, which are still (`U = 1`); the rest are turned, and a head of a turned set carries a moment and a pace |
| contacts | 128 | `f`, the strand's pair contacts, real: `f/2` complex contacts, as many toward each strand mate |
| ticks | 4 | `K`, the applications of the constitution (five states `x⁰` to `x⁴`) |
| frames | 4 | the ring sets, the founding's heads; every grown head copies the set of its index |
| reach | 3771 | the most sites a region may span, which sets the contact's gain `β`, the listener's shift, the class trits and a row's carrier |
| lanes | 4 | the registers the width is read in, each a ratio to its own power (here 32 coordinates each); these are face lanes, and a card's thread is never called a lane (the guide's precision law) |
| depth | 0 | the last turned ring sets that turn by located increments alone |
| carry | 32 | `C`, the carry circles, the last `C` of the complex contacts; even, as many scanned from each side |
| triads | 0 | `J`, the complex triads |
| opening | 1 | the cavity opening compared through a lift of its own, `R⁰` |
| junction | 0 | a tick's return of the state two ticks before, `x^(k+1) = v^k + Γ^k (v^k − x^(k−1))` |
| mark | 1 | the second read, which marks the field's own placements (one strength an encoding) |
| loud | (not written) | the face reads its site's lane powers as its sharpness (`κ` a lane and `b`) |
| crossing | (not written) | the triads' three legs stand at the site ([§3](#3-the-pipeline), the strand) |
| closed | (not written) | `E` closed characters with a key a class; an attempt, which the card refuses and whose keys take no deposit |

The material this declaration lays (`Loci::new`, in the state's order) is 242,729 entries: the three encodings 94,080;
the key, value and probe charts 8,256 each with their biases; the contact's return 8,320; the pair's two charts 16,512
each and its return 16,512; the readout's lift and the class bias 16,628; the moments' two encodings 15,680; the locks'
temperatures 8; the paces 490; the moment's chart 8,320; the lift's bias 128; the carry circles' charts 8,256; the
opening's lift 16,512; and the mark's strengths 3. Ten triads add 10,300 (their three charts, biases and return).

A level is declared on a line of its own after the field's material (`level 6 2`: six harmonics of the news phase, the
split after two ticks), followed by its own field's head line (`hnn-field-v14 2 64 4 8 2 128 2 4 3771 2 0`: by `level_declaration`
an alphabet of two, no carry circle, triad or opening, and the ticks the field has after its split; its width of 64 in
two lanes is the width its founding met, and `found-lane` grows the field's lanes and keeps the level), that field's
material (50,640 entries) and the glue between the two (99,136: `A`, `b_A`, `B`, `b_B`). With them the line's state
holds 392,505 entries. From lap 75 to lap 94 the line's states declared
`hnn-field-v14x 244 128 4 8 2 128 4 4 3771 4 0 32 10 1 0 1 0 1`, ten crossing triads, and 402,805 entries (253,029,
50,640 and 99,136).

Four extents stand in for laws the theory gives (depth from settling, width from the capacity price, reads until
agreement, a size belonging to its part); the table of
[THE_CONSOLIDATION §10](plans/THE_CONSOLIDATION.md#10-declared-extents-that-stand-in-for-laws) names each with the law
and where the tree already holds it.

## 5. The learner's state

A saved state is text, written and read by `Learner::to_text` and `from_text`
([`learner.rs`](../crates/engine/src/learner.rs)) and `Constitution::to_text`
([`constitution.rs`](../crates/engine/src/constitution.rs)). Its lines, in the order the code writes them, with the
counts of the store line's state ([§4](#4-the-declaration)):

1. the learner's line, `hnn-field-learner-v3 RATE DRAWN LAPS HELD`: the deposit's rate in bits, the key bytes drawn
   (four a draw), the laps, and the held step's halvings or `-`;
2. the field's head line ([§4](#4-the-declaration));
3. the field's material, 242,729 entries;
4. where the field has a level, `level 6 2`, the level's harmonics and split;
5. the level's own head line;
6. the level's material, 50,640 entries;
7. the glue between the level and the field, 99,136 entries, and after them, where `open-level` founded it, the block a
   one-sided stream reads the level through (49,920 more);
8. the deposit's first moment and
9. its second, one entry each for the 392,505 above;
10. the held step, only where the learner's line names one;
11. `parts`, the contact count the founded parts are told from and each part's octaves, where they are founded;
12. `rates`, each entry's own rate, where the state carries them;
13. `leak K`, where the leak is set;
14. `remainder`, the steps' carried remainders, one an entry on `2^(−16)` of its grain, where they are carried: without
    the line a step that stands under one grain of its entry is dropped (`Learner::remainder` gives the line's counts),
    and a founding sets a carried remainder back to zero;
15. the pass line ([`StorePass`](../crates/engine/src/learner.rs)), last: `pass ROLE STORE STRETCHES LEAST OCTAVES PAIRS
    SITES`, the word `own` where the training states are the field's own, four words a slice (its name, piece, cursor
    and places taken), where set the world's clause (`world SLICE EVERY RECORDS RUN`, and a fifth word where each
    draft is redrawn) and, last, the frontier's share (`frontier E` of every eight stretches, then `before` or `strand`
    where the frontier's stretches are read as known streams or by two streams, then `past` and `second` where those
    are set).

A section is the unit a deposit consumes, so its two bounds (pairs of sites and sites) are law and are carried in the
pass line. A state is never an archive of what crossed it (CLAUDE.md, retention is a quotient). Every line from the
tenth on is written only where the learner carries it, so a state without one reads and writes byte for byte as
before, and `train-store` refuses a state that does not write back as it was read. A tool that writes a state judges
every line it does not mean to change ([§7](#7-the-commands)).

## 6. Where a section's time goes

A reading of lap 17, from its own lines (3,000 sections in 2,009 s on the RTX 4080 SUPER under `.local/gpu.lock`): a section
of about 41,000 sites in about 200 regions takes about 0.66 s, of which the cut and its regions take 2 to 6 ms on the
host and the card's run with the deposit about 650 ms (`regions_ms`, `deposit_ms` on each `STORE_SECTION` line). A
read of the held passage at a lap's mean (100,508 places one open, 3,717 whole masks) takes about 262 s. `FIELD_PHASES`
and `FIELD_PROFILE` print the host's part by phase (`STORE_HOST`, `STORE_DEPOSIT_PARTS`) and the card's launches; a timing difference between builds is read
only inside one balanced hold of the card (CLAUDE.md, waiting).

## 7. The commands

`athena MODE complete-language WORD …` ([`main.rs`](../crates/athena/src/main.rs)). The mode is `train` (the card is
opened and the command runs through it), `host` (no card is opened; a command that reads runs through the host
realization on the host's threads) or `parity`. Every command pins its inputs by SHA-256, prints `FIELD_COMMAND` with
its words and one line a unit of work, and a run that opens the card prints `FIELD_CARD_OPEN`, `FIELD_CARD` and
`FIELD_SKIN`. The variables `FIELD_PROFILE`, `FIELD_PHASES`, `FIELD_TRACE` and `FIELD_BLANK_LIVE` are readings (their lines
begin with those names); the trainer, the writers and the readings refuse every other variable named `FIELD_…`. The
pass's tools and the foundings that judge their lines (`next-pass`, `join-store`, `move-store`, `own-states`,
`set-world`, `set-terrain`, `set-frontier`, `found-lane`, `found-loud`, `found-pump`, `open-level`) read the written state back and refuse a line
they did not mean to change.

**The line's commands.**

| Word | Mode | What it does | Its lines |
|---|---|---|---|
| `train-store` | `train` | trains sections over the store from a state, saving `STATE.k` and `MEAN.k` every so many sections and at the last, and `STATE.stopped` past its stop time; a learner with no pass crosses first (the codec extended by the store's fresh bytes, the pass set at the store's start, `STATE.0`) | `STORE_STATE_TEXT`, `STORE_DECLARATION`, `STORE_PASS_AT`, `STORE_SECTION` a section, `STORE_WORLD` where the pass has a world, `STORE_SAVE` a save, `STORE_STOPPED`, `STORE_PASS`; at a crossing `STORE_YARDSTICK`, `STORE_BYTES`, `STORE_LETTERS`, `STORE_CROSSING`; under a reading `STORE_HOST`, `STORE_DEPOSIT_PARTS` |
| `read-cavity` | `train`, `host` | reads the held passage at a state: one place open (`P` rows), whole masks (`W` rows), and each place at the frontier, every place before it known and the region ending there (`F` rows of `frontier.tsv`, its place the count of places known; `K` and `S` rows where the frontier is read as known streams or by two streams, on the word `known` or where the state's pass says so) | `cavity.tsv`, `frontier.tsv`, `CAVITY_LAW`, `CAVITY_SLICE`, `CAVITY_FRONTIER`, `CAVITY_KNOWN`, `CAVITY_STRAND`, `CAVITY_DONE` |
| `read-loudness` | `train` | the loudness of each region's places beside their surprise (`tools/loudness_table.py` reads it) | `LOUDNESS_LAW`, `LOUDNESS_SLICE`, `LOUDNESS_DONE` |
| `write-store` | `train` | the release from held prompts | `STORE_WRITE_LAW`, `STORE_WRITE`, `STORE_WRITE_DONE` |
| `parity-store` | `parity` | every read asked of the card and of the host, compared whole | `STORE_PARITY`, `STORE_PARITY_DONE` |
| `restore-store` | `train` | a saved state read in a fresh process and written back, its bytes compared with the file's; it writes nothing | `STORE_RESTORE` |

Gate 3 for the engine is `bash tools/gate_engine.sh LINE BIN OUT`: parity on 3 of the line's sections, 24 sections
reproduced, and the lap's read byte for byte (CLAUDE.md, the gates).

**The commands that write a state.** Each writes a new state and leaves its source as it was.

| Word | Mode | The state it writes | Its lines |
|---|---|---|---|
| `next-pass` | `train` | the state's next pass over its role: every slice set back to its first piece, the count of stretches kept | `NEXT_PASS` |
| `join-store` | `train` | the pass joined to a grown store at a new pass: the store's slices, each at its first piece | `JOIN_STORE` |
| `move-store` | `train` | the pass moved to a store whose slice was redrawn: the slice set to the first piece at or past the places the pass has taken of it, its cursor zero | `MOVE_STORE` |
| `own-states` | `train` | the pass's word `own` set: each stretch's training state is the release's own | `OWN_STATES` |
| `set-world` | `train` | the pass's world clause set: one stretch in so many of a slice is an act the world answers | `SET_WORLD` |
| `set-terrain` | `train` | the pass's terrain line set: the world's own records, `RECORDS` of one kind a region, their share of a section's sites held by the terrain's tension against the passage's (`PassTerrain`) | `SET_TERRAIN`; the trainer prints `STORE_TERRAIN` a section |
| `set-frontier` | `host` | the pass reads a share of its stretches at the frontier, in eighths, with its reading's words | `SET_FRONTIER` |
| `set-rate` | `host` | the deposit's rate set and, on request, its steps' remainders carried | `SET_RATE` |
| `set-leak` | `host` | the store's leak set ([`Learner::leak`](../crates/engine/src/learner.rs)) | `SET_LEAK` |
| `hold-families` | `host` | a learner whose deposit moves named families alone | `HOLD_FAMILIES` |
| `found-lane`, `found-loud`, `found-pump`, `found-friction` | `train` | a part founded at zero: one more lane; the loud face; the carry circles pumped (the pump's chart in the `carry` part); each head's friction of distance (its own part, `friction`) | `FOUND_LANE_LINE` and `FOUND_LANE`; `FOUND_LOUD_LINE` and `FOUND_LOUD`; `FOUND_PUMP_LINE` and `FOUND_PUMP`; `FOUND_FRICTION_LINE` and `FOUND_FRICTION` |
| `grow-crossings`, `found-crossing` | `train` | crossing triads grown with drawn legs and a zero return; the triads' legs set from a ruler's located file, the return at zero (a founding) or the ruler's (a ruler's state) | `GROW_CROSSINGS`, `FOUND_CROSSING` |
| `open-level` | `host` | the level opened to one-sided streams: the block a passage read by two streams takes the epoch before each place through, at zero | `OPEN_LEVEL` |
| `grow-carry` | `host` | more carry circles on a field that has some, founded as its first were (drawn drives and turn rows, the leak at its founding, `W` columns at zero: every face kept, a tower's level kept) | `GROW_CARRY` |
| `found-closed` | `train`, `host` | the closed face founded from a ruler's words (`crates/engine/src/closed.rs`), an attempt the card refuses | `FOUND_CLOSED` |
| `zero-triad-return`, `zero-level-return`, `ruler-temper` | `train`; `host`; `train` | a ruler's state, never trained from: the triads' return at zero; the level's prolongation at zero; one head's listener temperature moved | `ZERO_TRIAD_RETURN`, `ZERO_LEVEL_RETURN`, `RULER_TEMPER` |

The state tools routed under `train` open the card before they run, though they read no realization.

**The readings and a study's writers.** Each reads a state and writes none; a study's states train no line's lap.

| Word | Mode | What it reads or writes | Its lines |
|---|---|---|---|
| `read-open-rows` | `train` (it opens no card) | the open rows' shares over the sections a line would train next, by slice, head and tick | `OPEN_ROWS*`, `OPEN_CROWDS*`, and with its further words `CARRIED*`, `BYTICK*`, `HALVES*`, `HELD*`, `TICK_NEWS*`, `FAR_JITTER` |
| `read-prompt`, `read-writes` | `train` | a held continuation coded beside its own prompt and beside a foil; a write's code beside its reference's | `PROMPT_LAW`, `PROMPT`, `PROMPT_SLICE`, `PROMPT_DONE`; `WRITES_LAW`, `WRITES_SLICE`, `WRITES_DONE` |
| `read-forms`, `write-forms`, `write-acts` | `train`, `host` | a forms table's runs coded after their prompts; the writer after each prompt (`forms.written`); the trainer's acts off the line, each draft with the world's reaction | `FORMS_LAW`, `FORMS_ROW`, `FORMS_DONE`; `FORMS_WRITE_LAW`, `FORMS_WRITE_DONE`; `ACT`, `ACTS_DONE` |
| `read-tension`, `read-tension-store` | `host` | the covector at the strand's return beside the pair chart, the gathered current and the triads' products, by tick: at the places a forms table names (with `all`, every site, the tick's opening chart and the open row's sources, shares and locks at unit gain), or over the sections a lap meets next (`tools/tension_ruler.py` reads them) | `TENSION_LAW`, `TENSION_TEMPER`, `TENSION_BLOCK`, `TENSION_SECTION`, `TENSION_DONE` |
| `try-passes` | `train`, `host` | passes over a small forms table by the learner's own section step, each run a keyed half open, with reads of a second table every few passes, saves, and a stream word under which no row is met twice (`ruler/tension.rs`) | `TRIAL_PASSES`, `TRIAL_PASS`, `TRIAL_READ`, `TRIAL_DONE` |
| `write-next` | `train`, `host` | a ruler's writer of one place a read, each place the last of its region, for a field compared on the next place alone | `NEXT_WRITE_DONE` |
| `read-level` | `host` | a region's level written out for a ruler (its epochs' anchors, each place's news, each epoch's state; with `links`, every link of the level's equation and the covector at its locus, for `tools/level_links_ruler.py`) | `LEVEL_DONE` |
| `read-junction` | `host` | where an answer digit's contact weight goes among the operands' digits, by tick and head | `JUNCTION_LAW`, `JUNCTION_HEAD`, `JUNCTION_DONE` |
| `read-far`, `read-chart`, `read-strand-states` | `host` | what a place at the frontier takes from the far field, by what it hears there; a passage read at its boundary, every place at once; what a strand's sites hold, written out for a ruler (with `rows`, each open place's row by tick, head and source) | `FAR`; `CHART`, `CHART_LAST`, `CHART_DONE`; `STRAND_STATES`, `STRAND_ROWS` |
| `read-reach` | `host` | the code of every place of a passage by two streams under a ruler's friction of distance, a setting at a time (`Constitution::ruler_friction`) | `REACH`, `REACH_DONE` |
| `read-pace`, `read-triads` | `train` | the turned heads' located rates by symbol; the triads' material by triad | `PACE_RINGS`, `PACE_HEAD`, `PACE`; `TRIADS`, `TRIAD` |

Three modes take no command word: `athena yardstick` times the card's products, stores and gathers (`YARDSTICK`),
`athena reserve KEY=VALUE…` prints the octets a declaration reserves a pair, a site and a region (`RESERVE`), and
`athena attributes` prints the card's census (`CARD_ATTRIBUTE`).

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
| 7. No Lean, no file system or process in the pipeline | holds on the engine as a lint | gate 1's guard lints on `holonics-engine` and `athena` (`disallowed_types`, `disallowed_methods`, the lists in `clippy.toml`); `athena` is the exterior and allows them by name; gate 1 does not lint the card crate |
| 8. No templates | practice rule | CLAUDE.md, no catered machinery |
| 9. The codec is not the architecture | practice rule, with its repair owed | CLAUDE.md, a symbol is a word and one law reads every stream; the engine's codec is the codec's sheet until the symbol's line replaces it (`codec.rs`'s first lines) |
| 10. No scalar operand | retires with its object (`Word::pull_back`) | CLAUDE.md, loss is the logarithm of a ratio of Holons |
| 11. Learning is locating keys and depositing covectors | practice rule | CLAUDE.md, keys and navigation; learning uses the covector of a declared comparison |
| 12. No floats | holds on the engine as a lint | gate 1's guard lints on `holonics-engine` and `athena` (`float_arithmetic`, `f32`/`f64` disallowed); a reading printed at the exterior allows it where it writes; the card crate denies `float_arithmetic` in `hnn/mod.rs` and is not linted by gate 1, its yardsticks owing theirs |
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
  a passage at its own frontier in one forward stands on the host and, since November 18, on the card:
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
  - built on the card (November 18): the known stream, then the second stream.
    - The known stream is a batch's word (`FieldWords::before`): a support entry and a crowd on the after side meet no site, a still
      head shares a class's face among its members before the receiver, the opening and the moments read no after row, an odd strand
      contact has no mate, a circle scanned from the right stays at rest, and a region's first site is a row not computed; the level
      is unheard and the field reads once. It is the host's forward under a ruler at `3` and, as a region's own word
      (`Region::before`, atlas `tower.region-known-stream`), a law of the region: a section's known streams run as a second group on
      the card, each one's return standing for both reads where the field reads twice, and the faces and the training path's words
      stand in the regions' order. The opening is compared there as the retarded one. Card against host, bit for bit, on four fields
      read once and twice (`the_known_stream_on_the_card_reads_the_hosts_bits`, 24 cases).
    - The second stream (`Region::strand`, atlas `tower.region-strand`): a passage is staged as its known stream's sites and then as
      many open places (`site_place`, `region_heard`), each open place at the place of the known site of its index. A site's near
      field, falloff, plain frame, strand mate and circle are read by its place; an open place hears the known sites before its place
      and is heard by no one; its opening is the retarded cavity opening and its moment the known stream's retarded cavity moment of
      its place, so the cavity's forward and return (cut out of the opening's comparison) serve it whole; its clock is the clock of
      the known site before it and one bare stride at every tick, never read again from its own face (worth 0.004 to 0.013 nats at
      the frontier on the ruler's 800 rows, which is what the simpler form costs). Its moments' covectors are summed over the ticks
      and returned once, its clock's covector goes to the site before it, a known site's drive takes both of its mates' terms, and a
      circle's covector takes the open place's term beside the known site's. Card against host (`Constitution::strand_pass`,
      `strand_returned`), bit for bit, on four fields read once and twice, passages of 2 to 300 places alone and in sections beside
      regions of the law and known streams (`a_passage_read_by_two_streams_on_the_card_reads_the_hosts_bits`, 16 cases, first run).
    - The pass carries either for the frontier's stretches (`frontier E before`, `frontier E strand`; `StorePass::before`,
      `StorePass::strand`, set by `set-frontier`); a stretch read by two streams counts its card sites in the section's bounds. The held
      read writes the frontier's rows read each way (`K` and `S` rows, where the pass says so or on the word `known`), and the
      one-place writer writes a state in the regime its pass names (by two streams: the known places and one more site, the face read
      at the open place of that last place).
    - The strand's odd contacts facing the past (`Region::past`, atlas `tower.region-past`; the batch's word `FieldWords::before = 2`;
      the pass's words `frontier E strand past` and `frontier E before past`): in a one-sided region an odd plain contact's mate is the
      known site two before the place and a circle of odd contact is scanned from the left, where unset the one has no mate and the
      other rests. Why: on the two-stream line's state the plain contacts carry 0.99 nats to the frontier and the circles 0.46
      (`read-far` at `8` and `7`), and half of each stood idle. Card against host on the same four fields, first run: the strands'
      test with a section of strands facing the past (24 cases) and the known stream at `9`. Whether the line carries the word is
      G-1118-15's read.
    - The row of the site after reading the second site before (`Region::second`, atlas `tower.region-second`; the record of the two
      streams §15; the second bit of the batch's word; the pass's `frontier E strand past second`): in a one-sided region a site's
      opening, and the open place's at each place, take the row `E₊` of the second place before, where `E₊` read no site there. Why:
      an open place holds the place before it at nine tenths as it opens (the row `E₋`), the second at a half and the third at a
      fifth, no tick carries a farther place in, and the frontier binds about three places. Host: 220 probes of the covector match
      the code's difference and a place's face is the same bits in the passage cut after it. Card against host, bit for bit, on its
      first run: the strands' test with a section mixed with the second row (40 cases). Whether the line carries the word is
      G-1118-17's read.
    - The level as a strand hears it (atlas `tower.level-before`; the record of the two streams §10 and §11): on a tower whose glue
      carries the block `B⁻`, `b_B⁻` (`Constitution::level_before`, `athena host complete-language open-level`; founded at zero, carried
      in the learner's state), a passage read by two streams cuts its known stream where a one-sided stream can name a site (no
      earlier place within a section of news carries news as large), restricts each epoch over its known sites through the law's
      `A`, runs the level's field with each epoch hearing only the epochs before it, and hands every known site, and the open place
      at every place, the epoch before its own through the block (`scale_forward_before`, `scale_return_before`, `strand_level_cut`).
      On the card the host cuts the batch from the news the card reads at the known sites (`field_level_news_strand`), an epoch's
      known sites are one run and the sites that read an epoch two (`field_level_chart32_spans`, `field_level_chart64_spans`), a
      site that reads no epoch takes nothing (`LEVEL_NONE`), and the level's words carry the known stream's word. Card against host,
      bit for bit: the strands' test on a fifth field, the tower with the block drawn (30 cases), and sixteen small cases forward
      and returned (`the_level_a_strand_hears_on_the_card_step_by_step`). It is the carrier a level's own receipt needs; by the
      level's rows in the atlas it is not expected to move the frontier without one.
  - owed, in order: the composite's remainder at the place level (the record of the two streams §12 to §14: the frontier's excess
    stands inside units, 0.4 nats of all places, and about twelve thousand rows a register close most of it); the level's own
    receipt; a writer that keeps the known stream's states and reads one new place a symbol; the second read's mark is left out for
    good unless a reading asks for it.
  - why it was built: the frontier's fall under the control is 0.1603 + 0.0458 ln(sections / 3,000) over six laps with the share, a
    fifth lane of 32 buys nothing there in its first lap (one lap, which is no null on the lane), and a frontier comparison cost a region's whole read (the frontier record
    §5 and §7).

- **A founding law, and a lock that closes** (November 16, [the record](../research/records/2026-11-16_THE_LINK_THAT_SLIPS_IS_THE_LOCK_A_FAR_DIGIT_ARRIVES_AT_A_TENTH_OF_ITSELF_THE_SUMS_LAW_SITS_IN_A_PRODUCT_NO_READING_REACHES_UNTIL_THE_LOCK_CLOSES_AND_A_PART_ENTERS_BY_A_TENSION_READ_ALONG_ITS_CONSUMERS_EQUATION.md)). Every part
  of the engine enters at zero or with drawn operands; the founding law of October 24 (`contact.pool-founding`) stands in a host ruler
  (`tools/tension_ruler.py`) and in `found-crossing`, unused. A lock's temperature is one entry a head and receiver kind (`Loci::temper`),
  the open row's weights are formed afresh at every tick, and the readings of that day place the line's missing step there.

- **The cut's second part** (C5): the kernels' headers (one header a phase). The October items stand in their objects' modules. The renames stand (`Constitution`, `Declaration`, `Loci`, `Learner`, `Realization`, `Host`, `Resident`,
  `Codec`, `Forward`, `ReadLogits`, `Next`, `Receipt`, `OwnedRegion`); the module paths `field` and `hnn::field` stay.
- **The headers** (C7): every module and kernel header in the form of
  [THE_CONSOLIDATION §5](plans/THE_CONSOLIDATION.md#5-the-engines-cut-by-object) (object, equations, kind and index, kernels, Lean,
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
| A series is released at a tolerance: a store settles to its receiver's grain under the flux that passes through it, and its return reads the settled state | the lens of November 20; the held step of October 27 (atlas `hnn.held-step-covectors`, Lean `HNN/HeldStep`); the stores-and-caches law (atlas `store.finite-quality`); [the record of November 20](../research/records/2026-11-20_A_LANE_IS_A_REGISTER_OF_THE_FACE_AND_NEVER_A_THREAD_THE_CARDS_REGISTER_FILE_IS_THE_PRECISION_LAW_AS_CAPACITY_HEAT_FOLLOWS_EVERY_MERGE_AND_ORDER_ONLY_A_SECTION_AND_A_SERIES_RELEASES_ONLY_WHERE_ITS_TICK_CONTRACTS.md) §8, atlas `tower.field-tick-contraction` | **November 20:** the count of ticks is a declared 4 (`Declaration::ticks`); each tick adds and every reader divides by the face lanes' powers, so a site's state fills as a running mean and nothing in it is damped (atlas `tower.field-tick-running-mean`; the held tick was withdrawn on November 15 for that reason). The return composes the transposed ticks from kept shares, 280 octets a pair of sites (`read_octets`), which is why a section is three batches. The record named two host readings; both are read. **November 21:** the trained tick does not contract: on L71's end state the chart settles only as a running mean (the residual by tick), and a site's own block of the tick, read by finite differences at ticks 4, 8 and 16, has steady exponents on the lanes' fill, about 82 of 224 modes released as a power, about 70 held and about 72 boosted as a power ([the record](../research/records/2026-11-21_THE_BUILT_TICKS_RATES_STAND_STILL_ON_ITS_FILL_CLOCK_A_THIRD_OF_A_SITES_MODES_IS_RELEASED_A_THIRD_HELD_AND_A_THIRD_BOOSTED_AND_THE_CONTACT_KERNELS_WAIT_ON_THEIR_LOADS.md), atlas `tower.field-tick-rates-on-the-fill-clock`). So no tolerance releases the tape at this form; the boosted third is what a leak must contract, which a uniform leak cannot and a news write does where its reading sees it |
| A width is the machine's: a register of the face is founded by the tension at its locus, sized from its need, read by the blocks that declare it, and released by partition when its price reads empty | the precision law; atlas `radix.register-composition`, `tower.face-lane-composition` and `contact.pool-founding`; [THE_CONSOLIDATION §10](plans/THE_CONSOLIDATION.md#10-declared-extents-that-stand-in-for-laws); the record of November 20, §9 | **November 20:** the line's face is 7 lanes of 32, each founded by hand (`found-lane`) and kept where its level fell under a control's; every block reads every lane, the same at every place, and no lane is released. A face lane holds no radix (nothing carries from one lane to the next; the carry circles hold the engine's only carried digits). The piece not in hand is the ruler that sizes a register (G114 sized none) |
| Reach is a contact's strength times a friction matched to the distance, and the exponent of a head's prior is its own | atlas `wave.matched-friction-reach`, `contact.octave-falloff-navigable`, `tower.field-reach-on-clock` (November 13, designed); the stores law (no store is at rest) | **November 21:** the built falloff fixed the exponent at one bit an octave for a turned head and at none for a still one, so at a copy's answer digit head 0 put 0.65 of its row on the operand digit and 0.28 on the same digit of the earlier records, and a ruler's friction of one bit an octave there took the copy digits from 0.54 to 0.06 nats at 0.015 nats a place of text. Each head's friction of distance (`Declaration::friction`, two a head) is founded at zero and located by its own covector ([the record](../research/records/2026-11-21_A_STILL_HEAD_WEIGHS_NO_DISTANCE_SO_A_COPY_READS_THE_RECORD_ABOVE_AND_EACH_HEADS_FRICTION_OF_DISTANCE_IS_ITS_OWN_REACH_FOUNDED_AT_ZERO.md), atlas `contact.friction-of-distance`); the arm W80r reads where it goes |
