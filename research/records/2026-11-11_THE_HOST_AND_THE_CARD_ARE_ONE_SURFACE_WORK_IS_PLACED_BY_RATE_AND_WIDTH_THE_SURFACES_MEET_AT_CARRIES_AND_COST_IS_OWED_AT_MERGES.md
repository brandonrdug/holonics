# The host and the card are one surface: work is placed by rate and width, the surfaces meet at carries, and cost is owed at merges

Status (2026-11-11, 04:25 UTC): a lens derived and joined to its owners, with two host rulers read, design's sampled profile and its per-entry profile of a training lap scored, with the guesses G37, G38 and G40 scored and G39, G42 and G44 fixed and unread. The per-entry profile corrects the sampled one's first reading (§7): kernels hold 0.743 of a lap and not 0.94. It rules on the scope of the card rule (GPU first) and amends the guides. No learner part is ordered from it. Two realizations on the card are (§7), each keeping every bit: the share store addressed by its support, and a paced skin's exponent read from two site addresses. Claude (theory lead). Refs #76, #404, #407, #410.

Read beside [the traffic record](2026-10-31_THE_HARDWARE_IS_A_TRAFFIC_NETWORK_WORK_RIDES_THE_LANE_ITS_SHAPE_FITS_AND_EACH_CROSSING_IS_PRICED.md) (a lane carries a segment of a run and never owns a part of the law), [GPU first](2026-10-27_THE_LEARNER_RUNS_ON_THE_CARD_AND_ITS_WORKLOAD_IS_NEVER_TRADED_FOR_TIME.md), [precision is a count](2026-11-07_PRECISION_IS_A_COUNT_A_MACHINE_NUMBER_IS_A_GRAPH_AT_COUNTED_WIDTHS_AND_THE_CARD_IS_A_SURFACE_OF_THREAD_POTENTIALS.md), [systolic flow](2026-09-29_SYSTOLIC_FLOW_THE_WORD_IS_A_SYSTOLIC_PULSE_AND_A_TABLE_IS_A_NAVIGATORS_RESIDENT_FACE.md), [the news clock](2026-10-27_THE_LEVELS_TICK_ON_THEIR_OWN_NEWS_SO_THE_TOWER_LEARNS_ITS_ENCODING_ON_ITS_OWN_AXIS.md) and section 8 of [the grip record](2026-11-10_A_GRIP_OF_LETTERS_IS_A_NAVIGATOR_WORD_THE_FIXED_ADVANCE_MOMENT_READS_ONLY_PAIR_TERMS_AND_THE_CONTACTS_PRODUCT_MUST_CARRY_ALONG_ITS_OWN_CIRCLE.md) (a longer word is a founded unit at a coarser grain).

## 1. The lens

[historical] Brandon, November 11, 01:19 UTC (paraphrased; his words stay outside the repository). Design had read the machine during a re-draw stage: the host process at 12% of one core on four threads with half a gigabyte, the host's load at 2.7 of 24 threads, and the card 44% busy at 228 W (one sample at the stage's start, as §7 found). He accepts that the learner runs on the card and asks why the processor and its memory are not still another surface that some of the dynamics move onto by themselves. The system has varying timing costs, and he is sure the processor would integrate properly. He points theory at Landauer's principle and free energy, joins it to expansion and contraction, and asks for a way inside the computational mathematics for the timings of events to synchronize and resonate (cadence, rhythm) without the routes between devices being tuned by hand, the interface aside.

It continues his lens of October 31 (the hardware as a traffic network) and his authorization of November 7 (the whole host may be used, within the theory and never by brute force). What is new is three things: the route should settle by itself, its rhythm should come from the mathematics, and its price should be thermodynamic.

## 2. Recovered

| Part | Held as | Where |
|---|---|---|
| Co-present regions execute together when their effects commute | the hardware law; `holarchy.launch-cover` (per-thread exclusive regions commute; `scatterAdd` is order-free) | CLAUDE.md; `Foundation/DeviceLaunchLaw` |
| Integer series give the same bits on any partition | the precision law (parallel determinism) | CLAUDE.md |
| A workload has width, depth and branching; a lane fits one shape; a crossing is priced as a flux with its volume and its wait | the traffic record, §2 | October 31 |
| No lane owns a part of the law; the route may change as the dynamics change | the traffic record, §5 | October 31 |
| Host and card as one surface for one read, the share settling by itself | `hnn.field-lanes`: `k/n = t_c/(t_h + t_c)`, met halfway from the last share; over 39 sections every line the card's, the share at 2.3%, the time at 0.998 | `holonics::hnn::tower::field::LanesField`, November 7 |
| A level that ticks when its own news crosses a section | `hnn.tower-news-clock`: `Δτ_l(t) = ⌊S_t/σ_l⌋ − ⌊S_(t−1)/σ_l⌋`, and `Δτ = 0` moves nothing; `hnn.tower-news-clock-carry` | October 27 |
| A carry is the flux of a section | `radix.carry-section-flux`, `hnn.carry-is-section-flux` (formal-checked) | `Mathematics/ArithmeticContract`, `HNN/Moment` |
| A rhythm is one rate's section crossings read on another's circle | `radix.carry-rhythm`: `c_s(k) = ⌊(k+1)s/b⌋ − ⌊ks/b⌋`, the balanced word | November 10 |
| A rational pair lock is the zero-power line | `lock.pair-lock-zero-power`: `power(q, p) = 0 ⇔ q v_a = p v_b` (formal-checked); `lock.simplest-between` | `Transport/HelicalPairInteraction` |
| Rates 1 and √2 admit no joint clock | `holarchy.incommensurate-pumps` | `Holarchy/Join` |
| Erasure is a merge, priced by Landauer on the merged fibre; the shear is the reversible primitive | `standing.erasure-is-merge`, `floor.landauer-erasure`, `arith.shear-merge-cost` | October 9, October 28, November 8 |
| Free energy over the equilibrium is the divergence in thermal units | `xent.free-energy-kl`, `heat.free-energy-grain` (formal-checked) | `Physics/InformationDifference` |
| The word is a systolic pulse; a limb-wise multiply-accumulate is followed by the carry cascade | the systolic record, §1 | September 29 |
| The card's own clock around every launch; the host's wall time between marks; kernels, copies and allocations apart | `CardField::stamp`, `trace_phases`, `profile` | `holonics_cuda::hnn::field` |

So the route's pricing, a self-settling share, an event clock counted in news, the carry as a flux and the lock as zero power were all held. Nothing joined them into one statement of a two-surface run, and the card rule's text read as a wall against the host.

## 3. The chart

| His word | The object and the operation | What the discipline proves, restated |
|---|---|---|
| another surface | two Holons joined at a port; the port's flux is the crossing's volume | associativity of integer addition: co-present terms summed on any partition give the same bits |
| varying timing costs | each surface is (lanes, time a term, latency an event, word width, memory) | work `W` of depth `D` on `p` lanes takes between `max(W/p, D)` and `W/p + D` (Brent; Graham) |
| offload by themselves | the route is a slow variable relaxed by the measured slip | the lanes split's share, met halfway from the last one, is this relaxation for one read |
| synchronize, resonate | a pair contact between two clocks; slip is the time one side waits | a lock is the zero-power line `q v_a = p v_b`; work moves across the port until the slip is zero |
| cadence, rhythm | a carry: the flux of a section of the machine's own clock | the slow events among the fast ones form the balanced word of the two rates |
| the interface | the port: which crossing a job reads and which it joins | deterministic processes that block on their inputs compute the same histories at any relative speed (Kahn) |
| Landauer | a merge of distinguishable states into one | heat is owed for the merged fibre and for nothing else; a shear merges nothing |
| free energy | the code in nats, in units of `k_B T` | a closed grain with nonnegative dissipation cannot raise it |
| expansion and contraction | fan-out of one constitution over co-present places; merge of the terms into a sum, a carry and a release | two strokes in series take `e + c`; in antiphase on two surfaces they take `max(e, c)`, a gain of at most two, reached at `e = c` |

## 4. The law of a two-surface run

**4.1 Placement is a realization.** A term computed on the host or on the card is the same bits, so where it runs is never part of the law. Its parity is put on record once for each kind of event, and the placement may then move during a run. Reason: integer series are associative. Scope: terms whose inputs are named by the machine's own clock (4.3).

**4.2 The same work on both surfaces gains nothing.** This is measured (`hnn.field-lanes`): the share settled at 2.3% and the time at 0.998. A host lane is the card's kind of lane, slower. The split that pays is by kind of work.

**4.3 A join is at a named crossing.** A host job reads the state at a named crossing of the machine's own clock (a section, a lap, a carry) and its result joins at a named later one. The side that arrives first blocks, and the wait is printed. A join on wall time is barred: the bits would follow the schedule, and two runs of one law would differ. With the crossings named, the result is the same at any relative speed of the two surfaces. This is Kahn's determinacy read on the objects: each side is a receiver whose reception is a function of the flux histories through its ports. What stays behind is his unbounded channel; here a channel holds one crossing's state and the block is the bound.

A reading is the free case: it joins nowhere. A held or locked visit, a structure measure or a ruler run from a saved state leaves the state's bytes the same and never blocks a lap.

A slow variable carried on the host (a part's rate, a coarse grain's state, a growth decision) reads at one crossing and joins at a later one. That delay changes the bits, so it is law: it is declared and carried in the learner's state.

**4.4 Rate times width places a kind of event.** For a kind of event with `n` co-present terms:

```
time on the card = t_L + n t_c        time on the host = t_x + n t_h
n* = (t_L − t_x) / (t_h − t_c)        the card carries it ⇔ n > n*
```

`t_L` is an empty launch's latency, `t_c` and `t_h` are one term's time on the card at full lanes and on a host lane, and `t_x` is the price of the crossings the move adds (the traffic record's price). All four are measured, so `n*` is never a dial. The kinds are ordered by `n`. The host takes them from the narrow end until neither side waits, and the threshold moves by which side waited. [agent-inferred] `n*` is some tens of thousands of terms for one host lane on this machine: the least launch in an older profiled read of the field is 22 µs between two synchronizations, and a host lane's term is taken as a nanosecond. The built profile gives `t_L` as its least time a launch.

[measured November 11, §7] The per-entry profile reads the least launch at 23 µs and the mean transfer at 94 µs in training (2.5 ms in a re-draw read). For a kind in the middle of a chain of launches the move adds two transfers, so `t_x > t_L`, `n*` is negative and the card carries the kind at every count. On this machine the law places no kind of the present chain on the host. The host's lawful work is where the terms already stand on the host, or where no lap waits.

Width decides beside rate. The card's lanes are narrow and many, and the host's are wide with a native carry. The field's contact rows are summed whole on the card in 5 to 20 limbs of 64 bits a lane and divided once a row (`tower.field-card-realization`), which is a wide word on a narrow lane. A sum kept as limbs with its carries unresolved adds in one step on any number of lanes; resolving the carries is a short serial chain. So the digit partition is the device partition: the low digits in bulk on the card, the carries and the wide tails on the host. It applies inside the card first: limbs across lanes with their carries deferred, the carry and the division once a row (§7, G40).

**4.5 The surfaces meet at carries.** A carry is the flux of a section (`radix.carry-section-flux`). Between two carries the fast register owes the slow one nothing, so the two sides run free. A slow register acts when one whole unit has arrived, which is the news clock's law. Acting more often merges nothing, and acting less often overflows. The rate of slow events is the flux through the section over its modulus, so it is set by the passage and the register's width and by no schedule. Among the fast events the slow ones fall as the balanced word (`radix.carry-rhythm`).

The grains of the train passage, counted on the host:

| Grain | Events a lap | Events a second at 1,104 s a lap |
|---|---|---|
| letters (places) | 8,096,768 | 7,334 |
| units (runs of word letters; 4.82 letters each) | 1,125,322 | 1,019 |
| lines | 277,282 | 251 |
| passages | 24,685 | 22 |

Each coarser grain has fewer events and, by the unit lens, a wider state (a composed move). So each falls under `n*` sooner than the one below it, and the upper grains of a tower are the host's kind by 4.4, with no rule that says so. [agent-inferred, unmeasured] This is the form in which the dynamics move onto the host by themselves: a tower whose grains are its own carries spreads over the two surfaces by its event counts.

**4.6 Slip is waiting, and the lock is zero slip.** The two surfaces are a pair contact. With `v_a` and `v_b` their rates in crossings a second, the contact's slip is the time one side waits for the other, and its dissipation is that waiting. The lock is `q v_a = p v_b` (`lock.pair-lock-zero-power`). The rates are not fixed: moving a kind of event across the port changes both, so the route relaxes toward the lock, as the lanes split's share did. Nothing is authored but the port.

## 5. The accounting

Landauer prices a merge and nothing else (`floor.landauer-erasure`, with its hypotheses). A lap of the base attempt meets 8,096,768 places of 100 classes, at most 53.8 million bits, and deposits into 63,606 numbers of 32 bits, 2.04 million bits. So a lap merges some tens of millions of bits, and that count is fixed by the workload.

[reading; design's samples of the seventh training lap of the part-rate line, every 5 s] At a mean draw of 186 W over 1,069.8 s the card spends 199 kJ, about 3.7 mJ for each bit of passage, which is 1.3 × 10^18 times `k_B T ln 2` at 300 K. The floor in joules binds nothing here. What the principle gives the machine is its count: a step that merges nothing owes nothing. Idle lanes, a side that waits, a transfer that is discarded, a value recomputed unchanged, and arithmetic at a place that carries no news are heat with no merge behind it.

The free energy of the faces over the passage is the code in nats in units of `k_B T` (`xent.free-energy-kl`). A lap's yield is the nats it removes from the held code, and its efficiency is nats removed a joule. That reading is owed in the lap receipts beside the time. Its first value: the sampled lap moved the held joint code from 1.7524 to 1.7506 nats a place, 0.0019 nats a held place for 199 kJ. The three laps before it removed 0.0105, 0.0078 and 0.0020.

Expansion and contraction are the two strokes of each tick. The fan-out is one constitution meeting many co-present places: many narrow products, the card's stroke. The merge takes the terms into a sum, a carry and a release: few wide words, the host's stroke where they fall under `n*`. Run in series the strokes cost their sum; in antiphase on two surfaces they cost the longer one. Matched strokes are the resonance, and 4.4's threshold is where they match.

## 6. Two host rulers

Rulers on the host, never machinery. Scripts and logs are in the receipts.

**The grains** (`cap_t.py grains`, the train passage): the table of 4.5. Separators are 0.3301 of places (0.2052 the space class, 0.1249 punctuation and the rest), unit starts 0.1390, newlines 0.0342.

**Where the news lies** (`cap_t.py news`, design's locked visits of the held problems, 43,470 places, numbers only). The covector mass of a place is `m_t = |p_t − q_t|²`, with `p_t` the locked face and `q_t` the reference letter's indicator.

| Reading | rt4 (the part-rate line, lap 4) | ct8 (the plain-rate line) |
|---|---|---|
| mean locked code, nats a place | 0.5289 | 0.5516 |
| share of places holding half of the mass | 0.070 | 0.072 |
| share holding nine tenths | 0.170 | 0.175 |
| share holding 0.99 | 0.271 | 0.279 |
| places with mass under 2^-6, and their share of the mass | 0.6845, 0.0038 | 0.6748, 0.0037 |
| places with mass under 2^-10 | 0.5462 | 0.5343 |
| places with the face at 0.95 or more on the reference letter | 0.6123 | 0.6015 |
| mean mass at unit starts over inside units | 1.427 | 1.393 |

On the locked faces the news is concentrated: seven places in a hundred hold half of it, and two thirds of the places hold four thousandths of it between them. The lap's arithmetic is the same at every place and tick. So on this face the cost does not follow the news, by about six to one at nine tenths of the mass.

What this does not show. A quiet place is still a conductor: its state is read by its neighbours and carries their covectors back. And the deposit is a sum of covectors, not of their masses: many small pushes in one direction can outweigh a few large ones in scattered directions. Whether the cost may follow the news is decided by that coherence (G39), which is unread.

## 7. Guesses and scores

| | Guess, fixed before the read | Read | Score |
|---|---|---|---|
| G37a | separators 0.33 of places; unit starts 0.15; newlines 0.035 | 0.3301; 0.1390; 0.0342 | held |
| G37b | half of the covector mass in 0.14 of held places (0.10 to 0.18) | 0.070 | missed: twice as concentrated |
| G37c | 0.42 of places with mass under 2^-6 (0.34 to 0.50) | 0.6845 | missed: more places are quiet |
| G37d | mean mass at unit starts over inside units 1.5 (1.3 to 1.7) | 1.427 | held |
| G38a | a training lap: the card's time share 0.90 or more; the host process 0.25 of a core or less | 0.94 mean, 0.95 median, 0.26 least; 0.15 of a core | held |
| G38b | the card's kernel time over the section wall 0.80 (0.70 to 0.90) | 0.743 by the per-entry profile (kernel time over elapsed, 301 training sections); the proxy had read 0.94 | held; the proxy over-reads |
| G38c | the re-draw stage 0.50 or less | 0.89 mean, 0.99 median over its last 82 s on the proxy; 0.783 by the per-entry profile | missed: the 0.44 was one sample at the stage's start |
| G40a | profiled training: kernels 0.85 or more of elapsed; allocations 0.03 or less | 0.743; 0.093 | missed, both |
| G40b | entries under 200 µs a launch hold 0.10 of kernel time (0.05 to 0.16) | 0.228 | missed high |
| G40c | the contact family 0.60 of kernel time (0.50 to 0.75); the affine maps 0.08 or less | 0.487 (0.484 by the receipt script's family); 0.030 | contact missed by 0.013; affine held |
| G40d | the five heaviest entries hold 0.55 or more, each contact or moment | 0.504; each a contact, moment or pace entry | share missed; kinds held |

**What the first profile decides** (design's samples of the card and the host process every 5 s through the seventh training lap: 209 samples, 1,069.8 s, the host process at 838 MB). A kernel was resident in 0.94 of the samples and the card drew a mean of 186 W of its 320 W limit. The stage that occasioned the lens was not idle. Card memory peaked at 12.3 GB, above the 12 GB the line holds itself to.

[corrected 04:00 UTC] Two readings taken from those samples at 01:55 are withdrawn: that the gaps between launches are 0.06 of the wall, so that the host could add at most 0.06, and that the lever is inside the launches. The sampler counts a transfer and an allocation as a resident kernel. The per-entry profile below reads kernels at 0.743 of the lap, and the rest is what happens between launches.

Read from the source and from two older profiled reads in design's run directory (not copied; another declaration on November 5, this passage's release read on November 6), before fixing G40:

- The profile instrument is built (`FieldProfile`, `FIELD_PROFILE` on the pass binary): launches and time by entry, with the copies and allocations split. No stamp is needed for the per-entry read.
- Sections are cut from problems sorted by length, so the regions of a launch are mostly of like length (a lap's path problems are drawn across the sections).
- Launches under 200 µs each held 0.027 of kernel time in training on November 5 and 0.160 in the release read of November 6, where they were three quarters of the launches. The contact family held 0.385 and 0.637, and the affine maps 0.357 and 0.022.
- A contact row is summed whole in 5 to 20 limbs of 64 bits a lane and divided once by its mass.

**What the per-entry profile decides** (design, `FIELD_PROFILE` on the built pass binary from the ninth lap's state, each read alone under the card lock: 301 training sections in 212.3 s, stopped by a declared bound of 200,000 ms, and a re-draw read of 32 held problems in 93.4 s; the profile lines are in the receipts and `profile_budget.py` computes every number below). Profiled, a training section takes 0.670 s of lap time against 0.683 s unprofiled (the seventh lap), though a profiled run waits for the card at every launch and an unprofiled one does not. Running ahead of the card gains the lap nothing as built, so the profile's shares are the lap's.

| Share of elapsed | Training | Re-draw |
|---|---|---|
| kernels at 200 µs a launch or more | 0.573 | 0.780 |
| kernels under 200 µs a launch | 0.170 | 0.003 |
| allocations | 0.093 | 0.119 |
| transfers | 0.022 | 0.062 |
| the host between them | 0.143 | 0.037 |

- **Kernels hold three quarters of a training lap, and long kernels 0.57.** The other 0.43 is short launches, allocations, transfers and the host between them. A training batch runs 438 launches, 270 allocations (55.6 µs each) and 37 transfers (93.5 µs each); 456,275 of the 575,104 launches are short, at a mean of 79 µs against a least of 23 µs.
- **A section's return is cut into four batches.** The run made 1,253 returning batches for 306 returns (the reverse entries' 5,012 launches at four ticks a batch), 4.1 a return, with the peak store at the batch cap (8.40 GB, four fifths of the budget). The re-draw read is cut the same way: 141 batches for 29 reads.
- **The cause is the share store's address, read in the driver.** A region of `S` sites reserves its square: 280 octets a pair of sites when returning (a score and a share a head and kept tick, 4 × 4 × 16 octets, and the contact's return for one head, 24), at the dense address `[i][j]`, so that a column's return finds `p_ij` without an index. The driver's note of November 1 gives the reason: the reservation is the most a region's classes can ask. The regions have changed since. An opening region is the question and 2,062 places of open room, about 2,300 sites, and its rows hear the question's definite sites and their near field. The contact met 17.70 × 10⁹ pairs over 306 returns and 46 reads, between 50 and 58 million a run over its 16 head-ticks, so 3.1 to 3.6 million a head-tick, where a section reserves about 90 million pairs a head-tick ([agent-inferred] from the batches and the peak store: about 25 GB a section). The reservation is 25 to 29 times the pairs met, and it is why the card stood at 12.3 GB.
- **The host and the card take strict turns.** The unprofiled lap is no shorter than the profiled one, so the host's 0.257 (its own work, the allocations and the transfers) and the card's 0.743 add. By §5's two strokes a pair of strokes in series costs `e + c` and in antiphase `max(e, c)`, so running the host's part while the card computes is worth at most `1/0.743 = 1.35` times, and less once the step below removes part of the host's stroke.
- **The host's stroke is the batch's setup** (design's phase trace, `FIELD_PHASES` on 311 sections of the same state, unprofiled, 213.0 s; 316 returns in 1,351 batches, 4.28 a return). Setting a batch up (its tables staged, its buffers taken and its uploads) holds 0.180 of the lap at 28.3 ms a batch, with the card idle. The reverse holds 0.571 at 90.0 ms a batch, the four ticks' launches 0.100, the wait at each tick for the four words by which the host chooses the row's limb count 0.104, the host outside the card's runs 0.019 and the batch's release 0.016. A batch's tables are formed from the problems and the lap's keyed draws and read nothing of the learner, so the next section's can be staged while the card runs the present one: the host's stroke under the card's, joined at the section's crossing. That is the second step, after the one below has made a section one batch.
- **The time a pair is not shown to fall with fuller launches.** The forward contact (the exposure and the limb rows) takes 1.30 ns a pair met in training and 1.77 ns in the re-draw read, whose launches are sixteen times longer. Which lanes a launch fills is still unread (the mean grid by entry needs a small build).

**The step ordered from it: the reservation follows the support** (theory, 03:42 UTC; a realization, every bit kept; atlas `tower.field-support-stride`). A receiver's support is its near field (`NEAR_SLOTS = 10` entries) and, for an open receiver, the region's definite sites, or, for a definite receiver, the definite runs of its probed classes, which are disjoint subsets of the definite sites. So with `ndef_r` the definite sites of region `r`,

```
|S_i^h| ≤ K_r = NEAR_SLOTS + ndef_r        for every row i of r, every head and every tick
entry k of row i at   eoff_r + i K_r + k    in place of   eoff_r + i S_r + j
reservation  Σ_r S_r K_r   in place of   Σ_r S_r²
```

The forward and the rows' return already walk a row by its entry `k`. The columns' return needs `k` from `(i, j)`: a near entry from `i − j`; for an open `i`, `NEAR_SLOTS` plus `j`'s rank among the region's definite sites; for a definite `i`, `NEAR_SLOTS` plus the definite counts of `i`'s probed classes before `j`'s plus `j`'s rank in its run. A host reading of a share row scatters `k` to `j`. The stride is the same at every tick, so no offsets are rebuilt. The bound takes a receiver's probed classes as distinct, as the driver lists them ([agent-inferred] from `support_at` and `row_prepare`); the realization checks it where it prepares a row and refuses past it. Its acceptance is the bits: one lap from the ninth lap's state gives the dense build's tenth state, byte for byte. It is built after the amended carry (one change at a time in that driver). An arena for a batch's buffers, which design proposed, waits on the profile after this step, since the step changes every buffer's size.

**The second step: a paced skin's exponent is read from two site addresses** (theory, 04:14 UTC; a realization, every bit kept; atlas `tower.field-skin-site-address`). This is the wide word of 4.4, found by reading the contact kernels' arithmetic term by term. A turned head's clock is paced (`tower.field-pace`): the skin between two sites is `D_m(i,j) = e^(−2π|σ_h(i) − σ_h(j)|/n_m)`, with `σ_h` the running sum of the magnitudes of the head's rates. The card reads its exponent as a whole count of the face's bits,

```
bits(i, j) = nearest( 2π |σ_i − σ_j| / k_m ),     k_m = n_m · ln 2 · 2^24        (π on 2^-46, ln 2 on 2^-30, σ on 2^-24)
```

which is a division of a 128-bit word for every pair of distinct sites: the numerator passes 2^63 once the two clocks differ by 0.0012, and a site adds about one. The card has no instruction for that division, and the kernel file's own note calls it a long software routine. The built kernels run it anew at every use of a skin. A pair of sites of a paced head and tick pays it 8 times in the exposure (one a mode), 16 in the contact's numerators (a lane an entry, where a mode's two entries repeat it), 24 in the rows' return, 32 in the columns' return and 8 in the skin's own return: 88 in all. The paced moments call it through their own reader. The entries that read a paced skin (the columns' and the rows' return, the limb rows, the exposure, the skin's return and the four paced moment entries) hold 0.666 of a training lap's kernel time.

The division belongs to the site. Each site's clock has an address on a mode's circle, a whole winding and a residue, taken once:

```
2π σ_x = q_x k + r_x,    0 ≤ r_x < k                          once a site, paced head, mode and tick, beside σ
for σ_i ≥ σ_j:    Q = q_i − q_j,   R = r_i − r_j;    R < 0  ⇒  (Q, R) ← (Q − 1, R + k);    bits(i, j) = Q + [R + ⌊k/2⌋ ≥ k]
```

A pair then reads the difference of two windings with one borrow and one rounding carry: two subtractions and two compares on words of `k`'s width, in place of the division. It is the same integer. The proof is the carry law used twice (`ratio.div-rem`; Lean `Geometry/PhaseCarry`). `winding_add` on `a = (a − b) + b` gives `winding(a − b) = winding a − winding b − [phase a < phase b]`, the borrow. `winding_add_right` gives `winding(x + ⌊k/2⌋) = winding x + winding(phase x + ⌊k/2⌋)`, the rounding carry. The receipt script checks the pair's form against the kernel's own on 1,270,714 integer pairs, with every tie of the small numbers. Its hypotheses: `k > 0`; `σ` is a running sum of magnitudes, so the later site holds the larger `σ` and the order is the sites' own; `2πσ` stays inside the 128-bit word (about 2^84 at 2,300 sites); and `r` is as wide as `k`, which passes a signed 64-bit word at `n ≥ 739` and an unsigned one at `n ≥ 1478` (the order to design said 724, a slip corrected at 04:19). The width is read from `k` and never chosen.

On the objects this is the helical code's reading of a strand, residue and whole winding, applied to the skin's clock. A site carries its address on each mode's circle, a pair's exponent is the difference of two addresses, and the only thing left to the pair is the carry. It is the digit partition of 4.4 inside the card: the wide word once at the site, of which a region has `S`, and the narrow carry at the pair, of which it has `S K`. The exponential's face and the release follow as now. Acceptance is the bits, as for the stride: parity with the host, and the tenth state's bytes after one lap from the ninth. The driver takes one change at a time, in this order: the amended carry's scan, this step, then the stride. Noted and not ordered: a pair's eight skins kept once a pair (it wants the support's address, so it follows the stride); one product in place of two in a numerator (`(face · |v|) · 2^b` for `(face · 2^b) · |v|`); a mode's two entries sharing one skin.

Fixed and unread:

- **G39** (01:31 UTC; design, one section at the current state, with the built site weights). Split the section's deposit covector `G` by place at mass 2^-6 into `G_quiet + G_loud`. `|G_quiet| / |G|` is 0.30 (0.15 to 0.45) and the cosine of `G_loud` with `G` is 0.93 (0.85 or more). Rule: a quiet ratio of 0.2 or less with a cosine of 0.95 or more lets cost follow news, and a clock counted in news becomes a candidate law. A quiet ratio of 0.5 or more says the quiet places carry a coherent push, and the covector mass is the wrong count for a clock.
- **G42** (03:39 UTC; the share store addressed by the support, profiled as G40 was). Batches a return 1.0 to 1.3 (4.1 now). The card's memory peak 6 GB or less (12.3 now). A lap's wall 880 s (800 to 960; 1,070 now). Kernels 0.85 or more of elapsed and allocations 0.04 or less. The forward contact 1.0 ns a pair met or less (1.30 now; fixed against 1.24, which left out the six-limb rows). Rule: a lap above 960 s with the batches at one a return says the fixed cost a batch was not the cost, and the phase trace (`FIELD_PHASES`, built) decides the next step. Noted at 03:42, after fixing and before any read: the re-draw's 1.77 ns a pair met gives the last clause's premise no support, and a miss on it is expected. Restated at 04:14, before any read, since the second step may land first: the stride removes 190 s a lap (110 to 270).
- **G44** (04:14 UTC; the second step alone, on the same profiled 300 training sections from the ninth lap's state). The entries that read a paced skin fall together by 0.38 of their kernel time (0.20 to 0.60). Kernel time a section falls by 0.25 (0.12 to 0.40; 0.524 s now). The forward contact takes 0.80 ns a pair met (0.55 to 1.05; 1.30 now), and the re-draw read's 1.0 (0.7 to 1.4; 1.77 now). Rule: a fall under 0.10 on those entries says the division was not the cost and the limbs and the gathers are, and the next reads are the mean grid by entry and the contact split by pass. A fall of 0.20 or more says a pair's deep chain was the wide word, and the next step in the vein is the pair's skins kept once. Its basis is an estimate and unmeasured: instruction counts read from the source, a paced skin about 250 a call against about 80 for the rest of a term and entry. The exposure's time a pair against the limb rows' (0.40 to 0.84 ns) does not discriminate, since the work outside the skin could give that ratio alone.

Scored above, as fixed:

- **G40** (01:48 UTC; design, a profiled card read of training sections from the current state). Kernels are 0.85 or more of the profiled time and allocations 0.03 or less. Entries under 200 µs a launch hold 0.10 of kernel time (0.05 to 0.16). The contact family (the exposure, the limb rows, the reverse rows and columns, the pair, the echo, the skin's return and the spread) holds 0.60 (0.50 to 0.75) and the affine maps 0.08 or less. The five heaviest entries hold 0.55 or more, each in the contact or the moment family. Rule: with the contact family at 0.50 or more, the card's lever is the wide row, and the digit partition of 4.4 is derived for it as a realization that keeps every bit. With the short launches at 0.15 or more, those entries are the first candidates for the host by `n*`.

## 8. What does not transfer, and the lessons checked

- The joule floor does not bind (eighteen orders). Only the count transfers.
- Synchronous data flow's balance equations give a fixed rhythm for fixed rates. The machine's rates follow its news, so the rhythm is read at each carry and never solved once. Kahn's determinacy still holds.
- Physical oscillators lock through a lossy coupling. Here the coupling is the block at a crossing, and the loss is the wait.
- The card's busy percentage is a share of time with a kernel resident. It says nothing of how many lanes a launch fills (November 7).
- One sample is not a stage's reading. The 44% that occasioned the lens was the first sample of a stage whose later samples read 0.89.
- A sampler's share of time with a kernel resident counts transfers and allocations as busy. It read 0.94 where the kernels held 0.743, and two readings built on it were withdrawn within three hours (§7). A share of a lap is read from the driver's own profile.
- A reservation is a realization's choice with a reason, and it is re-derived when the regions change. The square was the most a region's classes could ask on November 1; with an open room of 2,062 places it is 25 times the support.
- A wide operation is placed by the index it depends on. The skin's exponent depends on two sites and its division on one; computed at the pair it ran 88 times a pair, and the digit partition of 4.4 puts it at the site and leaves the pair a carry.
- No lane owns a part of the law (the traffic record, §5). "The upper grains are the host's" is a consequence of counts on this machine, and it moves when the counts move.
- A table of each place's last face, kept so the next lap can skip quiet places, is refused as machinery: it is addressed by a named subject, has no dynamics, and grows with the passage (the cache test). If cost is to follow news it is by the field's own clock.
- Fewer visits to quiet places would be less data under another name unless the law itself counts its clock in news. Nothing here licenses a cut of the workload (GPU first).
- Lessons named before the choice: the learner carried on host threads (answered by 4.2 and by parity); a run switch for core behaviour (a placement keeps every bit, and a delay is carried in the state); a width chosen by hand (`n*` is four measured times); a design thought in the programming language (the law is stated in rates, widths, carries and crossings, and kernels appear only as owners). The law names no modality: text, image, sound and motion differ in their grains' counts and in nothing else here.

## 9. The guides

The card rule is amended in CLAUDE.md and AGENTS.md in the same change. Its first clause no longer puts every measurement on the card, and a new clause states the host as a second surface with the three lawful kinds of host work (a reading, a placed term, a slow variable with a declared delay), the bar on wall-time joins, and the reason for the scope.

## 10. Owed

- Design: the amended carry's build first. Then the skin's site address with its parity and G44; then the support stride with its parity and G42; then the next section's tables staged under the card's stroke; the mean grid by entry when a build is open; G39 on one section. Readings stay on the host while the card trains.
- Theory: score G39, G42 and G44. After G44's read, by its rule: the pair's skins kept once a pair (after the stride), or the mean grid by entry and the contact split by pass.
- Lean, for #410: the determinacy of a join at named crossings from `raceFreeInterleaved` and `scatterAdd_perm`; the two-stroke bound `max(e, c) ≤ e + c ≤ 2 max(e, c)`; the threshold `n*` as the crossing of two affine costs; the support bound `|S_i^h| ≤ NEAR_SLOTS + ndef_r`; the borrow form `winding n (a − b) = winding n a − winding n b − [phase n a < phase n b]` for `b ≤ a` (a corollary of `winding_add`) and with it the nearest quotient of a difference from two addresses.

## Receipts

In `2026-11-11_THE_HOST_AND_THE_CARD_ARE_ONE_SURFACE_WORK_IS_PLACED_BY_RATE_AND_WIDTH_THE_SURFACES_MEET_AT_CARRIES_AND_COST_IS_OWED_AT_MERGES_receipts/`: `cap_t.py`, its two logs, the guess files (G37 to G40 as fixed; G33 to G43 with their reads), the profile lines of the two profiled reads with `profile_budget.py`, the phase trace's lines, `skin_address.py` with its log (the identity under the second step), the G44 guess file, and a README. The rulers ran on the host in under a minute each on two cores; the train passage and the held problems stay private.
