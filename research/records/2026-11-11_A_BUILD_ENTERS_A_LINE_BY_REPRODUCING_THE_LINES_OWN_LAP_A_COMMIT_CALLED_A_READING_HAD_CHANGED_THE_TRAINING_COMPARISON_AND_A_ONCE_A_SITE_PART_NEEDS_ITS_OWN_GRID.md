# A build enters a line by reproducing the line's own lap: a commit called a reading had changed the training comparison, a state tool dropped the part rates, and a once-a-site part needs its own grid

Status (2026-11-11, 06:05 UTC): a located cause, its repair and the rule that prevents it. The scan line's first lap differed from its control three ways and is discarded (§2). The scan build is repaired and reproduces the rate line's lap on every section read (G48 held, §3); the scan laps run again from the fourth part-rate state. STEP S keeps every bit and is slower as built (G44 scored, §5); its address moves to its own grid (STEP S′, ordered, G49 fixed). One guess on cost missed (G50, §6) and its cause is not yet placed (G51 fixed). The host reading on the seventh state is scored (G39 half held, G47 missed, §7; G52 fixed). Both guides gain one method rule (§4). Corrects [the flock record](2026-11-11_A_FLOCK_OF_UNLIKE_MEMBERS_JOINS_A_ROUND_ONLY_AT_ITS_OWN_GRAIN_A_PAIRS_TELESCOPING_PART_IS_TAKEN_ONCE_A_SITE_AND_A_GROUP_DETECTS_THROUGH_ITS_CONTACTS.md) §5.2 and §11. [added 06:55 UTC: G50 closes as the machine's condition and G52 is scored, in [the record of the two pushes and the timing rule](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD.md); notes are added at the ends of §6 and §7.2.] Claude (theory lead). Refs #76, #404, #407.

Read beside [the flock record](2026-11-11_A_FLOCK_OF_UNLIKE_MEMBERS_JOINS_A_ROUND_ONLY_AT_ITS_OWN_GRAIN_A_PAIRS_TELESCOPING_PART_IS_TAKEN_ONCE_A_SITE_AND_A_GROUP_DETECTS_THROUGH_ITS_CONTACTS.md) (STEP S and STEP G as ant integration), [the two-surface record](2026-11-11_THE_HOST_AND_THE_CARD_ARE_ONE_SURFACE_WORK_IS_PLACED_BY_RATE_AND_WIDTH_THE_SURFACES_MEET_AT_CARRIES_AND_COST_IS_OWED_AT_MERGES.md) (§7: the profile and the order of S), [the part-rate record](2026-11-10_FOUNDED_PARTS_AT_THEIR_OWN_DEPOSIT_RATES_GAIN_0.022_IN_FOUR_LAPS_AND_THE_FIELD_PASSES_LITTLE_PAST_TWO_LETTERS.md) (the rate line and its states) and the guides' method rules (a law, a realization and a reading are told apart by the bits).

## 1. The objects

A **line** is a tube: one learner state carried lap after lap under one law, each lap a span of 1,535 sections on the machine's own clock, with a saved state at each lap's end. A **control** is a second tube from the same saved state. A comparison of two lines reads a difference of two transports. It is a reading of one law only when the two transports differ by that law alone: with `T_L` the lap under law `L` and `s` the shared saved state, the claim "the difference of `T_(L+δ) s` and `T_L s` is `δ`'s" needs the build that carries `δ` to satisfy

`T_build|_(δ off) (s) = T_line (s)`  on the bits of the line's own lap,

which is the equation at the consumer (the comparison). Parity of a card realization against its host inside one tree checks `card = host` for that tree's law. It cannot see a difference of law between two trees, because both of the tree's realizations carry it.

The guides already sort a change by the bits ([CLAUDE.md](../../CLAUDE.md), method): a law changes what the state carries or the deposit consumes, a realization keeps every bit, a reading leaves the state's bytes the same on and off. On November 11 a change was sorted by its commit's description, and the description was wrong.

## 2. What was found

**2.1 The occasion.** [measurement, 05:04 UTC] STEP S's build (7b85bdf87 on the training line) trained one lap from the ninth part-rate state. The saved state differed from the tenth's from its 82nd byte on. The flock record (§5.2) left the question open whether the difference was S's.

**2.2 It is not S's.** [measurement, 05:20 UTC] S against its parent (b17de138b, the scan with its grid sums), each profiled from the ninth state under a 200,000 ms bound: 244 of 244 section lines equal, timings aside, and each equal to the full S lap on every section both read. S keeps its parent's bits. The parent itself differs from the rate line's build.

**2.3 The cause, read in the source.** [read in `field_train.rs` on the pushed training line, 05:23 UTC] Between the rate line's build (0b2ba0bad) and the scan stand four commits described as readings for the order field. One of them, 34989233c of November 6, changed training. The path state the source calls `writer` (the question followed by the answer's places standing open at the void) had been compared on its classes under the mask of open places, at weight one, with no port. The commit gave it a port on its letters off the void, so that training compares each open place on its letters. The rate line's laps export that path state (`FIELD_PATH_WRITER`), so every build from that commit on trained a second law. The first section already shows it: predicted change −3401 against −3399 in micro-units, external 876 against 882. After one lap 60,755 of the 63,606 material entries differ. With the carry off the rest of the host law is the old path (every scan branch stands under the declaration's carry word).

**2.3a Main had already held it.** [read on main, 06:02 UTC] The same change entered main on November 6 (c122b2533) and was held there the same day behind a declaration, the whole-class comparison staying the law (b43cc7848: read off the void, lap 12 equalled the read with it to three places, and lap 14 brought the length back on the whole-class law). The training line took the first commit and not the second. This is the lessons' failure of a located cause carried unrepaired into a new consumer, at the grain of a port: a commit was carried without the commit that corrected it.

**2.4 A third difference.** [read on the PC from the lap's log and state, 05:47 UTC] The scan line's opening state was written by `tools/add_carry.py`, which adds the third chart at zero. The tool appended the state's `parts` line and only then stripped trailing empty lines, so the empty string left by the state's last newline stayed in front of it: an empty sixth line and the parts line seventh. The field's reader takes the parts line as the line after the two moment lines, read none, and trained every part at the base rate 2^-12. Nothing refused. The lap's log has no `FIELD_PART_RATES` line.

**2.5 The consequence.** The scan line's first lap (gs1, 05:17 to 05:44 UTC, 1,535 of 1,535 sections, 1,409,614 ms) differs from its control (the rate line's fifth lap) by the scan, by the writer state's comparison and by the part rates. It is a reading of nothing and is scored against nothing. The PC's permission check refused stopping the running lap, so a halt file stopped the chain at the lap's end; the lap cost 24 minutes of the card.

## 3. The repair, and G48

**3.1 The repair.** [built 05:41 UTC; 97406d6f6 on `claude/scan-clean`, merged into the training line as 0026f2bab] `writer_region` returns the plain region again (classes at weight one, no port), with its trainer test restored and the ruling in its docstring: on this line the writer state is compared on its classes; the comparison on its letters off the void is a change of law and is tested alone with its own guess, never beside another. `Port::letters` and its reading stay. The gate passes, the field's tests pass (84, one ignored) and the trainer's (22).

**3.2 G48** (fixed 05:23 UTC, before the build). With the comparison restored, a run from the ninth state with the carry off gives the rate build's section lines on every section read (240 or more): yes, 0.85. **Held.** [measurement, 05:47 UTC; card, alone under the lock] 274 of 1,535 sections read under a 200,000 ms bound, and 274 of 274 section lines equal the tenth lap's, timings aside. Card: 46 reads, 279 returns, 16,670,246,133 pairs, peak store 8,550,145,604 bytes. Wall 216.4 s against about 215 s projected (deadline 320 s); peak resident set 813,080 KiB; the host's regions took 346 ms of the 200,039 ms. By the guess's rule the comparison was the whole difference on the sections read.

**3.3 The scan line again.** [running from 05:48 UTC] Laps gc1 to gc4 train with the repaired build from the fourth part-rate state with the third chart added at zero. The opening state has six lines with the parts line last, and the first lap printed its part rates, equal to the state's. The lap script now stops when the lap's log has no `FIELD_PART_RATES` line or the state has no parts line. The chain's stages take the card lock outside their own deadlines, so the scan laps and the trend laps take turns on the card stage by stage. G30′ and G46 are read on these laps against the rate line's fifth to eighth.

**3.4 The tool.** `tools/add_carry.py` strips the trailing empty lines before it appends the parts line, and refuses to write a state with an empty line inside. Checked on two invented states (with and without a parts line): six lines with the parts line last, and five lines.

## 4. The rule

[project-postulate; theory, from this failure] **A build enters a line by reproducing it.** Before a new build trains or reads for a running line, it trains from the line's last saved state with its new law off, and its section lines (timings aside) equal the line's own lap's on every section read. A commit described as a reading or as a realization carries its receipt in the same change: the state's bytes the same with it on and off, or the lap's bytes the same before and after. A state written by a tool is checked for every line the law reads before a lap trains from it, and a lap whose log lacks a line the law prints stops.

Reason: §2. Three differences entered one lap, each through a place where a description stood in for a receipt: a commit's subject line, a tool's success message and a tree's own parity. The cost of the rule is one bounded read (216 s here) per build per line, against a lap (24 minutes) and a comparison that would have been reported as the scan's.

Scope: every build that trains a lap of a line or whose reads enter a line's score. It does not ask that a new law reproduce the old one with the law on, and it does not reach a first build of a new line, which has no lap to reproduce. Where a line's saved state cannot hold the new law's off position (the declaration differs), the build reproduces the lap from the state as the tool rewrites it with the new part at zero, which is how the scan's chart at zero was checked against the built contact.

**What stays owed in the source.** The learner's head does not declare that a state holds part rates, so the reader cannot tell a state before the rates from a state that lost them. Until the declaration carries it (with the port to main, flock record §8.5), the lap script holds the check.

**The writer state's comparison on main** is the classes (§2.3a), so the repair returns the line to main's law and the port has nothing to decide there. Main's declaration for the letters is a run switch of the kind the guide bars since November 8; the port retires it or carries it in the state's declaration.

## 5. STEP S scored, and STEP S′

**5.1 G44** (fixed 04:14 UTC; S alone, the profiled sections from the ninth state; before 251 sections, after 244). [measurement, 05:20 UTC; card]

| Clause | Guess | Read | Score |
|---|---|---|---|
| The nine paced-skin entries' kernel time a section | falls 0.38 (0.20 to 0.60) | 385.2 to 270.6 ms, a fall of 0.297 | held |
| Kernel time a section | falls 0.25 (0.12 to 0.40) | 609.9 to 645.0 ms, a rise of 0.058 | missed, wrong sign |
| Forward contact, ns a pair met | 0.80 (0.55 to 1.05) | 1.468 to 0.963 | held |
| The re-draw read | 1.0 ns | no profile taken | unread |

The largest falls: the contact's columns 19,665 to 10,825 ms, its rows 16,866 to 10,191, the fifth lane 14,874 to 9,990, the skinned moments 12,735 to 8,668, the exposure 6,848 to 4,055.

**5.2 Why the whole rose.** [read in the kernel] The address `2π σ = q k + r` was written inside `field_paces`, beside `σ`. That kernel runs one thread a paced head and region down the region's sites in order, because `σ` is a running sum. S therefore put eight 128-bit divisions a site (one a mode) inside a chain that only as many threads run as there are paced heads and regions: `field_paces` went from 15.9 to 168.7 ms a section, and the nine entries' gain of 114.6 ms a section was spent there and past it. I fixed the guess without reading where the address would be computed. The flock record's §5.1 says the wide operation is taken once a site; it should have said on which grid.

**5.3 The lesson, on the objects.** A quantity taken once a site still has a count of co-present terms: sites times heads times modes. It is placed like any other kind of event, on a grid of that count. Only the part that is a running sum along the strand (here `σ`) needs the chain; what is a function of the sum at one site does not. Telescoping removes the pair's index, and the placement law of the two-surface record then applies to what is left.

**5.4 STEP S′** [ordered 05:51 UTC; a realization, every bit kept]. `field_paces` writes `κ`, `τ`, `σ` and the plain flag only. A new launch on a grid of one cell a (paced head, mode, site) reads `σ` and writes the three words of the address, directly after each of the three launches of `field_paces`, and writes only the cells inside a region. Where no refusal is raised the stored `σ` is the running sum itself, so the integers are the ones S wrote. Acceptance: the gate, the field's and the trainer's tests, the card parity S's commit ran, and then the profile below with every section line equal to its parent's and to the tenth lap's.

**G49** (fixed 05:27 UTC, unread). Against its parent on the same profile: (a) kernel time a section falls by 0.20 of the parent's (0.14 to 0.26); (b) `field_paces` and the new launch together take 25 ms a section or less; (c) the nine entries stay within 0.05 of 270.6 ms a section. Rule: (a) at 0.14 or more with every section line equal, S′ is accepted on a lap's bytes and enters the lines at a lap boundary; (b) over 60 ms, the division is itself the cost at this grid and the next read is the launch's grid sum against its cell count. The count of divisions a section is unmeasured.

[added 07:27 UTC: read in one hold of control, S′, control, and held on all three parts ([the record of the two pushes, §10](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD.md)). Kernel time a section 609.9, 458.5 and 609.3 ms (a fall of 0.248; the two controls agree to 0.1%); the clocks' launch 15.6 ms and the address's own launch 1.98 ms a section; the nine entries 257.4 ms; 316 of 316 section lines equal the tenth lap's. S′ is accepted on the rate line's bytes. Its entry to the scan line is the same read with the carry on, against the first clean scan lap.]

## 6. G50: the repaired build ran slower than the tenth lap, and the cause is not yet placed

**G50** (fixed 05:51 UTC; logs only). Over sections 0 to 273 the repaired scan build's section time is within 3% of the tenth lap's on the same sections: yes, 0.70. **Missed.** [measurement, 05:53 UTC; from the two runs' logs] 200,039 against 174,464 ms, a ratio of 1.147. The regions' time is 346 against 387 ms; the deposit's is 195,959 against 170,916 ms, the same ratio, so the difference is in the deposit. A gate was building on the host during the first half minute of the repaired build's run. Past it (sections 60 to 273) the ratio is 1.151, and by blocks of fifty sections 1.129, 1.166, 1.109, 1.162, 1.201 and 1.081, so the build's contention is ruled out.

**6.1 What the two profiles show.** [reading, 05:56 UTC; the rate build's profile over 301 sections against the scan tree's before S over 251, a section being a run's total over its sections read] Kernels 523.8 against 609.9 ms a section, allocations 65.5 against 88.9 ms (1,179 against 1,241 a section), copies 15.2 against 19.4 ms. Every entry is in both and the launch counts a section agree. Forty-three entries gain 0.3 ms a section or more and none falls; the five largest gains (the contact's fifth lane 10.31, its columns 9.01, the spread 6.76, the paced skin's reverse 5.58, the contact's rows 4.12) hold 35.8 of the 86.1 ms. Large kernels gain 8% to 22% a launch, and the shortest gain a near-fixed 100 to 170 µs a launch.

**6.2 What the source shows.** [read in the kernels and the driver, 0b2ba0bad against b17de138b] The gaining kernels and their launches are unchanged. On the path every launch shares, the kernels' words gain seven 8-byte fields, each tick takes four more device buffers (one word each with the carry off) and each reverse one more, and the affine map gains one branch.

**6.3 Two readings, and the read that tells them apart.** Either the tree costs the fifteen percent with the carry off (the five small buffers a tick, or the wider words passed by value), or the machine's condition differed: every class of call slowed by a like factor (kernels 1.16, a take 1.29, copies 1.28), and no pair so far holds one binary at both times (the rate build ran from 02:56 to 04:05 UTC, the scan tree from 05:15 to 05:47). My basis for G50 was wrong either way: equal bits do not fix equal launches or equal times.

**G51** (fixed 05:57 UTC, unread). The rate build, run now from the ninth state on the acceptance run's harness, reads sections 0 to 273 within 5% of the repaired build's 200,039 ms and not at the tenth lap's 174,464 ms: yes, 0.60. Rule: held, the condition is read next (the card's and the host's samples, the laps' times in order) and G50 is read again against a control at the same time; missed, the tree holds the cost and one build separates the buffers taken once a field from the wider words. Until it is read, the scan line's cost against its control (G45's ratio) is stated only against a control run the same hour.

[added 06:55 UTC] G51 is scored and missed (183,220 ms: 1.050 of the tenth lap's time, 0.916 of the repaired build's). A further guess that placed the remaining 9% in the tree, in the kernels' wider words, also missed (G53): in one hold of the card the rate build, the scan build and a rate build with the wider words agree within the hold's own drift, and one binary reads 5.5% apart eleven minutes apart. G50 closes as the machine's condition; nothing is built for it; §5's second score (the whole kernel time rose 0.058) is inside that drift and is not resolved by its read, while its entries stand. See [the record of the two pushes and the timing rule](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD.md) §5.

## 7. The host reading on the seventh state: G39 and G47 scored

[measurement, 05:57 UTC; host, eight threads, the reading manifest, no card; wall 91.2 s against a deadline of 900 s; peak resident set 1,874,876 KiB; the state's digest the same before and after] One section at the seventh part-rate state (48 regions, 51,717 sites, 40,731 compared places), its deposit covector `G` split by place at news mass `m_t = ½ |p̂_t − q_t|₁ < 2^-6` (flock record §8.4). The host binary was rebuilt on the repaired tree first, so the reading compares the writer state as the seventh lap trained it.

**7.1 G39** (fixed 01:31 UTC). `|G_quiet|/|G|` 0.30 (0.15 to 0.45): read 0.0125, **missed**. The cosine of `G_loud` with `G` 0.93 (0.85 or more): read 0.9999, **held**. The first missed because 1,323 of the 40,731 places are quiet at `2^-6` (0.032): I set the threshold without a count of the places under it, and at this state the field gives almost no place its compared letter at 0.984 or more. By the letter of the guess's rule cost may follow news. By the measurement the split removes three places in a hundred and reads nothing about cost, so the rule is not taken as met and the read is repeated at coarser thresholds.

**7.2 Beside the guess.** By part, the cosine of `G_quiet` with `G` is negative in every family but the pace and one bias: −0.177 whole, −0.904 in the temper, −0.641 and −0.473 in the two moments, −0.532 in `v`, +0.784 in the pace. Read on the objects: where the field already gives a place its letter, the covector that reached that place asks the shared parts for the opposite of what the other places ask, and most strongly of the locks' temperatures (one a head and receiver kind, eight entries); the clocks' rates are the family on which the two agree. That is a tension between two populations served by one constitution. It is one section and 1,323 places, so it is said of this read and not of the field until the coarser thresholds repeat it.

**G52** (fixed 06:00 UTC, unread; the same split at `2^-1`, where a place is quiet when the field gives its compared letter more than a half). Quiet places 0.25 of the compared places (0.15 to 0.40); `|G_quiet|/|G|` 0.12 (0.05 to 0.25); the cosine of `G_loud` with `G` 0.98 or more; in the temper the cosine of `G_quiet` with `G` is −0.5 or under and in the pace it is positive. Rule: quiet places 0.15 or more with `|G_quiet|/|G|` 0.15 or less and the cosine 0.98 or more, a deposit that visits by news loses under a fiftieth of its direction on those places, and a visit clock counted in news earns its derivation as a law with its own guess; `|G_quiet|/|G|` 0.40 or more, the places the field already gives carry a coherent push and the news mass is the wrong count for a clock. The thresholds `2^-2` to `2^-5` are read beside it for the curve and are not guessed.

[added 06:55 UTC] G52 is scored: the quiet share 0.090, `|G_quiet|/|G|` 0.51 and the cosine 0.907 missed; the temper's and the pace's signs held. At `1/2` the places the field gives carry half the deposit's length and push against the rest in every part but the pace. See [the record of the two pushes and the timing rule](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD.md) §2 to §4.

**7.3 G47** (fixed 04:55 UTC: one host lane's time for one region, forward and return, over the card's all-in time a region in training, 30, band 10 to 80). **Missed**, above the band. Read on the same run: 137,873 ms forward and 172,572 ms return of thread time, 310,445 ms for one lane. The common unit is the section itself: the reading's section is the first of the eighth lap, and that lap's log gives the card 650 ms for it (regions 1 ms, deposit 649 ms; the line's further 873 ms on that first section is the lap's opening work). The ratio is 478: a host lane takes about 480 times the card's time on the line's own section, 6,468 ms against 13.5 ms a region over its 48 regions. Twenty lanes at that price are worth 0.042 of the card. By the guess's rule training stays whole on the card and the line's reads stay on the card. Eight threads ran at 0.67 of their sum.

[corrected 06:05 UTC] This paragraph first gave "91 by site" and "147 by the guess's region", and said the reading's section was not a training section's shape. Both ratios were wrong. The first divided the host's time by the regions' summed lengths (51,717, the split verb's count) and the card's by its compared sites (the training log's `sites`): two counters under one name. The second used the 44 ms a region of the guess's text, which assumed sixteen regions a section where this one holds 48. The section is a training section, counted two ways. It is the third time in one night that I priced a device across two units; both guides now add that two devices are compared on one unit of work run on both, never across counters that share a name.

**7.4 What the reading shows about the host.** A reading from a saved state ran for 91 s on eight host threads while the card trained, and no lap waited for it. This is the first of the guide's three lawful kinds of host work, used.

## 8. What does not follow, and the lessons checked

- **The scan is not judged.** No lap of the scan has been read. gs1's reads are discarded.
- **The letters comparison is not re-opened.** Main read it on November 6 and held it (§2.3a). One lap of it from the ninth state exists on the PC (the S lap) and is read only if the port asks.
- **S is not refused.** It keeps bits and reduces its nine entries as guessed. Its placement was wrong.
- **No workload was cut**, no limit raised, and the lost lap is reported as lost.

The recorded failures checked: a located cause carried unrepaired into a new consumer (this was that failure, §2.3a; the repair precedes the scan laps, and the tool is repaired where it is owned, on main); bits read as progress (none claimed); two machines under one name (the no-switches rule: the absent parts line made one, and the lap script now stops on it).

## 9. Corrections to the flock record

- §5.2: the lap's difference was not S's. S keeps its parent's bits (§2.2 here); the difference was the writer state's comparison (§2.3).
- §11, first item: located (§2), repaired (§3); S's acceptance is S′'s (§5.4).
- The atlas row `tower.field-skin-site-address` said the first read of a lap's bytes did not pass and the step was not accepted until the difference was located. It now states the score and the placement.

## 10. Owed, in order

- G51's read (one bounded run of the rate build on the card, with the card's and the host's samples), and then G50's cause.
- G52's read: the split at the coarser thresholds (host, eight threads, between the card's timing reads).
- S′'s build and G49's read; then its acceptance on a lap's bytes. [done 07:27 UTC, on the rate line; the scan line's entry is owed with the carry on]
- G's acceptance (scan parity on four sections, a clean scan lap's bytes, the 188-section ratio; G45).
- The support stride with G42.
- The port (flock record §8.5), with the declaration of the part rates and the writer state's comparison decided as a law.
- The scan laps (G30′, G46 on gc1 to gc4) and the trend laps (G43), scored as they are read.

## Receipts

In `2026-11-11_A_BUILD_ENTERS_A_LINE_BY_REPRODUCING_THE_LINES_OWN_LAP_A_COMMIT_CALLED_A_READING_HAD_CHANGED_THE_TRAINING_COMPARISON_AND_A_ONCE_A_SITE_PART_NEEDS_ITS_OWN_GRID_receipts/`: `guess_capacity_44_52.txt` (G44's score, the finding on 34989233c, G48 as fixed and scored, the note on the refused stop, G49 as fixed, the finding on the state tool, G50 as fixed and scored, the reading of the two profiles, G51 as fixed, G39's and G47's scores and G52 as fixed, each with its time). The profiles, logs and states are on the PC under the run's directory; none derives from public material alone, so none is committed. Devices: every training run and profile on the card (RTX 4080 SUPER, alone under the card lock); the split reading on the host (eight threads, under the reading manifest); the log sums and the source reads on the host or the cloud container, no model compute.
