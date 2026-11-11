# The places the field gives push against the places it misses, the deposit is their difference, and two builds are timed only inside one hold of the card

Status (2026-11-11, 06:55 UTC): two readings scored and one rule. (1) The host reading of a section's deposit covector, split by place at six tolerances of news, is scored (G52: three numbers missed, two held; §2). The places the field already gives its letter push against the places it misses in every part but the clocks' rates, and the deposit is the difference of the two pushes (§3). A deposit that visits by news is closed for this state (§4); whether the holding push is one common mode of the field is fixed as a guess and unread (G54, §6). (2) The cost that the repaired scan build showed against its control was the machine's condition and not the tree (G51 and G53 scored, both missed; G50 closes; §5). No build is ordered for it. Both guides gain one rule: two builds are timed against each other only inside one hold of the card, interleaved with a repeated control (§5.5). Continues [the line-entry record](2026-11-11_A_BUILD_ENTERS_A_LINE_BY_REPRODUCING_THE_LINES_OWN_LAP_A_COMMIT_CALLED_A_READING_HAD_CHANGED_THE_TRAINING_COMPARISON_AND_A_ONCE_A_SITE_PART_NEEDS_ITS_OWN_GRID.md) §6 and §7. Claude (theory lead). Refs #76, #404, #407, #410.

Every guess here was fixed with its clock time before its read; the file is in the receipts. Machine numbers are integers of the logs; ratios are theirs, released to the digits shown.

## 1. The objects

- **The deposit covector of a section**, `G = Σ_t g_t`: the coholon that reached the constitution's material from the section's compared places `t` (each an open site with a face), every family on its own grain. Deposition is the only law that changes the constitution, and `G` is what it consumes.
- **A place's news mass**, `m_t = 1 − p_t(x_t)`: half the distance `|p_t − q_t|₁` of the place's face `p_t` from its truth `q_t` (the indicator of its compared letter or class `x_t`). It is the receipt's reading at that place.
- **The split at a tolerance** `ε = 2^(−b)`: the quiet places `Q_ε = {t : m_t < ε}` and the loud places, the rest. The return is linear in the faces' covectors once the forward pass is fixed, so `G = G_q(ε) + G_l(ε)`, where `G_q` is the return with the loud places' face covectors zeroed. At `ε = 1/2` a place is quiet where the field gives its compared letter more than a half.
- **The consumer**, stated as an equation there. A deposit that visits only the loud places deposits `G_l`. It is the same deposit to first order where `⟨G_l, G⟩ / (|G_l| |G|) ≥ 1 − δ` and `|G_q| / |G| ≤ δ′` at declared `δ, δ′` (`receipt.news-concentration-locked-faces`; the clock that would use it is `hnn.tower-news-clock`).
- With `l = |G_l|/|G|`, `q = |G_q|/|G|` and `c = cos(G_l, G_q)`: `1 = l² + q² + 2 l q c`, so the read's four columns give the angle between the two pushes.

The reading is a ruler in the guide's sense: it opens a saved state read-only on the host, leaves its bytes the same (the digest is checked before and after each read), and no lap waits for it.

## 2. The read, and G52 scored

[measurement, 06:17 to 06:27 UTC; host, eight threads, the reading manifest, no card; six reads in 611 s against a deadline of 720 s; peak resident set 1,876,108 KiB at most; the state's digest the same before and after each read] One section at the seventh part-rate state (lap 58; the first section of the eighth lap; 48 regions, 40,731 compared places), the same section and state as G39's read. The read at `2^-6` reproduces the 05:57 read (the two covector files equal byte for byte).

| tolerance `ε` | `2^-1` | `2^-2` | `2^-3` | `2^-4` | `2^-5` | `2^-6` |
|---|---|---|---|---|---|---|
| quiet places | 3,665 | 3,128 | 2,725 | 2,128 | 1,677 | 1,323 |
| share of the compared places | 0.090 | 0.077 | 0.067 | 0.052 | 0.041 | 0.032 |
| `q = \|G_q\|/\|G\|` | 0.5095 | 0.2109 | 0.1043 | 0.0542 | 0.0264 | 0.0125 |
| `l = \|G_l\|/\|G\|` | 1.1930 | 1.0618 | 1.0267 | 1.0102 | 1.0044 | 1.0023 |
| `cos(G_l, G)` | 0.9068 | 0.9809 | 0.9950 | 0.9986 | 0.9997 | 0.9999 |
| `cos(G_q, G)` | −0.161 | −0.197 | −0.207 | −0.163 | −0.154 | −0.177 |
| `c = cos(G_l, G_q)` | −0.562 | −0.384 | −0.303 | −0.214 | −0.179 | −0.190 |

**G52** (fixed 06:00 UTC, the split at `2^-1`).

| | guess | read | |
|---|---|---|---|
| quiet share of the compared places | 0.25 (0.15 to 0.40) | 0.090 | missed, under the band |
| `\|G_q\|/\|G\|` | 0.12 (0.05 to 0.25) | 0.5095 | missed, above the band |
| `cos(G_l, G)` | 0.98 or more | 0.9068 | missed |
| temper: `cos(G_q, G)` | −0.5 or under | −0.917 | held |
| pace: `cos(G_q, G)` | positive | +0.433 | held |

By the guess's rule (`|G_q|/|G|` 0.40 or more): the places the field already gives carry a push that does not average out, and the news mass is the wrong count for a visit clock.

Why two of the numbers missed. I summed the quiet places as if their covectors were unlike one another, so that their lengths add in squares. On that reckoning, with a place's covector taken at the size of its news mass and the places counted by octave as read, the quiet places' length comes to about 0.06 of the loud places'. It reads 0.43 (0.5095 over 1.1930), seven times that. Either the quiet places add nearly in one direction, or the loud places cancel among themselves, or both; the read does not separate these, because the lengths of the places' own covectors are unread. The atlas row already said that many small like pushes can outweigh a few large scattered ones, and I guessed against my own row. The first number missed because at this state the field gives one place in eleven more than a half.

## 3. What the curve says

**3.1 The margins are spread evenly by octave.** Between successive tolerances lie 537, 403, 597, 451 and 354 places: near equal counts an octave of news, about 1.1 places in a hundred an octave, from `1/2` down to `2^-6`, with 1,323 below. A count that is flat by octave of `1 − p` is flat in the log of the odds: the places the field gives are spread evenly in margin and not gathered at one confidence.

**3.2 The holding push halves an octave.** `|G_q(ε)|/|G|` falls by 2.42, 2.02, 1.92, 2.05 and 2.11 from each tolerance to the next: `|G_q(ε)| ≈ ε |G|` within a fifth, over five octaves. With equal counts an octave and a place's covector of the size of its news, each octave holds half the length of the one above, so this is what §3.1 gives for either a like or an unlike sum; it fixes no direction by itself.

**3.3 Each octave of margin, alone, points against the deposit.** The projection of `G_q(ε)` on the unit of `G` is `q · cos(G_q, G)`: −0.082, −0.042, −0.022, −0.0088, −0.0041, −0.0022. Their differences are the projections of the octaves' own covectors: −0.040, −0.020, −0.013, −0.0047, −0.0019. Every octave of margin, taken alone, projects against the section's deposit, and the cosine of the nested sums with `G` stays between −0.15 and −0.21 at all six tolerances. To first order the deposit of this section raises the code on the places the field already gives while it lowers it on the rest.

**3.4 By part, the two pushes oppose.** [computed from the read's rows by `1 = l² + q² + 2lqc`] At `ε = 1/2`:

| part | entries | `q` | `l` | `c = cos(G_l, G_q)` | `l + q` |
|---|---|---|---|---|---|
| temper (the locks' temperatures, one a head and receiver kind) | 8 | 0.757 | 1.721 | −0.973 | 2.48 |
| `v` | 4,096 | 1.210 | 1.932 | −0.898 | 3.14 |
| moments after | 3,232 | 0.958 | 1.747 | −0.887 | 2.71 |
| moments before | 3,232 | 0.642 | 1.466 | −0.830 | 2.11 |
| `b` | 4,096 | 0.677 | 1.341 | −0.693 | 2.02 |
| `a` | 4,096 | 0.585 | 1.285 | −0.661 | 1.87 |
| whole | 63,606 | 0.510 | 1.193 | −0.562 | 1.70 |
| read | 4,096 | 0.275 | 1.036 | −0.263 | 1.31 |
| pace (the clocks' rates) | 202 | 0.236 | 0.923 | +0.213 | 1.16 |

In `v` each push is longer than their sum: the deposit there is 1.0 where the two populations ask for 1.93 and 1.21 in nearly opposite directions. The temper's opposition holds at every tolerance (−0.97, −0.96, −0.93, −0.94, −0.93, −0.91). The clocks' rates are the one part on which the two populations agree.

**3.5 The temperature's opposition is derived.** For a face `p ∝ e^(−E/T)` the covector of its temperature at a place with truth `u` is the centred surprise `−ln p(u) − H(p) = (E(u) − ⟨E⟩_p)/T` (`ratio.face-temperature-covector`, checked in Lean). Where `u` is the face's most likely class, `−ln p(u)` is the least surprise and `H(p)` is the mean surprise, so the covector is zero or negative: `H_∞(p) = −ln max_v p(v) ≤ H(p)`, with equality only on a face flat on its support (`ratio.face-temperature-sign-at-the-mode`, a new row; its Lean statement is owed in #410). A place quiet at `ε ≤ 1/2` has `p(u) > 1/2`, so `u` is its mode. Hence every place the field gives asks its temperature colder and none asks hotter: on a shared temperature the given places add in one direction with no cancellation, and the temperature's covector is the difference between that pull and the missed places'. Its zero is the lock's own balance (the mean surprise equal to the mean entropy), the calibration that `ratio.face-temperature-covector` states at the true conditional. The field's eight temperatures reach the faces through their heads, so the single-face statement is carried to them by the measurement (−0.97), not by this derivation.

**3.6 The other parts' opposition is measured, and its cause is unread.** A reading, `agent-inferred`: the face covector of a given place is `m_t ([x_t] − r_t)` with `r_t` the face's remainder, which deepens the well the place sits in; that of a missed place whose face leans to a class `w` is nearly `[x_t] − p(w)[w]`, which raises `w` there. Where `w` is a class that the same modes give rightly at the given places, the two ask the shared modes for opposite things, and the deposit moves the wall between a held well and the places it wrongly captures. The test that would read it: the missed places' leading classes against the given places' truths on shared modes, with the classes' base rates divided out (a host ruler; owed, §8). Until it is read, §3.4 is a measurement with no cause attached outside the temper.

## 4. What follows for the machine

**4.1 A deposit that visits by news is closed at this state.** At `2^-6` the quiet places are three in a hundred and carry 0.0125 of the covector's length: leaving them out saves three places in a hundred and changes nothing, so it earns no law. At `1/2` they are nine in a hundred, and leaving them out turns the deposit by 25° (`cos` 0.907) and removes the whole push that holds what the field gives. Cost does not follow news while the field gives one place in eleven. The 01:55 note asked whether cost may follow news and named the coherence of the quiet places' pushes as the unread quantity; it is read: they do not average out, and they oppose.

**4.2 The share of given places is a structure measure.** The quiet share at `1/2` (0.090 at lap 58) and the angle between the two pushes by part are order parameters of the state, in the sense of the guide's rule on judging by structure. The share is owed as a line of each lap's held read, where the faces are already formed (§8).

**4.3 A part whose deposit is a small difference of two large pushes.** In `v`, the moments and the temper the net is the difference of pushes two to three times its length. A section's covector in such a part then swings with the section's mix of given and missed places. Predicted, unread: these are the parts whose covectors agree least between sections, and `hnn.field-family-lengths` (a part's step shortened while the next section pays) is the law that already answers it. G54's tables read the first half.

**4.4 The lens of 04:33 UTC, used.** Brandon's flock lens reads the card and the host as unlike members of one ecology, each on its own kind of work ([the flock record](2026-11-11_A_FLOCK_OF_UNLIKE_MEMBERS_JOINS_A_ROUND_ONLY_AT_ITS_OWN_GRAIN_A_PAIRS_TELESCOPING_PART_IS_TAKEN_ONCE_A_SITE_AND_A_GROUP_DETECTS_THROUGH_ITS_CONTACTS.md)). If the holding push is one slow common mode of the field (the same direction from every section; G54), it is the kind of quantity the guide's third lawful kind of host work carries: a slow variable read from a saved state at a lap's boundary and joined at the next, while the card visits the places that carry news. That law is not derived here and not built: at a quiet share of nine in a hundred it would save nine places in a hundred. It is stated with its condition (the share large, and G54 held) so that the next read of the share decides whether to derive it.

**4.5 What does not transfer.** The discipline's apparatus for this balance (a temperature fitted after training on held material) stays in the discipline: the lock's temperature has its own covector in the deposit and its balance is §3.5's.

## 5. The cost that was the machine's condition: G51, G53, and the rule

**5.1 G51 scored.** (Fixed 05:57 UTC: the cost is the machine's condition; the rate build, run now from the ninth state on the acceptance run's harness, reads sections 0 to 273 within 5% of the repaired build's 200,039 ms; yes, 0.60.) **Missed.** [measurement, 06:13 UTC; wall 214.2 s; peak resident set 840,748 KiB; 300 of 300 section lines equal the tenth lap's] 183,220 ms: 1.050 of the tenth lap's 174,464 ms and 0.916 of the repaired build's 200,039 ms. The guess asked for within 5% of 200,039; it read 8.4% under. I then read the 9.2% between the two as the tree's cost with the carry off, though the two runs stood 50 minutes apart.

**5.2 What the source and the images show.** [read in the cloud clone and in the two binaries' images on the PC; no card] The words every kernel receives by value are 1,016 octets at the rate build (137 fields) and 1,072 at the scan tree (144), in every entry read; the seven new fields carry them past 1,024. The kernels read four of the seven (the scan's buffers), in the scan and its reverse only; the other three are read by no kernel. No entry read declares local memory in either image, the register declarations are equal in both, and the entries that do declare local memory declare the same sizes: a thread does not copy the words and no frame grew. The driver's documentation (the context flags, 12.3) says local memory is no longer shrunk after a launch. The pool serves a one-word request from a kept buffer of 4 to 8 words, so the five one-word buffers a tick are kept buffers taken again.

**G53** (fixed 06:28 UTC, before the image read; one hold of the card; four reads from the ninth state on the acceptance run's harness, 200,000 ms bound, no profile: R1 the rate build, C the repaired scan build with the carry off, P the rate build's tree with seven unused 8-octet words appended to the kernels' words and nothing else changed, R2 the rate build again; unit: section times summed over sections 0 to 273; R the mean of R1 and R2). (a) `C/R` 1.09 (1.06 to 1.12), yes 0.65. (b) `P/R` 1.06 or more and P within 2% of C, yes 0.50. (c) `R2/R1` within 0.97 to 1.03.

**5.3 The read.** [measurement, 06:33:14 to 06:47:41 UTC; one hold of 867 s against a deadline of 1,280 s; every build on the host paused through the hold and nothing else started; every section line of every read equals the tenth lap's, so the padding kept every bit]

| read | sections read | ms over sections 0 to 273 | of the tenth lap | wall s | peak resident set KiB |
|---|---|---|---|---|---|
| R1, rate build | 298 | 185,048 | 1.061 | 214.8 | 820,052 |
| C, scan build, carry off | 308 | 178,945 | 1.026 | 213.0 | 791,656 |
| P, rate tree, 1,072-octet words | 309 | 178,274 | 1.022 | 225.9 | 986,736 |
| R2, rate build | 313 | 174,837 | 1.002 | 212.5 | 859,092 |

P's wall includes the driver's first compile of an image the card had not run.

- (a) `C/R` = 0.994. **Missed.**
- (b) `P/R` = 0.991; P is within 0.4% of C. **Missed.**
- (c) `R2/R1` = 0.945. **Missed.** One binary read 5.5% apart, eleven minutes apart, inside one hold; by blocks of fifty sections R1 over R2 is 1.074, 1.041, 1.032, 1.095, 1.051, 1.063.

The four reads fall in the order they ran. Against a straight line from R1 to R2, C reads 0.985 and P 1.000. Inside the hold's own drift no tree is slower than another, and the words' size costs nothing that this read resolves (about 2%). By G53's rule: the 9.2% was the machine's condition; G50 closes as the machine's condition; the step that would have moved the scan's buffers out of the words is not ordered.

**5.4 What carried the drift is unread.** [5 s samples through the hold, medians by read] The card read 63 °C, 2,805 MHz, 176 to 178 W, 94% to 95% busy and 11.3 GiB held in all four reads. The host's one-minute load read 1.71, 0.98, 0.42 and 0.31 and its mean core frequency 4,727, 4,338, 4,073 and 3,989 MHz in the order of the reads. Across five reads of the same sections (these four and the 06:13 control) the reads' mean times rank with the host's load (rank correlation 0.9 on five points, inseparable from their order in time); within a read no sampled quantity tracks the section time beyond a rank correlation of 0.4 over 203 aligned windows. The card also serves the desktop (seven graphics processes at the 06:13 read). Which of the host's other work and the desktop's share of the card carries the drift is not placed; the next hold records each process's share of the card and of the host.

**5.5 The rule, and what was wrong in my reasoning.** Three guesses in a row were spent on one variation. G50 took the machine as the same across two and a half hours. G51 named the machine as the whole cause without a control at the hour of the read it explained. G53 read a difference of 50 minutes as a difference of tree, and I found a threshold in the source (1,024 octets) to hang it on. The profile's near-fixed gain a launch on kernels whose source had not changed was the evidence I leaned on; it is what a machine that is also doing other work does to every bracketed launch. Both guides now say:

> Two builds are timed against each other only inside one hold of the card, on the same sections, interleaved with a control that runs at least twice, with every other build on the host paused; the control's own spread is the read's resolution, and a difference inside it is no difference.

**5.6 What it reopens.**

- **STEP S's second score (G44).** The whole kernel time a section rose 0.058 between two profiled reads taken one after the other. That is inside the spread a control showed here, so the rise is not resolved by that read. The entries stand, because they are far outside any drift: the clocks' launch went from 15.9 to 168.7 ms a section and the nine paced-skin entries fell from 385.2 to 270.6. S′ is therefore still the right step, and its profile runs as one hold: the parent, S′, the parent again.
- **The scan's cost with the carry on.** The 1.3894 over 188 sections and the first clean scan lap's 1,450,361 ms against the rate laps' 932,686 to 1,048,264 ms were read across hours. A cost of two fifths stands against a drift of a twentieth; its second digit does not.
- **G45** (STEP G's ratio) is read inside one hold with a repeated control, not against "a control the same hour".

## 6. G54, fixed and unread

**G54** (fixed 06:31 UTC; host only: the same split at `1/2` on three more sections of the same state, the lap's sections 384, 768 and 1152, and on the first section of the latest saved state of the rate line; the cosines between sections computed on the PC from the covector files, which stay there).

- (a) In each of the four new reads: quiet places 0.05 to 0.15 of the compared places; `cos(G_l, G_q)` −0.9 or under in the temper and −0.6 or under in `v`; `cos(G_q, G)` of the whole negative. Yes, 0.70.
- (b) Across the four sections of the one state (six pairs), whole covector: the quiet covectors of two sections have a cosine of 0.5 or more in every pair, and in every pair it is above the cosine of the two sections' loud covectors. Yes, 0.55.
- (c) The later state's first section reads within 0.03 of the earlier state's quiet share and its temper cosine within 0.05.

Basis: §3.5 holds on any section; the holding push pointed against the deposit at every depth of margin on the one section. Rule: (b) held, the holding push is one slow common mode and §4.4's law is derived when the quiet share is large; (b) missed, the push is each section's own, every place is visited, and the visit clock counted in news is closed for this field.

## 7. What does not follow, and the lessons checked

- It does not follow that the words' size is free at any size, or that the scan with the carry on costs nothing. The read resolves 2% at 1,072 octets with the carry off.
- It does not follow that the drift is the desktop's, or the host's: §5.4 is five points.
- §3.4 is one section of one state. It is said of the field only after G54.
- The lessons. *A ratio across two things that differ in more than the named factor* (this night's own: two counters under one name, then two hours under one binary): §5.5's rule is its repair. *Bits read as progress* and *a short reading choosing a law*: no law was chosen here on a timing; three guesses were scored as misses and the step they pointed to was not built. *An index of contexts counted as generation*: the visit clock of §4.4 addresses nothing by content; its slow variable is a covector with a balance and a port, and it is not built.

## 8. Owed, in order

1. G54's read (the host run is ordered; it does not overlap a hold of the card).
2. S′'s profile as one hold (parent, S′, parent), with each process's share of the card and the host sampled; then S′'s acceptance on a lap's bytes.
3. The quiet share at `1/2` as a line of each lap's held read (a count over faces the read already forms).
4. The ruler of §3.6 (the missed places' leading classes against the given places' truths), a host reading, after G54.
5. In #410: `p(u) = max_v p(v) ⇒ −ln p(u) ≤ H(p)`, beside the face's covectors.
6. The port of the training line to main is unchanged by this record: the words' size is not a debt of it.

## Receipts

- [`guess_capacity_44_54.txt`](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD_receipts/guess_capacity_44_54.txt): every guess of the night from G44 with its clock time, its read and its score.
- Runs on the PC (their logs are under `${HOLONICS_ROOT}/.local/` and are not published): `split-curve` (host; 611 s against 720 s), `acc-rate` (card; 214.2 s against 320 s), `acc-quad` (card; one hold, 867 s against 1,280 s; measured over projected 1.008). Device line: the RTX 4080 SUPER under `.local/gpu.lock` for the card reads, host time inside them 339 to 404 ms of regions over 274 sections; the host reading on eight threads at nice 10 under the reading manifest.
- The padded build's one change is seven unused 8-octet words at the end of the kernels' words on both sides, on a detached worktree of the rate build's commit, retired after the hold; it entered no line and no branch.
