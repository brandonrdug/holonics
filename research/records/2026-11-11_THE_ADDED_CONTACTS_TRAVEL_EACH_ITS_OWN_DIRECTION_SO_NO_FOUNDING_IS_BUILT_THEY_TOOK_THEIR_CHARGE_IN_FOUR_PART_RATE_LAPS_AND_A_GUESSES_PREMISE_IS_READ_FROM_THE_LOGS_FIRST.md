# The added contacts travel each its own direction, so no founding is built; they took their charge in four part-rate laps, and a guess's premise is read from the logs first

Status (2026-11-11, 09:45 UTC): one reading scored and one sentence added to both guides. The question was whether a pair contact founded from the deposit's own second-order structure would gain much more than a drawn one. Its first design, a section's pair tensor, was sized against the contacts' own travel and withdrawn before any order (§2). Its second form is a host ruler on saved states, the rank of the new contacts' travel (§3). The guess G57 was fixed before the read; three of its four parts missed and the control held (§4). By the guess's own rule the outcome is spread: each of the 32 added contacts travels its own direction, in its column and in its rows, so no founding is built on this line (§5, §6). Two of the misses guessed a travel whose end the record of the day before had already printed, and the guides now say that a guess's premise is read from the logs before the guess is fixed (§7). Refs #73, #405.

The guess was fixed with its clock time before its read; the file is in the receipts. Machine numbers are integers of the saved states; ratios are theirs, released to the digits shown.

## 1. The objects

- **The field's pair contacts** ([`tower.field-growth-by-contacts`](../../docs/atlas/objects.tsv)): at a site with state `s` and strand mate's state `x`, contact `e` forms `c_e = (a_eᵀs)(b_eᵀx)`, complex over `f/2` pairs of real rows, and the face receives `W c`. The contacts are a sum of `f` products of three factors: a return direction `W[:, e]` on the face and two drives `a_e`, `b_e`.
- **The pair tensor of a passage**, `T[d, i, j] = Σ_t δx_t[d] s_t[i] x_t[j]`, with `δx_t` the face's covector at place `t`: the coholon that reaches the whole bilinear map from a site and its mate to the face. Every contact's covectors are contractions of it: `∂W[:, e] = T(·, a_e, b_e)`, `∂a_e = T(W_e, ·, b_e)`, `∂b_e = T(W_e, a_e, ·)`. A contact that opens with its column at zero and its rows drawn first moves its column along `T(·, a_e, b_e)`, and its rows move once the column stands.
- **A founding from the deposit** would open a new contact on a component `(v, a, b)` of `T` in place of drawn rows ([`code.rank-one-founding`](../../docs/atlas/objects.tsv), [`hnn.pair-contact-split`](../../docs/atlas/objects.tsv), [`tower.pair-contact-founded-split`](../../docs/atlas/objects.tsv)). It gains over a draw where `T`'s consistent part holds a few components much longer than the rest: drawn contacts are then all driven along the same few return directions and repeat each other, and a founding spreads them over the components.
- **The consumer**, as an equation at the growth law: with `D` the matrix of the new contacts' travel over a lap (one column a contact), founding is worth building where `D`'s columns share a subspace of a few directions lap after lap, and it has nothing to choose where each column keeps its own.

## 2. Why one section's tensor is not the reading

[derivation, 09:15 UTC, before any order] The first design accumulated `T` in the host return on four sections of the seventh part-rate state. The contacts' own travel sizes it. By the contact test of November 10 the learner moved an entry of the new contacts by 0.02 (the new columns) to 0.05 (the new rows) of its largest step a section, and the step is the covector's first moment over the root of its second ([`tower.field-deposit`](../../docs/atlas/objects.tsv)). So on a drawn contact the consistent share of a section's squared covector is `s² = 0.0004` to `0.0025`. Four sections hold 0.0016 to 0.01. A component is told from noise only past `K` sections with `K s²` above the noise's first share, which is 0.02 for even noise of 64 by 4,096 entries and more where the states share a mean: 8 to about 600 sections, times the count of components. A four-section tensor reads noise.

A lap has already summed 1,535 sections of exactly this drift, entry by entry, in the new contacts' travel. The saved states hold it.

## 3. The ruler

`tools/state_travel.py rank CONTACTS_BEFORE STATE STATE ...` opens saved states read-only on the host and prints, for the columns of `W` and the rows of `a` and `b`, the new contacts and the old (the control):

- the form's and each lap's travel's participation ratio `pr = (Σσ²)² / Σσ⁴` over the singular values, with the first and the first four shares;
- for each pair of successive laps the cosine of the two travels and `f_r`, the share of the later lap's squared length inside the first `r` left singular directions of the earlier lap's. A drawn subspace holds `r/64`.

Three controls on drawn states run in gate 1 (`tools/test_state_travel.py`: one shared direction, each its own direction, wander). The calibration on drawn travel of known shape ([`travel_rank_model.py`](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD_receipts/travel_rank_model.py); 64 by 32, 40 draws) reads, at a lap cosine `c` of one half:

| common travel's participation ratio | 1 | 2 | 4 | 8 | 16 | 32 |
|---|---|---|---|---|---|---|
| `f₁ / c` | 0.98 | 0.65 | 0.38 | 0.20 | 0.10 | 0.04 |
| `f₄ / c` | 1.03 | 0.95 | 0.81 | 0.57 | 0.33 | 0.16 |

Two facts bound the reading. Thirty-two columns that each travel a drawn direction of their own have a participation ratio of about `64·32/(64+32) = 21`, so 21 is the far end of the scale and not 32. And the step divides each entry by the root of its own second moment; the sign pattern of a rank-one drift is rank one, so a gathered drift stays gathered through the step and the ruler reads it.

It is a ruler in the guide's sense: it measures what the machine's states hold, it leaves their bytes the same, and it is no part of the machine.

## 4. The read, and G57 scored

[measurement, 09:26 UTC; host arithmetic on the PC, one process, no card, no build; the growth line's five states in 0.10 s and the part-rate line's nine states in 0.16 s; no state missing; the ruler's controls passed there first] The growth from 32 to 64 real contacts (16 complex pairs added) on the lane field: the grown state and its four laps, then the fourth to the twelfth part-rate laps.

**The new contacts on the growth laps** (three pairs of successive laps):

| family | cosine | `f₁ / c` | `f₄ / c` | participation ratio by the calibration |
|---|---|---|---|---|
| `W`'s new columns | 0.657, 0.581, 0.516 | 0.066, 0.103, 0.105 | 0.225, 0.338, 0.306 | 16 to 20 |
| new `a` rows | 0.619, 0.821, 0.834 | 0.024, 0.101, 0.104 | 0.310, 0.335, 0.313 | about 16 |
| new `b` rows | 0.612, 0.820, 0.834 | 0.056, 0.116, 0.118 | 0.314, 0.333, 0.343 | about 16 |

A lap's travel of the new columns reads a participation ratio of 20.1, 19.8, 19.1 and 17.6 over the four laps, at the drawn figure of 21.

**The new contacts on the part-rate laps** (seven pairs): the columns' cosines read −0.061, +0.072, +0.025, −0.011, −0.034, −0.039, −0.081 (mean −0.018) and their `f₄` 0.085 in the mean, where the old columns read 0.082 and a drawn subspace holds 0.0625. The new `a` and `b` rows read +0.053 and +0.072 in the mean. Successive laps do not agree: there is no common travel on these laps to take a rank of.

**The charge**, the new columns' rms over the old columns' (3.98M to 4.03M on the material's grain):

| state | grown | growth laps 1 to 4 | part-rate lap 4 | laps 5 to 12 |
|---|---|---|---|---|
| charge | 0 | 0.0318, 0.0566, 0.0784, 0.0960 | 0.4245 | 0.4368, 0.4416, 0.4480, 0.4534, 0.4582, 0.4625, 0.4665, 0.4712 |

| G57 | Guessed | Read | Score |
|---|---|---|---|
| (a) `W`'s new columns on the part-rate laps: common travel's participation ratio | 8 (5 to 13); `f₄/c` 0.40 to 0.75 | no common travel there (cosine −0.018); on the growth laps 16 to 20, `f₄/c` 0.29 in the mean | missed |
| (b) the new rows on the growth laps | 5 (3 to 8); `f₁/c` 0.20 to 0.50 | about 16; `f₁/c` 0.02 to 0.12 | missed |
| (c) control, the old contacts: cosines within 0.2 of zero, `f₄` under 0.15 | | `f₄` 0.114 at most over 30 pairs; 28 of 30 cosines inside, the old `a` rows −0.201 and −0.216 on the last two pairs | held |
| (d) the charge at the twelfth part-rate lap | 0.18 (0.12 to 0.27) | 0.4712 | missed |

By the rule fixed with the guess, the outcome is **spread** (`f₄/c` at or under 0.33 on `W`'s new columns; the three pairs' mean is 0.29 and one pair reads 0.338).

## 5. What the read says

1. *Each added contact travels its own direction.* In the columns and in both rows the common travel fills 16 to 20 of the 21 that independent directions would fill. The pair tensor's consistent part, as contacts drawn at this scale meet it, has no few components that stand above the rest in any of its three slots. A drawn contact lands on its own mix of them and travels there by its own covectors, which is one alternating step on the tensor a section.
2. *The contacts took their charge in the first four part-rate laps.* The columns stood at 0.096 of the old columns' length after four laps at the base rate and at 0.42 after four more laps at the contact parts' own rates (which opened three octaves above the base, rose one and stepped down as the parts' cosines fell; the founded-parts record of November 10, §3). They have gained 0.005 to 0.012 a lap since, to 0.47.
3. *Since then they lengthen along themselves and wander across.* On the part-rate laps a lap's travel of the new columns has a cosine of +0.16 to +0.25 with the form it left (0.19 in the mean; the old columns read +0.03 to +0.05), while two successive laps' travels read −0.018. Two travels that each hold 0.19 along one fixed form would agree at +0.04 through it, so across the form they oppose, which is the sign of rest in [`deposition.lap-cosine-drift-over-noise`](../../docs/atlas/objects.tsv).
4. *The mature columns are gathered and the new ones are gathering slowly.* The old columns' form reads a participation ratio of 11.4 to 11.8. The new columns' reads 20.1 after one growth lap, 19.2 after four, 17.8 at the fourth part-rate lap and 17.0 at the twelfth: about 0.1 a lap.
5. *The rows open with a transient.* Their first growth lap is small and gathered (`a`: rms 68k, participation ratio 7.3, first share 0.32; `b`: 75k, 3.5, 0.52) and the second lap does not continue it (`f₁` 0.015 and 0.034 at a chance of 0.016). `agent-inferred`, unverified: an entry opens at its first nonzero covector with first moment `g` and second `g²`, so its first step is a whole step in the covector's sign, and while the columns stand near zero the rows' first covectors share one pattern.
6. *The old contacts' cosines fall lap by lap.* The old `a` rows read −0.058, −0.041, −0.087, −0.143, −0.157, −0.201, −0.216 over the seven pairs (the old `b` rows +0.086 to −0.098, the old columns +0.173 to −0.087). By the cosine law a part at rest reads minus half its rate times its curvature, so these entries' rate is above what rest asks. The old contacts' rows here include the second lane's columns of `a` and `b`, which the founded-parts record already read at −0.16 to −0.30 and −0.04 to −0.24 at the floor; which entries carry the sign is unread by this ruler.

## 6. What follows for the machine, and what does not

- **No founding is built on this line.** A founding chooses among components; the read shows nothing gathered to choose. What a founding would have saved is the opening's travel, about four laps at the base rate and at most four at the parts' rates, which this growth has already spent. A later growth opens its contacts at the contact parts' rates from its first lap ([`tower.field-part-rates`](../../docs/atlas/objects.tsv)), which is the saving at no build.
- **The order goes to the row stride** (step A in THE_REBUILD's order within step 8), after the training line is `main`'s field, and the release stays read each lap.
- **What the grown contacts are worth at their charge is unread.** The growth record's control arm ends at the fourth growth lap (a gain of 0.0133 nats a place at a charge of 0.096); there is no 32-contact arm beside the part-rate laps. A ruler reads an upper bound without a lap: the held joint on a state a tool wrote with the new columns at zero, read-only, no lap training from it. At rest the first-order term of that difference is the columns' own covector, which is zero, so the difference is the second-order worth. It decides on the low side only (the old entries have moved beside the new ones). Its guess is fixed when it is ordered.
- **A part at rest above its best rate has no lower octave.** The part rule's octaves stop at the learner's rate. Finding 6 and the founded-parts record's lane columns both ask for less. A floor below the base rate is a change of the law and enters the line by reproducing its lap; it is not ordered before the reading of what a lap cosine counts (G59, §8) is in.
- *What does not follow.* That pair structure is absent: the contacts charged, so the tensor's consistent part is there; it is spread. That contact count is no lever: unread, above. Anything about reach: `T` is taken at a site and its adjacent strand mate, and what lies three and four letters back does not enter it. `agent-inferred`: a residual spread over many weak directions at this reach is served by reach along the strand before it is served by more products at the same reach; the open transmission by letter (0.57, 0.46, 0.17, 0.03 against the text's 0.77, 0.81, 0.48, 0.20) says the same, and the scan line and the row stride are already aimed there.

## 7. What was wrong in my basis, and the guides' sentence

Parts (a) and (d) guessed a travel on the part-rate laps. The founded-parts record of November 10 had printed its end: the three contact parts' cosines fell from 0.51 to 0.53 to about zero, their rates stepped down, and the new columns read 0 with a spread of 0.07 by the eleventh lap. The charge after the growth laps that the guess quotes as 0.068 was a figure of memory on another measure; this ruler reads 0.096. Part (b) reasoned that a row's travel is weighted by its own column and is therefore more gathered; the columns are spread, so the weighting gathers nothing. The spectrum behind (a), from the classes' counts, describes a return under one common mode, and the pair residual has none.

The guess still did its work: the rule was fixed before the read and the read fell on one side of it. What it wasted was one part of four on a question the logs had answered.

Both guides gain a sentence in "Theory picks, and a run tests a stated prediction": before a guess is fixed, what the logs and records already print about its premise is read. Reason: a guess on a premise a log has settled tests the guesser's memory, and its miss carries no information about the law.

*Lessons checked.* An authored routine standing in for learning: the ruler is host arithmetic on saved states and enters no law. Bits read as progress: no code is read here. A design thought in the programming language: the tensor is the pair contact's coholon and its contractions, stated on the objects before any array. A refusal answered with a larger limit: the thin tensor was answered with the lap's own sum, a different reading, and no count was raised.

## 8. Owed, in order

1. What a lap cosine counts. The trend line's rise was read from the logs at 09:47 UTC (G58, scored in the guess file: the trend line's code is higher on the sections it trains as well, by 0.0022 and 0.0048 nats a site at its first two laps, so the faster rates cost as spread; my guess, a fit to the passage, missed). The parts that rule raised furthest write a lane's face, whose scale every read divides out. G59 asked whether their steady travel is along that scale and was read at 09:55 UTC with `tools/state_travel.py scale` (scored in the guess file at 10:10 UTC; it missed): the travel is across those parts, the lane's writes and its lift lengthen together, and what the ruler shows instead is that the second lane and the added contacts' columns are still charging along themselves, 1.2 to 2 percent a lap. A lap cosine reads only the travel that survives a lap, never the spread a rate costs inside it. G60 (fixed 10:12 UTC, unread) reads from the logs how fast that spread sets in within a fast lap and whether the code then falls under it, before any card lap is spent on a cooling test. These two readings get a record of their own when G60 is scored.
2. The row stride on `main` (G42).
3. The charge's worth by the zeroed-columns ruler, with its guess fixed first.
4. Which entries of the old contacts' rows carry the falling cosine (the ruler's rows split by lane), before any floor below the base rate is derived.

## Receipts

- [`travel_rank_growth_extract.txt`](2026-11-11_THE_ADDED_CONTACTS_TRAVEL_EACH_ITS_OWN_DIRECTION_SO_NO_FOUNDING_IS_BUILT_THEY_TOOK_THEIR_CHARGE_IN_FOUR_PART_RATE_LAPS_AND_A_GUESSES_PREMISE_IS_READ_FROM_THE_LOGS_FIRST_receipts/travel_rank_growth_extract.txt) and [`travel_rank_rate_extract.txt`](2026-11-11_THE_ADDED_CONTACTS_TRAVEL_EACH_ITS_OWN_DIRECTION_SO_NO_FOUNDING_IS_BUILT_THEY_TOOK_THEIR_CHARGE_IN_FOUR_PART_RATE_LAPS_AND_A_GUESSES_PREMISE_IS_READ_FROM_THE_LOGS_FIRST_receipts/travel_rank_rate_extract.txt): the ruler's lines for `W`'s form, every lap and every pair of laps on the two lines. The whole outputs stay on the PC (their digests begin `2194fb6e` and `d9e0f99d`).
- [`travel_rank_score.py`](2026-11-11_THE_ADDED_CONTACTS_TRAVEL_EACH_ITS_OWN_DIRECTION_SO_NO_FOUNDING_IS_BUILT_THEY_TOOK_THEIR_CHARGE_IN_FOUR_PART_RATE_LAPS_AND_A_GUESSES_PREMISE_IS_READ_FROM_THE_LOGS_FIRST_receipts/travel_rank_score.py): the charge by state, each lap's cosine with the form it left (from the three rms figures), and the ratios of §4, from the two extracts.
- [`guess_capacity_44_55.txt`](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD_receipts/guess_capacity_44_55.txt): G57 as fixed at 09:20 UTC with its sizing, and its score.
- Device line: host only, one process, under a second; no card time, no lap waited. The states stay on the PC under `${HOLONICS_ROOT}/.local/`.
