# A clocked level's contacts hear the passing current at every arrival while its modes move on their own clock

Refs #404 #406. Status: [the measurement in §1; the law and its acceptance fixed before the build;
built on the host and the card, acceptances 1 to 3 met (§6); the race (4) failed its claim (§7);
the passage now joins only the levels a news clock holds, and the clock begins above the arrival
stack (§8), built on the host (acceptances 1 and 2), whose card parity and race are owed;
agent-inferred, October 29 and 30].
Claude (opus), design lead. Read beside
[the coarse level's sites](2026-10-29_A_COARSE_LEVELS_SITES_ARE_ITS_OWN_TICKS_CARRIED_ACROSS_SECTIONS_SO_ITS_HEADS_REACH_ACROSS_THE_PASSAGES_PARTITION.md)
(whose acceptance 7 is §1's measurement), [the news clock](2026-10-27_THE_LEVELS_TICK_ON_THEIR_OWN_NEWS_SO_THE_TOWER_LEARNS_ITS_ENCODING_ON_ITS_OWN_AXIS.md)
and [the radix record §1](2026-10-29_A_VALUE_IS_A_RADIX_MOVE_THE_FREE_ENERGY_IS_THE_CODE_THAT_FOUNDS_AND_POLARITY_IS_THE_ONE_REVERSIBLE_NEGATION.md#1-a-value-is-a-radix-move-and-the-towers-modes-are-registers-in-their-own-radices).
Owners it joins: `Tower::step` (the contacts' drive), `Tower::reverse_joined` (the contacts'
reverse), the layout and the tower's text, the card (`kernels/tower.cu`, `TowerCard`).

## 1. What the clocked races measured

[measured, RTX 4080 SUPER, October 29] Brandon asked that a new design race one hour first, read at
about 15, 30, 45 and 60 minutes, and run longer only once it is plainly improving. The clocked
tower (the news clock `B = 8`, `r = 2`, the held step) raced with and without participation from
22:33 UTC, the race's declaration otherwise unchanged (width 64, 128 modes, 256 contacts, four
levels, 320 streams, sections of 128, rate `2^(−7)`), beside the unclocked towers' laps (the participating
tower's from earlier the same day, the plain tower's from October 27). Held-out bits a byte:

| lap | plain | clocked plain | participating | clocked participating |
|---|---|---|---|---|
| 0 | 2.356 | 2.465 | 2.298 | 2.334 |
| 1 | 2.139 | 2.365 | 2.152 | 2.238 |
| 2 | 2.060 | 2.303 | | 2.192 |
| 3 | 2.020 | 2.265 | | 2.161 |

Both clocked races ran four laps in the hour (the plain one waited on the card between its laps
while the participating one held it). A plain lap takes about 114 s on the card in either clock; a
participating lap took 929 to 1,241 s unclocked and 738 to 841 s clocked. Both clocked races keep
improving, by smaller steps each lap (participating 0.096, 0.046, 0.031), and both stay behind the
unclocked towers at equal laps: the clocked plain tower's lap 3 (2.265) reads worse than the plain
tower's lap 1 (2.139). The clocked plain tower trails the plain tower by 0.23 at lap 1,
as the news race of October 27 trailed by 0.22 to 0.27 through its 21 laps under the first law,
and the held step (adopted then) has not closed it.

The readings of the participating race's laps 0 and 4 (atlas `tower.race-readings`): level 0's
heads spread over a few recent sites (0.1 to 2.3 bits), the upper levels' heads sit on one site
(0.004 to 0.09 bits) and sharpen from lap 0 to lap 4, while 75 to 100% of their chart covector
still reaches the charts that decide where they look, so the collapse is learned sharpening, not a
starved return. The bridge `W₁ᵃ` grew from about 0.45 to about 0.73 of the contacts' size on levels
1 to 3. On GSM8K another prompt's context costs the continuation 46 to 66 bits more than its own at
lap 0 and 141 to 147 at lap 4.

## 2. The located cause

[source-inspected] A level's contacts read only its modes' face: `a = W₁ r̂_l + b` (with `W₁ᵃ r̂ᵃ_l`
beside it under participation), `r̂_l` the normalized read of the level's state. Under the news
clock the state moves only on the level's ticks, so between ticks the level returns the same
current to the residual stream at every arrival. On the race's clock at about 2 bits a byte, level
1 ticks about every 4 classes, level 2 every 8 and level 3 every 16, so at most arrivals the face
reads the arriving class, level 0's fresh read and three constants, joined by the readout's sum.
Without the clock every level moves at every arrival and its contacts read a state the arrival has
just pushed, so the plain tower meets each class with four levels of contacts and the clocked one
with about one.

[agent-inferred] This is the clocked deficit's cause, not the coarse level's input. The packet law
(radix §1) changes what a coarse level hears at its ticks (its packet `m_P` instead of the fine
state `h_close`); it leaves the coarse contacts silent between ticks, so it is not built first.
The control that tests the inference: the plain tower with one level, raced two laps on the same
passage. If the clocked plain tower reads about as the one-level tower does, its upper levels add
little at the arrivals they do not tick.

[measured, RTX 4080 SUPER, October 29, at `1ec7c9dae`] The one-level tower (no clock, no
participation, the declaration otherwise the race's) reads 2.462 and 2.354 held out at laps 0 and 1,
against the clocked plain tower's 2.465 and 2.365: the clocked tower's three upper levels add 0.003
and −0.011. The one-level lap takes 49 s against 114 s for four levels. The race's readings agree:
the clocked plain tower's level 3 keeps its founded frictions (16 modes at each memory octave from
`2^1` to `2^8` classes) through lap 2 and moves one or two modes by lap 3, level 2 moves a few, and
only level 1 learns toward short memories as the unclocked levels do; under participation level 1
also keeps its founded frictions through lap 2. A coarse level whose contacts return a constant at
most arrivals hands its modes almost no covector, so its constitution barely moves. The passage
reaches that too: once the coarse contacts matter at every arrival, the covector their read `W₁ r̂`
returns to the modes grows with them.

## 3. The law

[definition; agent-inferred, October 29] **The contacts hear the passing current.** A level is two
objects on two clocks: its modes (parametron rings that store) move on the level's ticks; its
contacts (the helical pair contacts that conduct) meet the current that passes the level at every
arrival. The level's contact drive reads both the level's held face and the passing current
`x_l(t)`, the residual stream the level receives:

```text
a_l(t) = W₁ r̂_l(t) + W₁ˣ x_l(t) + b          (+ W₁ᵃ r̂ᵃ_l(t) under participation)
v_l(t) = max(a_l(t), 0)                        (or the pair law on a_l and its second drive)
x_(l+1)(t) = x_l(t) + W₂ v_l(t) + c
```

The contact is the meeting of two Holons: the level's held Holon, whose face stands between its
ticks, and the passing current. Reception changes both (THE_MACHINE, the receiver law); without
`W₁ˣ` the coarse receiver hears the passage only on its ticks and returns a constant between them,
a one-sided contact. With it the coarse level conditions every arrival on its held context, and the
fine current on the coarse one, while its modes keep the plain passive step on their own clock (the
news clock's law is unchanged, and so is its certificate). The join opens at zero, so joining it
moves no face; it is read as the gate already reads its input (`W x` on `2^(−40)` released to the
drive's `2^(−16)`). Every level carries it: at level 0 and in the unclocked tower the contacts
already read a state the arrival pushed, and the join adds the arrival's direct path there.

**The reverse.** `g_(W₁ˣ) = Σ_t δa_l(t) x_l(t)ᵀ`, and the input's covector gains `W₁ˣᵀ δa_l(t)`,
beside its covectors through the push, the gate and the charts. The modes' scan is unchanged.

## 4. Acceptance, fixed before the build

1. **Opens at zero.** A tower with the join at zero reads every passage face for face as the tower
   without it, clocked and unclocked, with and without participation.
2. **The covector.** `W₁ˣ`'s covector and the input's through it match the code difference on a
   small clocked tower (two levels gated, the news clock's test pattern), each family within a
   tenth where it stands above the reading's grain.
3. **The card.** Parity at the race's declaration with the join, clocked: every face and covector
   entry equal, host against card (RTX 4080 SUPER).
4. **The race.** One hour on the card, the clocked tower with the join beside the clocked plain
   tower, read at about 15, 30, 45 and 60 minutes with the writings whole. The claim: it reads no
   worse than the unclocked plain tower held out at its laps 1 and 3 (2.139 at lap 1, 2.020 at lap
   3, measured October 27 on the same declaration). Short of
   that, the located cause is not the whole cause, and the next loop works on the remainder.

## 5. The recorded failures these choices could repeat

- *A located cause carried unrepaired into a new consumer*: the clocked deficit has stood since
  October 27; participation was built on the clocked tower before it was repaired. This repairs it
  before the packets consume the clock.
- *A design thought in the programming language*: the join is stated as the contact meeting the
  passing current, the level's two clocks as the modes' and the contacts'.
- *Text as the exception*: nothing here reads a class, a boundary or a modality; the passing current
  is whatever the codec encoded.
- *Bits read as progress*: the race reports bits beside the writings, and the claim is a fixed
  comparison, not a trend.
- *A refusal answered with a larger limit*: the race keeps its declaration, its lap rule and its
  hour.

## 6. Built (October 29)

**Host.** `Tower::join_passage` (and `TowerLearner::join_passage`, its moments at zero) appends each
level's `W₁ˣ` (`F × d`, the material's grain) after every other part's material, so it joins last;
the pair face, ring face, rotor, mutual contact, participation and strands refuse to join after
it, and the passage refuses a ring face, a rotor or strands beside it (their contacts' lifts read
the contacts' rows by their own laws). `Tower::step` adds `W₁ˣ x_l` to the drive, released on its
own as participation's `W₁ᵃ` part is; `Tower::reverse_joined` sums `δa x_lᵀ` into `W₁ˣ`'s covector
and returns `W₁ˣᵀ δa` to the level's input after the return's material has read the level's output
covector. The tower's text adds a line `passage`; the growth splits `W₁ˣ` as it splits the
contacts. Tests: `the_passage_opens_at_zero_and_restores_exactly` (acceptance 1: face, state and
drive equal at every cell, clocked and unclocked, with and without participation under both
contact laws; the text and the learner's restore whole; a second passage and a later
participation are refused), `a_clocked_levels_contacts_hear_the_passing_current_between_its_ticks`
(without the passage level 2's drive equals its predecessor's at every arrival it does not tick;
with it the state is held and the drive moves), and acceptance 2:
`the_passage_covector_matches_the_code_difference` (at zero, clocked),
`the_opened_clocked_passage_covector_matches_the_code_difference` and
`the_opened_passage_covector_matches_the_code_difference` (opened from the keys, clocked and
unclocked, over the first 31 classes of the news passage; on the 13-class passage the opened
unclocked tower reads 20 of its 29 families above the grain, three short of the fixture's
three-quarters, none off). `bash tools/gate.sh`: 22 of 22.

**Card.** `kernels/tower.cu` reads `W₁ˣ` transposed in the forward (`tower_forward`, the drive's
part beside `W₁ᵃ`'s) and returns `W₁ˣᵀ δa` to the input covector in `tower_reverse_contacts`, after
the level's output covector is kept for the return's material; `TowerCard::outer_families` sums
`δa x_lᵀ`. The law words carry the family, its reach and the flag. [measured, RTX 4080 SUPER] At
`cf459c4e8` the card's 39 tests passed, but the first parity was refused before any section: the
frame sized its list of transposed families without the passage (a write of 99 words into 87, the
missing 12 being one `W₁ˣ` family on each of four levels), and no card test joined the passage.
The frame's shape now carries the passage, and two card tests join it, opened off the keys:
`the_cards_clocked_passage_is_the_hosts_for_thirty_two_sections` (clocked and unclocked) and
`the_cards_clocked_participating_passage_on_the_pair_contact_holds_an_uncompared_place_as_the_host_does`
(beside clocked participation on the pair contact and advanced class by class under the clock).
[measured, RTX 4080 SUPER, at `25710373a`] The card's 41 tests pass, and the parity at the race's
declaration is equal (acceptance 3): every face, covector entry and learner equal over 32 sections
at 24 streams clocked (98,304 faces, 12,685,344 covector entries), over 4 sections at 320 streams
clocked (163,840 faces, 1,585,668 entries) and over 32 sections at 24 streams unclocked. The race commands are `train-two-ladder-passage-tower-classes`
and `train-two-ladder-news-passage-tower-classes`; `tower_pass parity … passage` joins it.

## 7. The race (October 30)

[measured, RTX 4080 SUPER, at `25710373a`] The clocked tower with the passage (A) and the
unclocked tower with it (B) raced together from 00:07 UTC, each lap waiting on the other's for the
card; both stopped by the window rule after lap 9 (a game held about 2 GiB of the card through
lap 9, so its times are contaminated and its bits are not). The unclocked plain tower was raced
again at the merged commit `53cff3ff6` for four laps and reproduced October 27's laps 2 and 3 code
for code, so the reference stands. Held-out bits a byte:

| lap | plain | B (unclocked, passage) | clocked plain | A (clocked, passage) |
|---|---|---|---|---|
| 0 | 2.356 | 2.327 | 2.465 | 2.448 |
| 1 | 2.139 | 2.168 | 2.365 | 2.338 |
| 2 | 2.060 | 2.104 | 2.303 | 2.279 |
| 3 | 2.020 | 2.054 | 2.265 | 2.239 |
| 5 | 1.970 | 2.002 | | 2.202 |
| 9 | | 1.965 | | 2.161 |

A passage lap took about 127 s on the card against 114 s plain. At lap 9 A read 2.187 on GSM8K
and B 1.934.

**Acceptance 4 fails.** A reads 2.338 and 2.239 at laps 1 and 3 against the plain tower's 2.139
and 2.020: the passage closes about 0.03 of the clocked tower's 0.2-bit deficit. The located cause
is real but not the whole cause. In the unclocked tower the passage costs about 0.03 at every lap.

**What the readings show** (A's and B's lap 9 states, read on the card). With the passage the
clocked coarse levels learn: level 1's modes all left their founded spread for the reading's
shortest octaves (`2^0` to `2^5`), and levels 2 and 3 moved most of their modes toward short memories, where without it level
3 had kept its founding through lap 2. The clocked tower uses context as the unclocked one does:
on GSM8K another prompt's context costs A's continuation 90 to 138 bits and B's 117 to 132. So the
coarse levels learn and are read; what A lacks is the depth the arrival levels give each arrival.
A level that ticks at every arrival runs its recurrence on the arrival's own input, and the plain
tower runs four of them per arrival; the clocked tower runs one, with three held faces read
through contacts.

## 8. The next loop: the clock begins above the arrival stack

[definition; agent-inferred, October 30] **The clock begins above the arrival stack.** The levels
below a clock's first clocked level `F` tick at every arrival; level `l ≥ F` ticks at the
sections `B r^(l−F)`. `F = 1` is the clock of October 27. A clocked level then adds coarse reach
above the depth the arrival levels give each arrival, instead of replacing it. **The passage
joins only the levels the clock holds** (`l ≥ F`): there the contacts would otherwise return a
constant between ticks (§2); at a level that ticks at every arrival the contacts already meet the
arrival through the state it pushed, and there the join cost the tower (§7). The passage is
refused without a clock.

**Acceptance (fixed before the build).**

1. A clock from level `F` on four levels: levels below `F` tick at every arrival and read face for
   face as the unclocked tower's; the levels from `F` tick at `B r^(l−F)` on their own news; the
   text writes `F` and restores whole; a clock above the top level is the tower without it, as
   one level on a clock is, and the passage is refused there.
2. The passage joins only levels `l ≥ F`, opens at zero and its covector matches the code
   difference on three levels clocked from level 2.
3. Card parity at the race's declaration, six levels clocked from level 4 with the passage.
4. **The race.** One hour on the card: six levels, the clock (`B = 8`, `r = 2`) from level 4
   with the passage on levels 4 and 5 (C, `train-two-ladder-stacked-news-passage-tower-classes`),
   beside the plain tower of six levels (E). The claim: C reads no worse held out than E at laps 1
   and 3. Short of that, at this declaration a clocked level is worth less than an arrival level,
   and the clock's place is the participation's reach (radix record §1), not the bits.

**Built on the host** (`NewsClock::above`, `Tower::hears`; the card's law word `news_first`).
Acceptance 1 is `the_clock_begins_above_the_arrival_stack`. Acceptance 2 is
`the_passage_covector_matches_the_code_difference` and its two opened siblings, read at steps of
`2^(−9)` units. Two properties of the fixture surfaced there, neither a fault of the reverse:

- At the first cell a clocked level has not ticked: its state rests and the tiny tower's contact
  biases are zero, so its four drives sit exactly on the rectifier's kink, and every step of a
  passage at zero, from `2^(−9)` to `2^(−14)` units, carries them across. The passage at zero is
  read with the heard level's contact biases opened.
- With the passage on clocked levels only, the fitted slope's error grows as the step shrinks:
  12%, 35% and 62% at `2^(−10)`, `2^(−11)` and `2^(−12)` units on one family whose covector stays
  110.6, and within a tenth at `2^(−8)` and `2^(−9)`. That is the forward's rounding to `2^(−16)`,
  not a covector off by a constant.

**Six levels on the card.** The race's six levels met two walls before any card work. The founding
reads 1,245,440 key bytes at six levels (852,224 at four) and the race's key file held 1,048,576;
the race's keys are now the same rule counted to `2^16` (2,097,152 bytes, whose first 1,048,576
are the old file, so a four-level tower founds the same on either). And the card's law carried its
levels' words in place, in the kernel's parameter words: 2,256 octets of law and 1,088 of frame at
four levels, 424 more a level, against the 4,096-octet parameter space, so it refused a fifth.
Each level's words (with its section, which the law held beside them) are now resident on the
card, addressed from the law, and the forward carves its per-level ticks, open sites and swell
from its shared memory by the declared levels: the card carries any number of levels. Its parity
at six levels is `the_cards_clocked_passage_is_the_hosts_for_thirty_two_sections`' third case.

The recorded failures these choices could repeat: *a located cause carried unrepaired into a new
consumer* (the passage at the arrival levels is retired before the stacked clock consumes it);
*bits read as progress* (the claim is a fixed comparison at two laps, with the writings beside it);
*a refusal answered with a larger limit* (the window rule stopped A and B at lap 9 and neither was
relaunched).

