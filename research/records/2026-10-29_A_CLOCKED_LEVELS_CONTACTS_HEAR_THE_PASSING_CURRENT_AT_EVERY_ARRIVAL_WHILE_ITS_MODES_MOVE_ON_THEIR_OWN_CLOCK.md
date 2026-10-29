# A clocked level's contacts hear the passing current at every arrival while its modes move on their own clock

Refs #404 #406. Status: [the measurement in §1; the law and its acceptance fixed before the build;
built on the host and the card, acceptances 1 and 2 on the host (§6); card parity (3) and the race
(4) owed; agent-inferred, October 29].
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
levels, 320 streams, sections of 128, rate `2^(−7)`), beside the unclocked towers' laps from
earlier the same day. Held-out bits a byte:

| lap | plain | clocked plain | participating | clocked participating |
|---|---|---|---|---|
| 0 | 2.356 | 2.465 | 2.298 | 2.334 |
| 1 | 2.139 | 2.365 | 2.152 | 2.238 |
| 2 | | 2.303 | | 2.192 |
| 3 | | 2.265 | | 2.161 |

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
   worse than the unclocked plain tower held out at its laps 1 and 3 (2.139 at lap 1). Short of
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
`δa x_lᵀ`. The law words carry the family, its reach and the flag. Parity at the race's
declaration is owed (acceptance 3). The race commands are `train-two-ladder-passage-tower-classes`
and `train-two-ladder-news-passage-tower-classes`; `tower_pass parity … passage` joins it.
