# A coarse level's sites are its own ticks, carried across sections, so its heads reach across the passage's partition

Refs #404 #406. Status: [built on the host and the card and tested, parity at the race's declaration on the 4080 (§5); the measurement (acceptance 7) running; agent-inferred, October 29].
Claude (opus), design lead. The first of the October 28 expansions in the order fixed by
[the audit](2026-10-29_THE_CODEX_LEAD_OF_OCTOBER_27_AND_28_AUDITED_THE_THEORY_STAYS_THE_TEXT_SURFACES_ARE_WITHDRAWN_AND_PARTICIPATION_IS_NEXT.md#4-the-order-now):
the consumer of [the radix record §1](2026-10-29_A_VALUE_IS_A_RADIX_MOVE_THE_FREE_ENERGY_IS_THE_CODE_THAT_FOUNDS_AND_POLARITY_IS_THE_ONE_REVERSIBLE_NEGATION.md#1-a-value-is-a-radix-move-and-the-towers-modes-are-registers-in-their-own-radices)
(atlas `hnn.news-packet-participation`), which answers the item "the section" that
[the participation record §8](2026-10-28_ATTENTION_IS_THE_FIELDS_PARTICIPATION_THROUGH_ITS_OWN_TRANSPORT_SO_THE_PASSAGE_IS_TERRAIN_AND_THE_MODES_ARE_ITS_GEOMETRY.md#8-what-the-first-build-leaves-by-name)
left owed. Owners it joins: the news clock (`NewsClock`, the held step in `Tower::step`,
[record](2026-10-27_THE_LEVELS_TICK_ON_THEIR_OWN_NEWS_SO_THE_TOWER_LEARNS_ITS_ENCODING_ON_ITS_OWN_AXIS.md)),
participation (`hnn::tower::participation`, `LevelSites`, `Tower::reverse_joined`'s participation
return and transport covector), the stream state's text (`TowerState::to_text`), the growth
(`Tower::widen_state`) and the card (`kernels/tower.cu`, `TowerCard`).

## 1. What the participation race measured

[source-inspected; measured] Every level of the participating tower admits a site at every arrival
and closes its section after 128 sites, so every level's heads read the same 128 classes. At the
answers' opening of the race's laps 0 and 1 (RTX 4080 SUPER), level 0's heads weigh the last few
classes and levels 1 to 3 reach back at most 59 classes, their shares in steps of one head's whole
weight: each upper head sits on nearly one site. The coarse levels carry the longer memories (their
modes decay slower), but their participation reads the same section as level 0's, so a head with
a slow transport has nothing far back to reach. A lap took 929 to 1,241 s against the plain race's
113 s, the four levels' participation each reading 128 sites.

## 2. The law

[definition; agent-inferred] **A level's sites are its ticks.** Under the news clock, level `l` takes
its step `Δτ_l(t)` times at arrival `t` (the held step). Participation follows the same clock:

```text
Δτ_l(t) ≥ 1:   U ← U u_t^Δτ,   L ← L + Δτ (−log₂|λ_t|),   the input's charts admitted as a site,
               the probe reads every admitted site, the current y_l read and held
Δτ_l(t) = 0:   nothing moves: no site, no probe, y_l(t) = y_l(t−1)   (the zero-order hold)
```

The current is held as the modes are: an arrival that ticks no time moves nothing, so the level
presents the same state and the same current to its contacts. Level 0 ticks at every arrival, and
without a news clock every level does, so the present participation is this law with every
`Δτ = 1`, face for face.

**A level's section is its own.** It closes after `section` of that level's sites, releasing them
and resting its frames, so a level-`l` section spans `section` of the arrivals where `l` ticks (an
arrival that ticks twice admits one site and turns its frame twice). On the race's clock
(`B = 8`, `r = 2`) at its held-out 1.85 bits a class, level 1 ticks about every 4.3 classes, level 2
every 8.6 and level 3 every 17, so a section of 128 sites reaches about 550, 1,100 and 2,200 classes
(several GSM8K problems), where level 0's reaches 128. The partition is the passage's own news, so
the reach moves with the learning and nothing names a window.

**The sites are carried with the modes.** A level's open section is part of the stream's state
across the learner's sections, as its modes are (`LevelSites`, now with each level's own count and
its held current). A learner's section reverses from its opening, where the modes are constants;
the sites carried at the opening are constants with them, read by the section's probes and
receiving no covector, while the sites the section admits receive theirs. This is the same
truncation the modes already take at the opening, so carrying the sites adds no new cut. A held
cell's current covector joins its last tick's (and is dropped when that tick precedes the opening,
as the opening state's is). A level's section that closes inside a learner section parts the
section's transport sums at its close. The turn and met covectors of a move taken `Δτ` times count
it `Δτ` times.

**Not a store.** The carried sites are the open section's present terrain, released at its close
by the level's own count, exactly as the participation record's §4 reads them; nothing is written
to be looked up, and the address remains the transport.

**The order** [agent-inferred]. The radix record's consumer also gives a coarse site the packet
`x_P = Read(m_P)` as its input, in place of the held arrival. That is a change to the clocked
tower's own input (it changes the plain clocked tower, without participation), with its own
acceptance (the radix record's (a)–(c)), so it is built and measured after this one: this build
changes only participation's clock and section, so the measurement changes one thing.

## 3. Acceptance, fixed before the build

1. **Unchanged without a clock.** Every participation test passes unchanged; a participating
   tower without a news clock gives the same faces, covectors and text as before.
2. **Ticks.** On a clocked participating tower, each level's sites are exactly its ticked arrivals;
   at a no-tick arrival a level's state, frames, met dissipation and current equal its
   predecessor's; a level's section closes after `section` of its own sites.
3. **Carried sites.** A passage read across several learner sections gives the faces it gives read
   whole (the forward does not see the sections), and the states between sections carry the
   coarse levels' open sites.
4. **The covector.** On a small clocked participating tower, over a section whose opening carries
   sites at the coarse levels, the covector matches the code difference for participation's
   families and the moves, gates, pushes and reads below.
5. **Text and growth.** A state with carried sites and held currents restores whole from its text,
   and grows (`Tower::widen_state`) to the grown tower's faces.
6. **Card.** Parity at the race's declaration with the clock (`B = 8`, `r = 2`) on the race passage:
   every face, covector entry, learner and state equal, host against card; the `tower_pass` suite
   whole.
7. **The measurement.** The clocked participating race beside the participation race and a clocked
   race without participation (the held step, never yet raced), lap for lap on the race's passage,
   keys and declaration: bits by region, the writings whole, and each level's reach at the answers'
   opening.

## 4. The recorded failures these choices could repeat

- **An index of contexts counted as generation, a store**: the carried sites are the open
  section's terrain, released by count; no key is written to be looked up.
- **A design thought in the programming language (windows, offsets)**: the reach is the passage's
  own news partition, not a declared window.
- **A located cause carried unrepaired**: the participation record's §8 item "the section" is the
  cause measured in §1 (upper heads on one site); this build repairs it there.
- **An uncertified deposition step**: the certificate rereads the section with its carried sites.
- **Text on its codec's grain**: the clock counts the tower's own code in bits, for every medium.
- **Bits read as progress**: the writings and the reach are shown beside the bits.

## 5. Built

[source-inspected; tested] **The host** (`hnn::tower`):
- `LevelSites` carries each level's own count of open sites and its held `current`;
  `LevelSites::reopened` releases a closed section's sites and rests its frames, keeping the current.
- `Tower::step` admits a site only where the level's clock ticks, advances the frames and the met
  dissipation `Δτ` times, holds the current under a news clock (without one every level ticks at
  every arrival, so nothing is held), and closes each level's section at its own count.
- `Tower::reverse_joined` reads the sites carried at the opening as constants, joins a held
  cell's current covector to its last site's (dropped before the call's first site), parts the
  transport sums where a level's section closes, and counts each move's turn and met covectors
  `Δτ` times. The refusals of a reverse over carried sites and of a section longer than
  participation's are gone.
- `join_news` refuses after participation (the clock joins first); `admits_participation` admits
  a news clock. `TowerState::to_text` and `Tower::state_from_text` carry each level's count, frames,
  met dissipation and current; `Tower::widen_state` repeats the current with the modes.

Tests (`hnn::tower`, 116 of 116 with these):
- `a_clocked_levels_sites_are_its_ticks_and_its_current_is_held` (acceptance 2), on clocks of three
  bits (level 1 still at some arrivals) and one bit (two or three ticks at each);
- `a_clocked_participation_carries_its_sites_across_calls` (acceptances 1 and 3): three calls equal
  the passage read whole, and with participation's contacts closed the tower is the plain clocked
  tower face for face;
- `the_clocked_participation_covector_matches_the_code_difference_from_a_carried_opening`
  (acceptance 4): from an opening carrying both levels' sites, rectifying plain and turned and the
  pair contact on three bits, and rectifying plain and turned on one bit, 30 of 32, 36 of 36, 32 of
  32, 32 of 32 and 35 of 36 families read, every one within a tenth. A level still at a third of
  the arrivals reads fewer sites, so its covectors sit within a few times the reading's grain: the
  difference is read at the participation tests' step and at twice it, a parameter matching at
  either. At one step level 1's largest key covector, 5,040,148 at `2^(−32)`, read 6,957,096, and
  5,009,006 and 5,167,706 at twice and four times; at twice the step level 1's largest read
  covector, 16,971,702, read 20,063,011, and within a tenth at one.
- `a_clocked_states_text_restores_each_levels_sites_and_held_current` and the growth test on the
  clocked participating tower (acceptance 5).

[source-inspected; measured on the 4080] **The card** (`kernels/tower.cu`, `TowerCard`): the forward
keeps each level's carried count and members in the block (`pa_open` `[S][L]`, `pa_member`),
admits a site only at a tick, turns the frame `Δτ` times, reads the held current (`pa_hold`) at a
cell the level is still at, and closes each level's section within a call; the ends return each
level's section (`pa_sect`). `tower_reverse_participation` joins held cells' current covectors to
their sites, reads the carried sites as constants, marks the closes (`pa_mark`) where the transport
sums part, writes zero chart covectors at held cells and counts the transport `Δτ` times. The
refusals of participation beside a clock, of a read across a close and of a reverse over carried
sites are gone. Tests (`tower_pass`): the clocked participating pass for 32 sections, on the pair
contact with an uncompared place, unclocked sections of twelve over learner sections of nine,
the class-by-class advance, and a section read on across calls and closed within one (its
covector over carried sites the host's). `tower_pass parity … NEWS_BITS NEWS_RADIX participating`
runs the race's declaration; `train-two-ladder-news-participating-tower-classes` is the race's
command.

**Acceptance 6 on the 4080.** On the RTX 4080 SUPER at `16689828d` (B-PC, under the card lock),
the kernel compiled on the first build; `tower_pass` passed 39 of 39 in 23.9 s, the five tests
above among them. `tower_pass parity … 8 2 participating` at the race's declaration: 32 sections at
24 streams, 98,304 faces and 21,076,000 covector entries equal and every learner equal (host
52,717 ms, card 12,242 ms); 4 sections at 320 streams, 163,840 faces and 2,634,500 entries equal
(host 71,890 ms, card 12,219 ms; peak resident set 5.66 GB).

**A reading beside acceptance 7** [agent-inferred, from the unified-theory thread]: in
`participation_return`, `g_z = ln 2 · a ⊙ (g_a − ⟨a, g_a⟩)` vanishes on a head whose weights sit on
one site, so such a head's probe, key and friction charts learn nothing about where to look. Beside
the bits and the reach, the measurement reads each head's participation entropy in bits at the
answers' openings and the share of each head's covector reaching its score charts (probe, key,
friction) against its value chart, for the clocked and unclocked races.

[source-inspected; tested on tiny towers] **Built as one reading of a lap's rested learner**,
`read-tower-race STATE STATE_SHA DEV DEV_SHA PROMPTS PROMPTS_SHA STREAMS SECTION OUT` (host; its
codes are the card's by the parity), with the readings the radix record §§3–4 asks of the race:
- each head's entropy `−Σ a log₂ a` (`Participation::entropy`, on `2^(−20)` bits) at each prompt's
  opening, now also a column of every `PARTICIPATION.tsv` the release and the body write;
- over the held-out passage's opening, each head's mean entropy over its sites and the share of its
  chart covector reaching probe and key against value (`Tower::participation_shares`);
- each level's modes counted by friction octave, written as the memory each octave matches
  (`Tower::mode_octaves`, the octave the heads are founded on);
- the bridge `W₁ᵃ`'s size against the contacts' at each level (`Tower::participation_bridge`): it
  opens at zero, so its size is whether participation has founded its conduction there;
- the flux `I = L(what follows a prompt | another prompt) − L(it | its own prompt)` in bits for each
  of the race's prompts, the continuation being the classes after the prompt's first place in the
  held-out passage up to the next end letter (atlas `culture.question-answer-information`; the
  prompts are a first span, so their continuation is the next span of the same source, and the flux
  is what four kilobytes of context save on the next four).

Brandon asked on October 29 that a new design race for one hour first, read near 15, 30, 45 and 60
minutes, and run longer only when it is plainly improving; the two clocked races are declared so.

