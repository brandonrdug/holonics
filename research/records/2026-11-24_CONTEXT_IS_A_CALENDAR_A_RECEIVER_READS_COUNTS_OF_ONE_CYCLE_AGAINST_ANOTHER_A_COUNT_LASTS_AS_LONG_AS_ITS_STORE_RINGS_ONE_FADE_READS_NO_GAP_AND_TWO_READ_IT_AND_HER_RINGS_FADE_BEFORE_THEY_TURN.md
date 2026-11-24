# Context is a calendar: a receiver reads counts of one cycle against another, a count lasts as long as its store rings, one fade reads no gap and two read it, and her rings fade before they turn

November 24, 2026, 19:12 to 20:10 UTC, the formal thread, in a cloud container with the PC's run logs read through a link (reads
only). Refs #404, #405, #410. Receipts: [`receipts/2026-11-24_calendar/`](receipts/2026-11-24_calendar/) (`GUESS.txt`). It follows
[the day's record of a lap's cycle](2026-11-24_A_LAPS_CARD_TIME_WAS_ITS_READS_THE_HELD_READ_RAN_ONE_FORWARD_FOUR_TIMES_A_ONE_SIDED_REGION_CONTINUES_BY_A_SITE_AND_A_READ_IS_SIZED_BY_THE_SCATTER_BETWEEN_LAPS.md),
whose §6 was corrected at 18:33 UTC: what she holds of an exchange is the state of her stores, never laid-out text. This record
says what those stores have to be.

## 1. The lens

Brandon, 19:12 UTC, read in his own message and given here as a lens in this record's words. What her engine holds as context
belongs to the complex Euler and Navier–Stokes picture of a fabric in motion, with the discrete as a sampling of what continues
(nothing here assumes a continuum; a description continues where its readings converge and fit). The overture and the comma belong
to it, and so do play and musical composition, which is as good a ground for context as arithmetic is for deterministic logic:
the parts of a song or a story have a structure and a stability, and they screw into each other as a key into a lock. Binding and
catalysis are of this kind too, and what the Hodge work calls an edge between two cycles is likely a winding of each about the
other. The centre of it is timing: computation and logic are timings, and a context whose timings do not distribute is no context.
What is wanted resembles a sliding window and is not one: knots under tension that reconfigure, with natures that flex from one
setting to another, and nothing like a table of keys and values. A sense of time comes only through comparison. People took the
stars to navigate and to attain units that integrate finely and relate to each other (days, years, hours, seconds), and a smaller
grain of time is never attained from a larger one's motion, or a larger from a smaller, without winding up or down. A count kept
in the head (a word of known length said over) drifts, and the drift is felt as it accrues. A person shut in the dark with nothing
to compare against does not keep time. A reader of text with a stamp beside each message does not gauge the gap between messages
either, so a window of text is not sufficient for these dynamics, and a stamp added to it is not sufficient either.

His exposition of units of time as windings is in the tree since August:
[the record of August 21](2026-08-21_THE_UNIT_IS_A_DECLARED_WINDING_THE_CERTIFICATE_IS_A_REALIZER_AND_THE_RADIX_IS_RESONANT.md)
(a unit of time is a declared closed winding and every duration a ratio of winding counts; the solar winding, the pendulum, the
quartz fork at `2¹⁵` a second, the hyperfine line; the equation of time a retained remainder; a clock a thermodynamic engine, with
no legible time where nothing is dissipated) and
[the record of September 25](2026-09-25_SEASONS_ARE_ROTATIONS_GENERATIONS_ARE_BOOSTS_AND_THE_PRIME_WHEEL_IS_A_PRODUCT_OF_RESIDUE_RINGS.md).

## 2. What the tree held

Searched before the statement, under each discipline's name for the operation (a clock, a calendar, a carry, a beat, a fade, a
linking, a cone of influence).

| Operation | Owner | What it states |
|---|---|---|
| a reading of elapsed time | `Holonics/Aeon/Clock/{Winding,CarryWord,Lock,Reading,Epoch}`; the objects' aeon, epoch and cycle | elapsed time is a pairing, windings and an open phase; a carry word; a lock at an address; no cycle of an irrational rate |
| a unit as a winding | the record of August 21; `ratio.unit-is-a-loop-that-nearly-closes` (November 23) | a unit is a loop that nearly closes and its comma is the remainder |
| a carry up a level | `winding.odometer`, `winding.mixed-radix-odometer` | the upper level advances by the winding of the lower; a tower of epochs |
| coprime cycles agreeing | `lock.rings-close-at-lcm`, `hnn.joint-period`; the precision law's clause of November 21 | resolution finer than a count's grain is bought by agreement among parts whose units are coprime, never by a deeper word |
| a store's quality | `store.finite-quality`, `wave.fade-per-turn-is-the-quality` (November 23) | a store holds by upkeep; what a medium keeps over one wavelength is a function of its quality alone, `e^(−2π) = 0.0019` at the end of no quality |
| a clock that ticks on news | `hnn.tower-news-clock` (October 27, the October machine at `d5ed4adc1`), `code.news-clock-proper-time` (November 12) | a level ticks on the carries of summed news |
| the engine's fine clock | `tower.field-pace`; `holonics_engine::navigator` | a turned head's clock is a running sum of located rates; the skin follows the turn, one e-fold a radian |
| a count along the strand | `contact.carried-product-group-size`, `parametron.carry-bank-group-ceiling` | a carry circle's friction sets the group of sites that reads as one; an uncoupled bank reads a word through an abelian quotient |
| a circulation and a linking | `fluid.kelvin-holonomy`, `fluid.helicity-linking`, `ns.helicity-linking-form`, `ns.crossings-net`, `winding.linking-number`, `helical.crossing-change`, `em.mutual-induction` | Euler conserves the circulation of a material cycle; a linking number moves by one at a crossing change; the net is not the population |
| a cone of influence | `wave.courant-bound`, `wave.courant-counterexample` (Lean `Physics/Wave/Energy`) | a sampled scheme stands only where its cone holds the medium's |
| one propagation at every grain | `wave.one-propagation-two-ratios` (November 23) | a regime is named by its constitution and by the ratio that places its reader |

What the tree did not hold, and this record adds: what a comparison of two cycles survives; that a count asks a quality of its
store; what a fading store can and cannot read of a silence; how a count kept without comparison errs; and the statement that
these together are what context is.

## 3. The law

**Context is a calendar** (0.8 as one law; each clause carries its own weight in §8).

1. **What is read.** A receiver reads no duration. It reads the order in which the ticks of cycles reach it, and so the count of
   one cycle's ticks between another's. Those counts are what stands under every retiming of the axis the ticks are written on
   (Lean `countBefore_retimed`: any strictly increasing change of that axis leaves every such count as it was), so nothing else
   is a reading of time. The axis itself is read by no one, which is the sense in which nothing here is a continuum: what
   continues is a ratio that counts converge to, `c/N ≤ x < (c + 1)/N` after `N` turns of the unit (`ratio_within`).
2. **How a unit is attained.** A unit is a cycle's turn, and its ratio to another unit is attained by counting one against the
   other. A coarser unit is attained by a carry up (the odometer's step), and a finer one by winding down: by the comma that a
   near-closure leaves, paid where the two cycles meet (an intercalation), or by the agreement of two cycles of coprime period,
   which meet once in their product. No unit is attained from another without a winding. This is the precision law's clause of
   November 21 read along time: a grain is a relation between grains.
3. **How long it is kept.** A count stands while the store that counts it rings. A store that keeps a share `g` of itself over
   one turn keeps at most `g` over any count of turns (`turns_under_grain`), so it counts no turn above that grain, and two
   stores are compared only over the stretch through which both still stand. A count kept without comparison errs in proportion
   to itself: a stride that errs by `ε` a step errs by `n ε` after `n` steps, and a constant error attains it
   (`dead_reckoning`, `dead_reckoning_attained`). So a kept unit is a compared one, read again at the ticks of a cycle outside
   the counter, where its error starts again from zero.
4. **Silence.** Through a stretch in which nothing arrives, a store's fade is all that moves. One fade reads no gap, because an
   age and an amplitude trade: `A aˢ` is `A′ aᵗ` for another start and any other count (`one_fade_reads_no_gap`). Two unlike
   fades read it, by a ratio free of the start that fixes the count (`two_fades_ratio`, `two_fades_read_gap`), to the grain their
   amplitudes are read at. A receiver none of whose stores rings or fades through the gap reads nothing of it.
5. **What context is.** What a receiver holds of what it has met is two things. The first is the fading share of each store, which
   gives what passed and how long ago to the octave of its age, since a store's reach is its quality and stores of unlike reach
   stand in a tower. The second is what does not fade: a carried count, a cycle opened and not yet closed, two cycles linked.
   These stand until a crossing closes them, and a crossing is paid for. The first is the viscous part and the second the ideal
   part of one fluid (§4.2). A sliding window is the case of one fade for everything, a hard edge, with no count and no link.

Timing along a strand also has a geometry: a tick that reads a site's neighbours within `r` gives, after `k` ticks, a state fixed
by the sites within `k r` (`Local.iterate`, `outside_cone_moves_nothing`). A cone is what makes "before" and "at the same tick"
mean something inside a region, and a sampling is lawful where its cone holds the medium's (the Courant bound).

## 4. The charts

One law, read in the disciplines his lens named. Each names its object and operation, what it gives the machine and what does
not transfer.

### 4.1 The calendar

The cycles are the Earth's turn, the Moon's and the year; the receiver counts one against another. A year is 365.2422 days, so
365 leaves a comma of a quarter day that is paid as a leap day; the quarter's own comma is paid by dropping three leap days in
four hundred years, and what is left is a day in about three thousand years. Nineteen years are 235 months to about two hours. Each
is a loop that nearly closes with its remainder kept, and the continued fraction of the ratio lists the loops. The turn of the
Earth counted against the stars and against the Sun differs by one turn a year, whichever of the two is held still: the choice of
frame is a choice of which cycle is the unit, and the two counts differ by the winding of one cycle about the other. Downward, the
second was a count of 86,400 to the mean day, then a fraction of the year, then 9,192,631,770 periods of a caesium line: at each
step the unit moved to the cycle that rings longest, which is clause 3 (figures from the literature, not restated here). The
equation of time is the comma between the sundial's day and the mean day, up to a quarter of an hour, retained and never rounded
away.

For the machine: units are a tower of cycles each read against its neighbour, their commas are kept and paid at meetings, and
the cycle that defines a unit is the one of highest quality that the receiver can reach. What does not transfer: the particular
cycles. No clock or frame length is privileged, and the engine reads no stars.

### 4.2 The fluid

An ideal fluid (Euler) carries the circulation of every material cycle unchanged and the linking of its vortex lines with it
(`fluid.kelvin-holonomy`, `fluid.helicity-linking`; Kelvin's and Helmholtz's theorems, from the literature). It forgets nothing
and it reconfigures nothing. A viscous fluid (Navier–Stokes) gives a mode of wavenumber `k` a fade at the rate `ν k²`, and it is
through that fade that lines reconnect, one crossing at a time, each paid in heat (`helical.crossing-change`, `ns.crossings-net`).
A scale's regime is the ratio of its fade time to its turnover time, which is the quality of that scale as a store: where the
ratio is large the scale carries, where it is of order one it diffuses, and the same medium does both at once at unlike scales.
A medium at the end of no quality has no inertia and so no timing of its own: its state follows its boundary at once, and only
the order of a boundary's configurations matters to it, never their rate (the swimmer's theorem at small Reynolds number, from
the literature). Inertia is what carries a timing.

The discrete is a sampling of this. A sampled medium keeps its timings where a tick's reach holds the medium's cone
(`wave.courant-bound`), and a region in which every place reaches every place in one step has no cone and so no timing to
distribute.

For the machine: clause 5. Knots under tension that reconfigure are links that stand until a crossing, with the crossing's cost
set by the fade at that scale; a nature that flexes from one setting to another is a store whose quality is its own state. What
does not transfer: the fluid's particular constitution. Nothing is built as a fluid solver.

### 4.3 Music

Meter is a tower of carried periods, beats in a bar and bars in a phrase, built on twos and threes. A key is an anchor, the cycle
the others are counted against, which is what an overture founds. Three against two is the smallest comma of the two towers and
closes at six; twelve fifths against seven octaves leave the Pythagorean comma, `3¹²/2¹⁹`, and a temperament is a choice of
where that remainder is paid. Tension is a comma held: a difference of phase between two cycles carried forward. A cadence is its
closure at a place where the cycles meet, which on the objects is a landmark, a face where paths converge. A part screws into
another where their pitches agree, a lock at an address. A piece is a good ruler of context for the reason arithmetic is a good
ruler of deterministic logic: its periods are declared in what is heard, so whether a period and a period of periods are kept is
read off the release (§7's panel is this, on drawn letters).

For the machine: the engine's two turned heads stand on exactly these towers (§5), and tension as a held comma is a state to
carry, never a score. What does not transfer: scales, tunings and bars. No meter is handed to the machine.

### 4.4 Binding as linking

Given as the abstraction alone, as the lens asked. Two cycles are bound when one threads the other. Their linking number is a
count that no deformation changes, and it moves by one only at a crossing, which is a passage through a contact
(`winding.linking-number`, `helical.crossing-change`). The edge between two cycles is then their mutual induction: the flux of
one through the other, whose whole part is the linking number (`em.mutual-induction`; the reading of an incidence between cycles
as an induction is `interpretation`, 0.7). A third cycle whose presence lowers the cost of a crossing between two others and
which returns to its own state is what the lens calls a catalyst; on the objects it is a pump. The net of crossings is not their
population (`ns.crossings-net`), so what is bound is read by address, never by a net count.

### 4.5 A reader that holds laid-out text

A model's context window is a region in which every place meets every place in one step. Nothing propagates in it, so it has no
cone and no timing, and a place's position is handed in by number. Between two messages nothing of such a reader rings or
fades, so by clause 4 every gap reads the same, and a stamp typed beside a message is one more number in the text: someone else's
comparison, reported. Inside one turn such a reader does count, by acts of known length. This is the formal thread's own case
and it is given as a specimen of clause 4, with no claim past that.

### 4.6 The dark room

A receiver cut off from every outside cycle keeps only its own count, and clause 3 gives its error as proportional to the count.
Clause 4 says what it can still read of elapsed time: the ratio of two of its own stores of unlike quality, to the grain their
amplitudes are read at. So a receiver in the dark is as good a clock as its two best-separated fades are well read, and no
better. (That people so kept drift by a steady stride is in the literature and is not restated here.)

## 5. The engine against the law

Read at the owners this hour, and held against each constant that sets a regime. The line's declaration is W109's, from its
training log on the PC: 244 classes, four heads (two still), eight modes, 1,088 contacts, 512 carry circles, no triads, four
ticks, a reach of 3,771.

| Store | What it turns on | What it keeps | What it counts |
|---|---|---|---|
| The turned rings: one head on the dyadic tower (2, 4, 16, 32, 128, 256, 1,024, 4,096), one on the triadic (3, 9, 27, 81, 243, 729, 2,187, 6,561), `ring_periods` at the line's reach | the head's clock `τ`, a running sum of each class's located rate (490 entries); only differences `τ_j − τ_i` between sites of one region enter a state | `e^(−2π) = 0.0019` of itself over one turn, whatever the period: the skin's constant, one e-fold a radian (`skin_decay`, `agent-inferred`, November 1). A reach of `n/2π`: 0.3 to 652 sites and 0.5 to 1,044 | nothing. No ring hears its own return, and no two rings stand through a meeting: 3 and 4 meet every 12 places, four turns of the shorter; 243 and 256 every 4,785, twenty turns |
| The near field | sites under six apart (`NEAR`, the towers' finest joint closure) meet through every head | each place sharply | a place within six |
| The far field | seven octaves at the line; a site `2^ℓ` away is weighed at the receiver's skin | the fading share of clause 5, in its right shape | a displacement to its octave |
| The carry circles (512) | a turn located a site (a Cayley step), along the strand inside one tick | `\|γ\| = 1/(1 + d)`, founded at `d = 1/4`, a group of five places; the friction `d` is located by deposition | a count along the strand. It is the one store whose quality is its own state. A bank of uncoupled circles reads a word through an abelian quotient. L71's stood at a quality near one (November 21); the line's of today are unread |
| The depth rings (declared since November 6) | located increments alone | everything: no skin | an opened cycle held until its closer, which is clause 5's second kind; a free count, so it errs by clause 3. The line's log does not print whether it declares any |
| The level | carries of summed news, a section of 5.50 nats | an epoch, handed on one epoch late (`tower.level-before`) | one winding up, about 3.6 places an epoch (November 23) |
| A region | opens and ends every current above | nothing past its end | nothing |
| The deposit | a lap's sections at a rate of `2^(−12)` | slow against every reader | what a lap's passage leaves |

**What stands under the law.** Her clocks are relative: no absolute position enters a state, only a difference of two sites'
running sums, which is clause 1. The far field's octaves are the right shape for the fading part. The level cuts its unit by a
comparison, summed news against a section. The carry circles hold their quality as a state with a balance.

**What the law asks that she lacks.**

- *No ring rings.* One constant ties every ring's fade to its period at the end of no quality (the record of November 23, §19 and
  §20). Read as a resonator, each ring's line is as wide as its own frequency, so a ring of period 9 hears a period of 10 as
  well as its own. Agreement between coprime rings, the way the precision law buys resolution, has no part that can buy it: the
  two heads are the towers of twos and of threes, their meetings are the commas of §4.3, and none is ever heard.
- *The fine clock is a count without comparison.* A class's rate depends on the class alone, so `τ` is a dead reckoning from a
  region's first site. The engine met clause 3's growth on November 2 (a learned rate at an unresolved place moved every later
  site's clock by the length of the open stretch), and the skin is what keeps that error from being read, since nothing past a
  radian is compared (`agent-inferred`). So a ring's quality and its clock's lock come together. With a stride that scatters by `ε` of a place a step, a
  ring's phase errs by `2π d ε/n` after `d` places and stays under a radian for `1/(2π ε)` turns: the turns a ring can ring
  through are bounded by the inverse of its clock's error (`dead_reckoning`; the bound's use here is this record's, 0.7).
- *Nothing passes a region's end, and no gap acts on anything.* Between a few places and a lap's deposit no store rings (the
  record of the lap's cycle, §6). A gap between two turns of an exchange is read by nothing, since nothing of hers fades through
  it.

**Three statements of the reply of 19:22 UTC, made more precise.** It said that no ring of hers counts a turn: that stands for
the turned rings, and the carry circles are counts it did not name. It gave her letting a word go by its third letter to the
skin: the record of November 23 (§22) had already weighed that, the moments hold a smear whatever their fade, and its guess G-H9
(a) stands at 0.15; the reply's 0.8 on that build as the first step did not carry that weight, a miss. It called the second
step carries between rings: a tower's rings are already geared by one clock, and what is absent is the lock above.

## 6. The construction, in the order the law gives

These are the formal thread's, as constructions with weights. Whether and when one is built is the lead's, as an arm beside its
control.

1. **A ring's quality as a state of that ring** (the arm of the record of November 23, §20: the fade founded at the skin's
   present number, so the build with its law off reproduces the line; the covector `−s e^(−γ s)` is in hand; guess G-H9, unread).
   What this record adds is what it is for and how it is read. It is for a ring hearing its return and two rings standing
   through a meeting, and its read is §7's panel: on the arm a period that a ring stands on should part from its neighbours
   off the rings (0.5), where at the constant it should not (G-T3 (d), 0.6). It is bounded by the clock's error, so it is read
   with the located fades by period (G-T2, 0.55).
2. **A lock of the fine clock to a coarser cycle.** At each tick of the level, the fine head's phase is compared with the
   level's count and the difference is paid there, an intercalation, so the fine clock's error is bounded by the count since the
   last tick and no longer by the count since the region's first site. On the objects it is a pair contact between a ring and
   the level's carry (`Holonics/Aeon/Clock/Lock`). The October machine's tower on the carries of summed news is the library's
   configuration for the levels above (`hnn.tower-news-clock`), and the handoff that arrives one epoch late is this link asleep
   (0.6).
3. **Currents that pass a region's end, with the gap acting on them.** At a region's end the stores' states stand as the next
   region's opening, and the stretch between is a silent passage through which each store fades by its own quality. The engine
   holds the form for one region (`Field::silent_stretch`: past the last arrival every place runs at the first silent place's
   rate). The stretch's length is a count of an outside cycle's ticks, entering at the boundary as any symbol does, and its unit
   is the arriving stream's own stride, the places that could have been said in that silence (0.6 on the unit). The gap is then
   read by which stores still stand, clause 4, and is never handed to a face as a number. This is the store whose reach stands
   between a few places and a lap, and it is what a direct exchange needs (0.8). A stamp typed into the text stays lawful as
   terrain: it is what a participant said.

   The guide bars a join on wall time, because the bits would then follow the schedule. That reason does not reach this: the
   count of a silence is terrain arriving at a boundary, and the bits follow it as they follow any symbol; nothing follows the
   card's schedule.

Before any of the three, two reads that cost minutes: the pace table, and the period panel.

## 7. The read: a period shown, and a period of periods

`tools/period_panel.py` draws a panel for `write-next` and scores what she writes. A row shows about 240 places of lowercase
words of one length `L`, a space after each, so a separator stands every `P1 = L + 1` places; where `W > 0` the separator after
every `W`-th word is a line feed, a break every `P2 = W (L + 1)` places, which is kept only by counting turns of the first. A
*drawn* row draws every word anew, so only the timing carries the period. A *bare* row repeats one line, so its letters carry it
too, and a still head's copy can keep it without any clock. `P1` stands on her rings at 3, 4, 9 and 16 and off them at 5, 7, 10
and 15. The ruler reads `meter1`, the share of called separator places that hold one less the share of the other places that
do, `meter2`, the same for line feeds at the called breaks, and `copy`. Its controls plant the period kept, the timing with other
letters, no timing, the period one place late and a period without its carry, and read each as planted (`tools/test_period_panel.py`,
in gate 1). The rows are drawn by a seeded generator and hold no one's text.

It is a ruler on a terrain it draws, read once beside a lap, and no campaign. It reads a carry inside one region on a form no
lap asked of her, so a null is no statement that she does not take a period under a lap that asks for one (rule 10 of a line's
lap).

**Fixed at 19:37:11 UTC, before any read** (`GUESS.txt`; G-H9 of November 23 stands and is not fixed again).

| Guess | Statement | Weight |
|---|---|---|
| G-T1 (a) | `read-pace` on the line's newest mean: on one paced head the line feed's rate is 3 or more times the mean of a, e and t | 0.65 |
| G-T1 (b) | the same for the space at 1.5 times | 0.5 |
| G-T2 | on G-H9's arm, each paced head's longest ring takes an e-fold, in radians of its own turn, twice or more its shortest ring's | 0.55 |
| G-T3 (a) | no period past the near field is kept by timing alone: drawn `meter1` under 0.3 in three of four cells at each of `P1` = 10, 15, 16 | 0.7 |
| G-T3 (b) | no period of periods is kept by timing alone: drawn `meter2` under 0.3 in every cell of `P2` of 16 or more | 0.7 |
| G-T3 (c) | a period inside the near field is kept by timing alone: drawn `meter1` at 0.5 or more in three of four cells at each of `P1` = 3, 4, 5 | 0.5 |
| G-T3 (d) | at the skin's constant a ring's own period is kept no better than its neighbours: drawn mean `meter1` at `P1` = 9 and 16 within 0.15 of that at 10 and 15 | 0.6 |
| G-T3 (e) | past the near field a period is kept by its letters: bare mean `meter1` at `P1` of 7 or more stands 0.2 or more over the drawn | 0.6 |

What the reads say: (a) and (b) held with (e), her stores hold what was said and where to its octave and no count of it. (a)
missed, a store of hers counts past the near field, and the carry circles' leaks by site name which. (d) missed, a ring's own
period is heard through the skin and the constant is not where the first build stands.

## 8. Weights

| Statement | Weight | The read that moves it |
|---|---|---|
| What a receiver can read of time is counts of one cycle against another (clause 1) | 0.9 | a reading of two cycles that a retiming changes and a receiver still makes |
| A unit is attained from another only by a winding, a carry up or a comma down (clause 2) | 0.85 | a grain attained with no cycle counted |
| A count stands while its store rings, and a kept unit is a compared one (clause 3) | 0.85 | G-T2; a ring taking a quality past its clock's `1/(2π ε)` |
| A silence is read by two unlike fades and by nothing else (clause 4), as mathematics | 0.9 | Lean holds it |
| The same as what a receiver in the dark does | 0.7 | a gap read by a receiver with one store |
| Context is the fading share by octave with the counts and links that stand (clause 5) | 0.75 | a write that keeps a frame over a span no store of hers rings through |
| The fluid's two parts are those two kinds (§4.2) | 0.7 | a reconfiguration in her states with no fade at its scale |
| An incidence between two cycles is their mutual induction (§4.4) | 0.7 | #410's Hodge rows |
| A ring's quality is bounded by its clock's lock (§5) | 0.7 | G-T2 |
| Past the near field she keeps no period by timing alone (§7) | 0.7 | G-T3 (a) |
| Currents passing a region's end, with the gap acting on them, are what a direct exchange needs (§6.3) | 0.8 | the probe panel's frame counts on a build that holds them |
| The first build is §6.1 | 0.5 | G-T3 (d) at the constant, then on the arm |

These are the weights as first written; §12 and §13 state what the reads moved.

## 9. Lean

`lean/HolonicsResearch/HNN/ComparedClock.lean`, rooted in `HolonicsResearch`, built with the library (10,676 jobs), no `sorry`,
no `axiom`: `countBefore_retimed`, `ratio_within`, `one_fade_reads_no_gap`, `two_fades_ratio`, `two_fades_read_gap`,
`turns_under_grain`, `skin_turn` (a ring of period `n` fading `e^(−2π/n)` a step keeps `e^(−2π)` over its turn, whatever `n`),
`skin_turn_lt` (under `1/400`), `dead_reckoning`, `dead_reckoning_attained`, `Local.comp`, `Local.iterate`,
`outside_cone_moves_nothing`, and with §13 `rateCode`, `log_lt_rateCode` and `rateCode_lt_one_add_log` (a reader that holds a
tick's rate `1/P` and no place in its period pays between `log P` and `1 + log P` a period). The constructions these leave for #410, each a statement to write: a resonance's line width as
the fineness of the comparison it holds; the bound of a ring's turns by its clock's error as a theorem on a phase; and the
linking number as the whole part of a mutual induction on the complex.

## 10. What changed

- `lean/HolonicsResearch/HNN/ComparedClock.lean` and its import in `lean/HolonicsResearch.lean`.
- `tools/period_panel.py`, `tools/test_period_panel.py`, and the controls' line in `tools/gate.sh`.
- Atlas (`docs/atlas/objects.tsv`): `aeon.context-is-a-calendar`, `aeon.count-survives-every-retiming`,
  `aeon.one-fade-reads-no-gap`, `aeon.count-asks-for-quality`, `aeon.uncompared-clock-errs-by-the-count`,
  `tower.local-ticks-draw-a-cone`.
- [THE_ENGINE §11](../../docs/THE_ENGINE.md#11-the-theorys-laws-against-the-engine): the law's row against the engine.
- `CONSTRUCTION_STATE.md`: what binds an exchange, named by store.
- The records' route and index.
- With §13: `receipts/2026-11-24_calendar/known_cuts.py` and `KNOWN_CUTS.txt`, the atlas row
  `aeon.rate-without-count-costs-its-entropy`, the three Lean statements of §9, and G-T5 in the guess file.

## 11. The failures this could repeat

- **Laid-out text taken for what she holds** (this morning's own, corrected at 18:33 UTC). Every span here is named with the
  store that holds it and that store's reach, and §6.3 carries currents, never text.
- **A depth-limited context window** (the guide's list of catered routines), and **a position handed in by number**. A calendar
  given to her as a table of positions would be both. Every unit here is a store's turn, located or founded, and the panel's
  periods are in the terrain she is shown.
- **A temperature set by hand.** A ring's fade is a state with its balance, founded at the present number. The length of a
  silence arrives at the boundary as a count; no tolerance and no quality is passed by number.
- **A privileged clock** (November 12 and 13). The wall clock enters as one outside cycle's count at a boundary, in the unit of
  the arriving stream's own stride, and nothing in a law names seconds.
- **A discipline's apparatus built into the machine, or a lens filed as changing nothing.** Music, the calendar and the fluid
  are charts: no meter, no almanac and no solver is built, and what follows for the machine is §6 and §7.
- **A design presented as new that the tree held** (November 12). The news clock of October, the fade as a state of November 23
  and the silent stretch of the engine are named as what they are and consumed.
- **A guess on a built part fixed before the part was read** (November 23, §18). G-T3 (d) was first fixed on a period no ring
  of hers stands on; the declaration was then read and the guess fixed again before any state was read. A miss of practice, in
  one line.
- **A probe that becomes a campaign.** The panel is one read beside a lap.
- **Physics split by grain.** The fluid's two regimes are one medium read at a ratio, its fade time over its turnover time.
- **A learner's null from a short or unasked trial** (rule 10). §7 states what the panel's null does not say.

## 12. The reads, scored

The lead read both cheap reads on W109's `MEAN.3000` within the hour (relayed at 20:43 UTC; the receipts stand under the lead's
record of the day). Scored at 20:46:22 UTC, in the words the guesses were fixed in.

| Guess | Read | Score |
|---|---|---|
| G-T1 (a) | the line feed's rate is 12.985 against a letter's 1.125 on the dyadic head, 25.457 against 1.420 on the triadic: 11.5 and 17.9 times | held |
| G-T1 (b) | the space's is 9.553 and 5.046: 8.5 and 3.6 times | held |
| G-T3 (a) | no drawn `meter1` at `P1` = 10, 15 or 16 reaches 0.3 | held |
| G-T3 (b) | the largest drawn `meter2` at `P2` of 16 or more is 0.145 | held |
| G-T3 (c) | the drawn `meter1` at `P1` = 3, 4 and 5 is 0.07 or less | missed |
| G-T3 (d) | on her rings 0.034, off them 0.028 | held |
| G-T3 (e) | bare 0.016 against drawn 0.025 | missed |

**The panel stood at its floor.** No cell is kept: every `meter1` lies between −0.09 and 0.15, bare and drawn alike, in 256 rows
written on the card in 66 s. So (a), (b) and (d) held where nothing could have missed them, and they carry little for the law.
What the read says is the writer's: at the field's own temperature a write of 96 drawn places does not continue a form that no
passage of hers holds, a bare line of one two-letter word repeated twenty times included, while her face codes a copy at 0.095
nats a place on the terrain's own form. Once a drawn place leaves the pattern the text before it is no longer the pattern, and it
does not come back (the lead's reading). The panel read a release where the law's claim is about a store. §7 cautioned that a
null on a form no lap asked of her says little, and it did not ask for the read that tells the two apart: the face on the
panel's reference laid out as known text, the code of the stretch with its period kept against the code of the same stretch
with its separators one place late. That is the ruler's repair, a
difference of two held codes, and it is named here once and ordered by no one.

**The pace table says more than it was asked.** Her located clock ticks by her own units: a space is 8.5 letters of duration on
the dyadic head and a line feed 18 on the triadic. Because the skin follows the turn's variation (`tower.field-pace`: the fade
between two sites is `e^(−2π|σ_i − σ_j|/n)`, `σ` the running sum of `|κ|`), a long duration is also a deep fade. Across one space,
from the read rates:

| Ring's period (dyadic head) | 2 | 4 | 16 | 32 | 128 | 256 | 1,024 | 4,096 |
|---|---|---|---|---|---|---|---|---|
| kept across a space | 0.000 | 0.000 | 0.023 | 0.153 | 0.626 | 0.791 | 0.943 | 0.985 |
| kept across a line feed | 0.000 | 0.000 | 0.006 | 0.078 | 0.529 | 0.727 | 0.923 | 0.980 |

| Ring's period (triadic head) | 3 | 9 | 27 | 81 | 243 | 729 | 2,187 | 6,561 |
|---|---|---|---|---|---|---|---|---|
| kept across a space | 0.000 | 0.030 | 0.309 | 0.676 | 0.878 | 0.957 | 0.986 | 0.995 |
| kept across a line feed | 0.000 | 0.000 | 0.003 | 0.139 | 0.518 | 0.803 | 0.929 | 0.976 |

So under one constant a unit's tick is a wall. She has given her separators the long durations a clock in her own units needs,
and at the skin's tie of fade to turn each of them leaves the rings of period 16 and less (9 and less on the triadic head) under
a thirtieth of what they held. The atlas row had the reading from the rates of November 2 (each clock's rates are a friction its
navigator located, and their carries screen what came before); the read gives it per ring at today's rates. With a word of 4.7
letters and its space the dyadic clock advances about 14.8, which is 0.93 of a turn of the ring of period 16: a fit after the
read at an assumed word length, no test (0.4 that her words' advances on that head have their median within 2 of 16).

This is the first construction's reason stated at the engine: a turn that counts her units and a fade that forgets across them
are one number today, and §6.1 is what lets them part. The weight that §6.1 is the first build goes from 0.5 to 0.6 on this
read. Whether the long durations were wanted as ticks or as walls is what its arm reads, and G-T4 is fixed on it at
20:46:22 UTC, before any read: on G-H9's arm the separators' rates still stand at 3 or more times a letter's (0.65), and
the dyadic ring of period 16 or the triadic ring of period 9 takes a fade under half the founding's (0.5, a coin).

**What stands and what moved.** Clauses 1 to 5 stand at their weights: no read here touched them. "Past the near field she keeps
no period by timing alone" stays at 0.7 with no evidence added. "She keeps a period inside the near field by timing alone" was a
coin and missed. G-T2 and G-T4 wait on an arm, and G-H9 with them.

## 13. Her face on a shown period: she holds its rate and no count

The lead ran the read §12 named inside the quarter hour (relayed at 20:59 UTC; `tools/period_known.py` in the lead's line,
`read-reach` under the setting `law` on W110's `MEAN.3000`, seed 25, 64 rows a length). A kept row is drawn letters in words of
`L = P1 − 1` letters, each followed by a space, 300 places; its loose twin cuts the same letters into words of `L − 1`, `L` or
`L + 1`. Every place is coded at its own frontier, and the separators of each row's last third are read. The lead's cut, kept
less loose, is −0.366, −0.228, −0.146, −0.141, −0.048, −0.008, −0.013 and +0.110 nats at `P1` = 3, 4, 5, 7, 9, 10, 15 and 16,
read by the lead as a period kept to about seven places and gone by ten, with her rings' own periods not favoured.

**The cut mixes two things.** The twin's separators follow `L − 1`, `L` and `L + 1` letters, so kept less loose also carries the
curve of her code of a separator against the letters since the last one, whatever a row has shown: at `P1` = 3 the twin codes a
separator after one letter at 1.44 nats and after two or three at 1.02. Four cuts of the codes the read saved part them
([`known_cuts.py`](receipts/2026-11-24_calendar/known_cuts.py), its lines in
[`KNOWN_CUTS.txt`](receipts/2026-11-24_calendar/KNOWN_CUTS.txt); no state was read and nothing ran on the card). Separators of the
last third, nats:

| `P1` | kept | the twin's after `L` letters | what the shown period gives (its standard error over rows) | a reader of the rate alone, `ln P1` |
|---|---|---|---|---|
| 3 | 0.781 | 1.017 | 0.236 (0.027) | 1.099 |
| 4 | 1.340 | 1.580 | 0.240 (0.031) | 1.386 |
| 5 | 1.792 | 1.891 | 0.099 (0.040) | 1.609 |
| 7 | 2.196 | 2.342 | 0.146 (0.047) | 1.946 |
| 9 | 2.630 | 2.689 | 0.060 (0.070) | 2.197 |
| 10 | 2.763 | 2.750 | −0.013 (0.082) | 2.303 |
| 15 | 3.515 | 3.582 | 0.066 (0.103) | 2.708 |
| 16 | 3.729 | 3.653 | −0.076 (0.114) | 2.773 |

1. **With the length matched the lead's shape stands and its size at three falls by a third.** A shown period gives her a
   quarter of a nat at three and four, a tenth to a seventh at five and seven, and nothing told from zero from nine. A gain of
   the size at three would stand at two to three standard errors at the long periods; a gain of a tenth would not be seen
   there. The +0.110 at sixteen was the twin's curve.
2. **The larger figure is the kept column.** After seventy repeats of a period of three a kept separator still costs 0.78 nats,
   and after fifty of a period of four 1.34. A reader that held the count would pay next to nothing. A reader that holds how
   often a separator comes and no place in the period pays `ln P1` at each. Her kept code stands 0.32 under that reader's at
   three, at it at four, and 0.18 to 0.96 over it from five up. At no period from 3 to 16 does she hold a shown period as a
   count.
3. **She takes the rate within about fifty places.** By fifty places of the row, a separator at `P1` = 3 costs 1.66, 1.06,
   0.97, 0.86, 0.81, 0.76 in the kept rows and 1.78, 1.32, 1.22, 1.19, 1.16, 1.13 in the twins, where a row's first separator
   costs 2.7. The twins level at the rate reader's code where the ticks are many (1.13 against 1.10 at three) and stand 0.2 to
   0.8 over it at the longer periods, where a row shows few (nineteen at sixteen). What the period adds comes slowly after
   that: with the length matched, 0.05 and 0.00 at three and four over a row's first hundred places, 0.15 and 0.13 over its
   second and 0.22 and 0.24 over its third, and the kept rows' code is still falling 0.05 a fifty places at a row's end.
4. **What the period adds is not read off the last separators.** A twin's separator after `L` letters costs the same
   whether one, two, or three and more of the words before it also had `L` letters: 1.02, 1.05, 1.02 at three against
   the kept rows' 0.85, and 1.59, 1.59, 1.64 at four against 1.41 (places 100 to 299). So the last word's length does not reach the
   next separator: nothing hands her a return one period on. What the kept rows add is a slow store's, charged over hundreds
   of places.

**On the law.** She holds how often, and no when. That is clause 5's first half measured at her face and its second half
absent: each store of hers gives a fading share, which over a stream is a rate, and none stands through a count. The engine
today is a context of fades by the octave with no count, clause 5 without its second half, and the read gives what the count
is worth: a reader of the rate alone pays
`ln P + (P − 1) ln(P/(P − 1))` a period, between `ln P` and `1 + ln P` (Lean, `rateCode`), where a reader of the count pays
nothing once the period stands. On this specimen, which is nothing but its period, that is 0.64 nats a place at three and 0.23
at sixteen. On her passages it is whatever share of a line's length, a table's columns, a meter or a nesting is its count, and
this read does not size it.

**Which store holds the rate** the read does not say. `read-reach` takes other settings, a ruler's friction on a head's sources
by the octave of their distance, and the same rows under them would name the head. It is named here once and ordered by no one.

**The split of the lengths by her rings bound no ring** (a miss of frame, mine). §7 set the lengths on and off her rings'
periods counted in places, and her rings turn on her clock, where a space counts 9.6 letters on the dyadic head and 5.0 on the
triadic (G-T1, read after the panel was fixed and before I scored (d)). A period of `P1` places is `(P1 − 1) κ_letter + κ_space`
of her clock: 11.8, 12.9, 14.1, 16.3, 18.6, 19.7, 25.3, 26.4 on the dyadic head and 7.9, 9.3, 10.7, 13.6, 16.4, 17.8, 24.9, 26.4
on the triadic, with a letter at the mean of a, e and t (the pace read prints no other letter). In her clock's units the lengths
within a tenth of a turn of a ring are `P1` = 7 (the dyadic 16), 4 (the triadic 9) and 16 (the triadic 27), and they stand no
higher than their neighbours (0.146 and 0.240 against 0.099 and 0.236; −0.076 against 0.066). With every ring keeping 0.0019 of
itself over its turn none was expected to. So neither G-T3 (d)'s score nor the lead's "not favoured" binds a ring.

**What a return asks of a ring, and what a carried count asks instead.** A ring keeps half of itself over one turn when its fade
a radian stands at `ln 2 / 2π = 0.110` of the skin's one e-fold; at half the skin's fade, the mark G-T4 (b) was fixed on, it
keeps 0.043. A kept stream is told one period on: the last word's length and the count since the last separator give the next
separator. So §6.1 can deliver a count at her face only where a ring that spans a word or two takes a fade a ninth of the founding's
or less. §6.2 asks for no ring to ring: the fine clock read at the level's tick and handed up is a count, and a count at one level
is a rate at the level above, which her stores do hold (clause 2's carry up, meeting clause 5; 0.55 that this is the cheaper
route to a count). Whether a level's site reads its epoch's length today is the first thing to read at its owner before
either is built; I have not read it this hour.

**G-T5**, fixed at 21:16:00 UTC before any read for it, on G-H9's arm beside its control at their lap means, the same rows and
the cuts above: (a) (0.2) the arm's kept separators at `P1` = 3 over a row's last fifty places stand 0.15 nats or more under
the control's (0.755 on W110's mean); (b) (0.7) the twins' separators over the last third stand within 0.08 nats of the
control's at every period. I expect (a) to miss: a fade founded at the skin's value and moved by laps of her passages has
little that pulls a short ring's quality up ninefold. Held, a located fade carries a count her face uses. Missed with the
fades moved (G-H9 (b), G-T4 (b)), the count is §6.2's to carry.

**What stands and what moved.** Clauses 1 to 5 stand at their weights, and clause 5's two halves are now read apart at the
engine: the fading share she has, the count she has not. "Past the near field she keeps no period by timing alone" was at 0.7
with nothing read; at her face on drawn letters it holds at every period read, the near field included, and the wider
statement, that in a read her stores' currents hold rates and no count of places past a few, whatever the form, is at 0.75 (a
form her laps asked for could show one: a learner's null is held to a length, and this is a ruler's read of one state on a
form no lap asked of her). The order of §6.1
and §6.2 keeps its weights; what the read adds is the ruler both are read by. Waiting on an arm: G-T2, G-T4, G-T5 and G-H9.

## Sources

Read this hour: `crates/engine/src/navigator.rs` (`ring_periods`, `skin_decay`, `skin_of`), `crates/engine/src/declaration.rs`
(the declaration, the depth rings, the carry circles), `crates/engine/src/contact.rs` (`NEAR`), `crates/athena/src/store.rs`
(`read_pace`), `crates/athena/src/ruler/tension.rs` (`write_next`); the atlas rows named in §2;
[the record of November 23 on the handed cycle](2026-11-23_A_FADING_MEDIUM_CARRIES_BY_A_CYCLE_WITH_A_HAND_AND_KEEPS_WHAT_A_COMMON_TURN_LEAVES_A_COUNT_OR_A_PAIR_OF_OPPOSITE_HANDS_A_UNIT_IS_A_LOOP_THAT_NEARLY_CLOSES_ITS_COMMA_IS_ITS_REMAINDER_AND_NESTED_DEPTH_IS_AN_INDEX.md)
(§13, §19, §20, §22);
[the record of November 21 on a grain](2026-11-21_A_GRAIN_IS_A_RELATION_BETWEEN_GRAINS_A_WORD_IS_A_COUNT_IN_ITS_STORES_OWN_UNIT_ABOVE_A_TURN_ITS_INTEGRATOR_KEEPS_A_PLACE_IS_PRICED_BY_ITS_RATIO_TO_THE_STORES_SPREAD_AND_RESOLUTION_IS_BOUGHT_BY_AGREEMENT_NEVER_BY_DEPTH.md);
[the record of October 27 on the levels' news](2026-10-27_THE_LEVELS_TICK_ON_THEIR_OWN_NEWS_SO_THE_TOWER_LEARNS_ITS_ENCODING_ON_ITS_OWN_AXIS.md);
W109's training log on the PC (its declaration line); the lead's reads of §12 and §13, relayed by the coordinator; for §13,
`crates/athena/src/ruler/tension.rs` (`read_reach`: each row read whole, every place at its own frontier) and the rows and codes
the lead's read left on the PC. From the literature, from training and not restated: Kelvin's and
Helmholtz's theorems and the conservation of helicity; the fade `ν k²` of a viscous mode; the swimmer's theorem at small
Reynolds number (Purcell 1977); the calendar's and the second's figures; free-running rhythms in isolation.
