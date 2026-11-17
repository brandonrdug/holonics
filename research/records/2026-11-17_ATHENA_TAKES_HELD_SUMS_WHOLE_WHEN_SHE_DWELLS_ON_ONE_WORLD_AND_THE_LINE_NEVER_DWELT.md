# Athena takes held sums whole when she dwells on one world; the ten-pass trials stopped short of the transition, and the line read its store once

November 17, the lead. Refs #404, #405, #73. It follows, and withdraws parts of,
[the record of the step back](2026-11-17_ATHENA_DOES_NOT_COMPOUND_NOTHING_BINDS_NOTHING_TEMPERS_AND_ONE_COMPARISON_TRAINS_EVERY_PART_THE_PLAIN_ENGINE_DOES_NOT_TAKE_A_HELD_SUM_IN_TEN_PASSES_AND_A_PART_WITH_ITS_OWN_FACE_DOES.md)
and [the first founding attempt's](2026-11-17_THE_KEYED_PAIR_PRODUCT_STANDS_IN_THE_ENGINES_HOST_FORWARD_AND_LOWERS_A_HELD_UNITS_DIGIT_TO_1_60_NATS_A_FREE_RELEASE_DERAILS_BECAUSE_THE_PRODUCT_HAS_NO_LEG_AT_THE_RECEIVING_SITE.md).
Receipts: [`receipts/2026-11-17_tempering/`](receipts/2026-11-17_tempering/) (`guesses.txt`, G-L1 to G-L3; `long_*.txt`, `fixed.txt`,
`panel_p250.txt`, `stream.txt`, `text_none.txt`).

## 1. What she wrote

The plain engine, no part added, from the line's lap 94 end state, after 150 passes over 3,923 short sums `a + b = v` (one- and two-digit
operands, 1,766 distinct pairs): 96 held prompts, none of whose sums stands in those passes as written, 8 places written free after each.

```
92 + 61 = 153        97 + 9 = 106        8 + 19 = 27         1 + 8 = 9
96 + 4 = 100         86 + 66 = 152       16 + 67 = 83        6 + 3 = 9
42 + 60 = 92   (reference 102)           33 + 36 = 59   (reference 69)
92 + 11 = 113  (reference 103)           58 + 7 = 55    (reference 65)
```

| the 96 held prompts | written whole | written length the reference's | last digit the reference's |
|---|---|---|---|
| lap 94's state, before the dwell | 2 | | 9 |
| after the dwell (pass 150, one extent) | 86 | 93 | 93 |

By the reference answer's length: one digit 9 of 10 whole, two digits 60 of 66, three digits 17 of 20. Of the 63 prompts whose pair
stands in the passes in neither operand order, 55 are whole; of the 33 whose pair stands there in the other order, 31. The ten that
differ are single digits off (a tens digit one under, a carried hundred kept or dropped) and three lengths. After the answer's line feed
she opens a next record in the table's form. The panel is whole in `fixed.txt`.

## 2. The run

`athena train complete-language try-passes` on the card: the learner's own section step at the state's own rates (every part at 12
bits), 100 records a section (40 sections a pass), each record a region whose run has a keyed half of its places open. The tables are
synthetic. Read every 10 or 25 passes with nothing deposited, on 486 strictly held sums (neither operand order in the passes), 251 held
sums whose pair stands there in the other order, and 400 of the fitted rows: the answer's last digit open alone, in nats a place (ten
symbols flat are 2.303).

The first run (G-L1), three arms that differ only in the store's leak (§7):

| strictly held last digit, pass | 0 | 25 | 50 | 75 | 100 | 150 | 200 | 250 |
|---|---|---|---|---|---|---|---|---|
| no leak | 2.305 | 2.292 | 0.521 | 0.072 | 0.017 | 0.011 | 0.029 | 0.016 |
| leak 12 bits (stopped near pass 105) | 2.305 | 2.261 | 0.276 | 0.089 | 0.023 | | | |
| leak 14 bits (stopped near pass 95) | 2.305 | 2.287 | 0.374 | 0.060 | | | | |

Nothing moves for 25 passes (1,000 sections). Then the digit is taken inside the next 50, about four minutes of the card, and it stays:
density at the written digit 0.99 from pass 100. The leak is not what takes it. The arms were stopped once read, to free the card.

G-L1 was fixed as the step back's own claim (its §10) and missed on every arm. I had given it even odds.

## 3. An artifact of the first run's rows, and the control without it

The held panel written from the no-leak arm at pass 250 read 63 of 96 whole with every write two digits long: two-digit answers 63 of 66
whole, three-digit 0 of 20, one-digit 0 of 10 (`panel_p250.txt`). The cause was the table: a run was the answer, its line feed and five
symbols more, so a region's extent (7, 8 or 9 open places) told the answer's length, and a write's 8 places are a two-digit row's
extent. The reads "with the whole run open" of that run carried the same leak. The last digit open alone did not, since its place is
given and its value is not, so §2's table stands for the last digit and says nothing of a sum's length.

The control again (G-L1b) with every run 8 places (the answer, its line feed and the next record's opening to fill), 150 passes:

| strictly held, pass | 0 | 20 | 40 | 50 | 60 | 80 | 100 | 120 | 150 |
|---|---|---|---|---|---|---|---|---|---|
| last digit open alone | 2.308 | 2.293 | 1.911 | 0.612 | 0.152 | 0.062 | 0.081 | 0.047 | 0.118 |
| last digit, whole run open | 3.056 | 2.652 | 1.839 | 0.788 | 0.274 | 0.161 | 0.138 | 0.061 | 0.302 |
| first digit open alone | 1.631 | 0.839 | 0.444 | 0.288 | 0.095 | 0.036 | 0.031 | 0.011 | 0.039 |

At pass 150 the fitted rows read 0.006 and the pairs met in the other order 0.009, so the strictly held sums keep a gap and a spread
(0.04 to 0.12 from pass 80 on, one state a read). §1 is this run's panel. G-L1b held on each of its four parts (86 against 78 guessed).

## 4. An independent read

Codex (GPT-6.2) read the no-leak arm's state at pass 250 on its own four-prompt squares `(a, b), (a+1, b), (a, b−1), (a+1, b−1)`, neither
operand order in the passes (its mail of 19:53 UTC; its files are private). Two-digit targets: 101 of 104 written, all four of a square
in 23 of 26. Three-digit targets 0 of 152, which is §3's artifact. Over all, 32 of 64 squares follow the difference law
`(z, z+1, z−1, z)`, against 0 of 64 for the closed-face state of this morning. Its reading: ordinary descent learned transferable
behavior. It has the one-extent state for its three-digit squares.

## 5. What is withdrawn

The trials of this morning ran ten passes, 400 sections. The transition's middle stands near section 2,000.

- The step back's §2 reading ("descent on the one comparison still finds no slope into a law that lives in a pair of sources"), its
  §4 item 4 as a measured fact, its §7 ("stepping binds a record to its answer and locates no law": that run was read at pass 500 of
  200 records with its code still falling a tenth every 50 passes), and its §10 ("stepping on the one comparison does not take a law
  that lives in a product", "the read of a founded face has to be founded too"). The engine takes the law by its own descent.
- The first founding record's §5: the build that was to follow (the site's leg, the part's reverse, the closure's covector) answered a
  fault the engine does not have. The closed face (`holonics_engine::closed`) lowered a held digit in ten passes because its covector is
  short; the plain engine reaches further in a hundred. No line uses the part, and its retirement is owed.
- G-O2's reading of the October machine: three passes are no more a length than ten were. What that read holds is its own table.
- What I told Brandon at 18:47 and 19:07 UTC from those readings.

What stands from the step back: the line's Athena is one state rolled through everything; the writes of November 12 to 17 are as he
read them; the deposit had no leak; reports ran on nats; and §4 items 1 to 3 and 5 as descriptions of the engine.

## 6. What the line was

Read from the pass line of lap 94's state: 701,025,568 places taken, each once. The cut takes the slice with least progress against its
quota, each slice's pieces in order from a cursor, and never returns (`passage::Cut::next`); a section is filled with stretches from
every slice.

| slice | places taken by lap 94 |
|---|---|
| code | 140,409,503 |
| web | 70,230,675 |
| science | 70,165,631 |
| books | 42,086,783 |
| wikidata | 28,123,271 |
| arithmetic | 175,004,806 (3,647,503 pieces) |
| words | 175,004,899 |

Arithmetic was a quarter of every section's places since it joined, 3.6 million pieces, and the held units digit of a short sum stood
at 2.33 nats at lap 94. Here 240 thousand records of one world, met alone, took it. So the line's fault was not the sums' count. Brandon's
word for it on November 17 was hot soup sloshed around and never left to settle. Which difference carries it was G-L3's subject, and §8
reads that it is none of the three I named (records met again, a world met alone, sections that are one world's).

## 7. The store's leak

`Learner::leak` (new this day): after a section's step every material entry relaxes by `2^(−leak)` of itself, to the nearest grain; an
entry held by its rate does not leak. It is carried in the learner's text as a trailing `leak K` line and is absent from every standing
state (`host complete-language set-leak`). Its reason is the guide's (no store is at rest; the deposit had no relaxation), and an
entry's steady state under it is `2^(leak − rate)` times the mean of its own step's ratio `m / (⌊√v⌋ + 1)`. On the sums it sped the
transition's first half at 12 bits (0.276 against 0.521 at pass 50) and was not needed. Its value is a trial's bracket; whether it keeps
what one world founded while another is dwelt on is unread.

## 8. Records met again, or a world met alone

The stream arm (G-L3): 400,000 fresh sums of the fitting half's operand law, no held pair in either operand order, each met once; 100
passes of 4,000 rows (4,000 sections), one extent, from lap 94's state (`stream.txt`).

| strictly held, pass (sections) | 25 (1,000) | 40 | 45 | 50 (2,000) | 60 | 70 (2,800) | 85 | 95 | 100 (4,000) |
|---|---|---|---|---|---|---|---|---|---|
| last digit open alone | 2.301 | 2.205 | 1.509 | 0.843 | 0.242 | 0.075 | 0.046 | 0.020 | 0.076 |

Its panel at pass 100: 88 of 96 held sums written whole (one digit 10 of 10, two digits 61 of 66, three digits 17 of 20), the written
length the reference's in 95. The transition stands where the control's does. So meeting a record again is not what founds the law: a
world met alone is. The guess held (under 0.1 nats at section 2,800).

The two mixed arms (`alternating.txt`, `within.txt`), each stopped once read:

| strictly held last digit open alone | at about 120 thousand sums met | 160 thousand | 200 thousand | 400 thousand |
|---|---|---|---|---|
| the control, sums alone (passes 30, 40, 50, 100) | 2.244 | 1.911 | 0.612 | 0.081 |
| sections of sums and of text alternating (the same passes) | 2.197 | 1.208 | 0.506 | 0.065 |
| 25 sums and 75 text rows inside each section (the same passes) | 2.187 | 1.809 | 1.235 | |

- **Alternating sections.** The sums are taken on the control's schedule, and the text beside them falls on the text-alone arm's
  schedule (held tenths 1.782 at pass 100, where the text-alone arm read 1.786). Its panel at pass 100: 87 of 96 held sums written whole,
  the last digit the reference's in 95; the text panel, written left to right, 75 of 133 words in the lexicon (56%). One state holds
  both, each learned as if alone.
- **Mixed inside each section**, where the sums are 6% of a section's places: the transition comes at about the same count of sums met,
  a little later.

So G-L3's guess for the mixed arms missed: neither a second world between the sections nor inside them stops the founding or much
delays it. What the four arms agree on is a count: about 160 to 200 thousand records of the law, each with its operands known and its
answer open, met in any arrangement tried.

**That leaves the line unexplained by its pass alone, and §6's reading is narrowed.** The 175 MB of arithmetic the line took hold
1,627,767 two-operand sums of one- and two-digit operands (counted in the slice), eight times the count above, and its held units digit
stood at 2.33 nats. Two things differ there that no arm here read. The sums were about a hundredth of a section's places, five times
thinner than the thinnest arm. And the line's trainer opens a stretch by its writer's and mask states (`passage::state_of`), in which an
answer's place is often open while its operands, a few places to the left, are open too: a comparison with nothing to found on. The
same holds for text there: most open places stand beyond other open places, so the field is compared on a symbol whose near left is
unknown, which is a blend's training. Lap 94's state codes the next place on its whole left context at 2.05 nats. Neither is read as
the cause yet; the second is what the plain-text run of the night tests (§11).

## 9. Plain text under the same dwell

The world: three simple narrative books of the store's books slice, about 41 thousand octets each, a line break's hyphen joined at the
boundary; their first nine tenths the fitting text (111,469 octets; rows of 48 known places and a run of 32; 35 sections a pass), their
last tenths held, a fourth book never read. From lap 94's state, no leak. A keyed half of the run open, nats a place:

| pass | 0 | 50 | 100 | 150 | 200 | 250 | 300 | 400 |
|---|---|---|---|---|---|---|---|---|
| fitting rows | 2.049 | 1.748 | 1.666 | 1.624 | 1.586 | 1.550 | 1.532 | 1.494 |
| held tenths | 2.035 | 1.819 | 1.786 | 1.760 | 1.748 | 1.750 | 1.753 | 1.773 |
| the unread book | 1.974 | 1.861 | 1.849 | 1.867 | 1.871 | 1.887 | 1.907 | 1.935 |

No transition. The fitting text falls slowly, the held tenths stop near 1.75 by pass 200, and the unread book turns back after pass
100: the field is taking these three books' own strings. The panel (twelve prompts, 64 places, the writes private):

| the twelve prompts | words written | in the fitting text's lexicon | longest run shared with it |
|---|---|---|---|
| lap 94's state, the law's keyed order | 121 | 48 (40%) | 11 octets |
| lap 94's state, place order | 127 | 54 (43%) | 11 |
| pass 400, keyed order | 131 | 56 (43%) | 10 |
| pass 400, place order | 141 | 83 (59%) | 15 |

(The held text's own words stand in that lexicon at 88%, the unread book's at 81%.) Written left to right the share of words rose by a
third, on fitted, held and unread prompts alike (64%, 57%, 54%), and nothing was recited. Read by eye the writes hold more short words
and the books' names, and are still almost-words. In the law's keyed order within an octave the dwell bought nothing. At pass 400 the
fitting rows read 1.494, the held tenths 1.773 (their lowest 1.746, near pass 200) and the unread book 1.935. G-L2 held on the held
rows' floor and the panel's shares and missed on the fitting rows (1.2 guessed), on a rise at the end (0.03 against 0.05) and on
recitation (none); its leak arm was stopped at pass 12 to free the card and is unread.

Read against §2: a sum's law is one covector that every record of the world pushes the same way, and 2,000 sections of it close the
lock and the product together. A text is thousands of small laws, each word one, that share every entry and are each met once in
several sections. Under a step that divides an entry's first moment by the root of its second, a law's step is its own signal over
every other law's variance on the entries it shares, so each word is taken at a small fraction of the rate (`agent-inferred`; it is
what G-L3's mixed arms test on the sums). Brandon's reading of the same day names the missing thing: the binding is not sparse, so
partials do not get to cohere. A dwell alone does not give it.

## 10. A rule from the failure

Added to the guide's method rules: a learner's null is held to a length. Before a trial is read as "the machine does not take X", its
own code has stopped falling, and its length is set against a control that does take a law of that kind. Ten passes were read as a
null; a founding part, a day's plan and two statements to Brandon stood on it.

A second, smaller: a trial's table is read for what its form gives away before a held read is quoted (here a region's extent).

## 11. What follows

Brandon, the same evening (20:27 UTC, in my words): the sums are a way of looking at what she learns on simple examples and are not to
become a campaign; a worded form she was never shown is expected to fail and is no finding. The second worlds I had queued (three-digit
sums, subtraction, `add x to y`) are not run. One pair stays as a single look at whether a founded law shortens the next (`x plus y
equals` from the founded state and from lap 94's), and is read in `guesses.txt`.

1. **Text, the main line.** A run of the night (G-N1): fifty simple narrative books as next-symbol rows, each place compared on its
   whole left context, 40 passes, with sixteen prompts written left to right after each pass. It reads whether the states a field is
   compared on, more than its pass, are what kept text at almost-words (§8's last paragraph).
2. **The pass's own navigation.** The engine has no act of staying or leaving: the cut chooses before any forward. The first chosen
   contact is the pass's, read from the learner's own progress in a world (the receipt's `predicted` and `transfer`, kept as one slow
   store a world), drawn by odds, with a matched replay against the quota law. This is Brandon's line of 16:08 UTC and Codex's crossing at
   the pass's grain. The arms of §8 say what it is for: not to keep worlds apart, which they do not need, but to give a law the count of
   well-formed records it needs before the pass moves on.
3. **What text needs that a count does not give**: a law its own entries and its own comparison (§9), if the night's run leaves
   almost-words on the page.
4. Every step's report opens with the panel, whole.

## 12. The one worded pair, and the night's run at its second pass

**The pair** (`worded_zero.txt`, `worded_pair.txt`; G-W1). Zero-shot, the state that writes `a + b =` whole writes 0 to 3 of the 96 held
sums in each worded form (`a plus b equals`, `a plus b =`, `a + b equals`, `add a to b =`, `add(a,b) =`), which Brandon reads as
expected: she was never shown that `plus` is `+`. Shown `a plus b equals` as a stream of fresh records, the state that had founded the
sign form takes it under 0.1 nats by section 400 and writes 95 of 96 held sums in it; lap 94's state, shown the same, takes about 3,000
sections, the first founding's count. What she had founded carried, about eight times sooner, and only where the operands stand had to
be found again. The sign form loosened while she was away from it (its panel 86 to 53 of 96), which the alternating arm of §8 does not
show. This is the last of the arithmetic.

**The night's run at pass 2** (G-N1; the writes are the store's and stay private, the counts are here). Lap 94's state codes the next
place on its whole left context at 2.05 nats on the held twentieths; after one pass over the fifty books (2,244 sections, eleven
minutes) 1.732, after two 1.645 (fitted 1.615, the unread books 1.659).

The law's writer could not read it. A field compared only on a place that ends its region meets, under `write-forms`, a place with a
run of open places to its right, a state it was never compared on, and the first panel came out as dashes and quotation marks. A
ruler's writer that meets the compared state (`write-next`: one place a read, each place the last of its region, 48 known places)
reads it:

| sixteen prompts, 64 places each | words written | in the fifty books' lexicon |
|---|---|---|
| lap 94's state | 155 | 59 (38%) |
| after pass 1 | 189 | 117 (62%) |
| after pass 2 | 193 | 139 (72%) |

By eye: lap 94's state writes debris of every register it met (code, markup, almost-words). After pass 1 the writes are plain prose
with real short words and sentence marks; after pass 2 most words are real and the syntax is word salad. Not clean. It is the largest
change in her text of any step this month, in twenty-two minutes, and the only thing changed is the state she is compared on.

The reading it supports (`agent-inferred`, the run goes on to pass 40): the line compared her on writer's states and mask states
(`passage::state_of`). In a writer's state the open places past the first stand beyond other open places, so their near left is
unknown; in a mask state the right side is half known. She was almost never compared on a place as the boundary of what is known. A
place compared beyond open places is trained to a blend, and her almost-words are blends. The generation law asks for a boundary that
is released; the boundary of a passage being read is its next place.

## 13. The build the night's run points to, fixed before it is made

Read at pass 5 (`guesses.txt`): the held next place 1.732, 1.645, 1.603, 1.582, 1.569 nats (2.050 before), the panel's words in the
lexicon 61%, 72%, 69%, 74%, 75% (38% before). The fall flattens toward about 1.5, and the writes at pass 5 are real short words and
phrases with no clean sentence. So the comparison's state removed the debris in an hour, and what shows now is the engine's own level.
Two things follow, in this order.

**1. The boundary chart** [definition; agent-inferred, November 17, to be built]. A passage being read has a boundary, its next place.
A receiver at place `t` reads the passage's current up to `t − 1` and its face is compared with the symbol that arrives at `t`. Every
place of a known passage is such a boundary at its own time, and one forward compares them all when the transport is one-sided: no site
reads its own symbol or anything past it.

```text
moment     s_t = Σ_(k<t) ζ^(k−t) D(t−k) E₋(u_k)                       the retarded moment: the strand's past at the place
open       x⁰_t = E₋(u_(t−1)) + C s_t + b_s                           no row of the site's own symbol, none of the next
support    S_i = { j < i : near or of the probe's class }               sources stand before their receiver
strand     the pair's mate t − 1; the circles' scan in the passage's direction
face       at every site, compared with the symbol that arrives there
```

By induction over the ticks a site's state is then a function of `u_(<t)` alone, so a site is a source for every later site and a
receiver of its own symbol at once, and no site is veiled. The two-sided field stays for a region that is complete in space (a problem
with its port, an image, a place to fill), under the declaration's word.

Why: tonight's run compares one place a region of 49 sites, 400 comparisons a section. The chart compares every site of a region, about
48 times the comparisons for the same forward, which is what makes megabytes a minute and not a pass in eight. And it is the generation
law read on a passage: the boundary that is released is the next place, where the writer by octaves released far places before near
ones and the trainer's states followed it (§12).

The recorded failures it could repeat, checked: a design thought in offsets (it is stated on the retarded moment and the support's side,
and the trial's 48 known places are a ruler's convenience, not the chart's reach); a modality's exception (a passage in time is read
this way whatever it carries; a region in space keeps the two-sided field); a context window standing in for learning (the reach is the
declaration's: moments and far sources span the region); the transformer's global pass (the field still disperses: near field and
classes, one side of them).

Acceptance, fixed now. (a) With the word off every state reads and trains bit for bit as before, and the card's bits are the host's
with it on. (b) A place's face under the chart does not change when any symbol at or past it is changed (tested on the bits). (c) On
the fifty books, a pass that compares every place once takes under a minute of the card, and the panel after equal comparisons is at
tonight's level or past it, read by eye first. Parts not yet made one-sided (the second read's mark, the level, the junction, the
triad's forward leg, the blank clocks) are refused under the word until each is.

**2. Then her own navigation**, which this chart makes natural: a reader's boundary moves, so reading is the navigation. The passage's
moments carried across a stretch's end (Codex's one-opening packet is the oracle for what crosses; a cold restart between), then the
stride, the choice to stay and the next piece read from her own progress (the receipt's `predicted` and `transfer`).

What neither gives is depth of binding: at about 1.5 nats a place she writes as a short-context model does. A law's own entries and its
own comparison (§9), sized by what a founding saves, is the work after these two, and the chart is what makes its trials cheap.

## 14. How far back she reads, against a count of the same text

Two rulers on the pass-5 state, the same 1,200 held rows (`reach_and_count.txt`). Her next-place code when only the last `k` places
stand in the region, and a count model's code by the longest context it may use (interpolated Witten-Bell, counted on the fitted text):

| known places | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 48 |
|---|---|---|---|---|---|---|---|---|---|---|
| Athena, pass 5 (nats) | 4.241 | 2.957 | 2.422 | 2.083 | 1.843 | 1.711 | 1.619 | 1.591 | 1.549 | 1.547 |

| the count's longest context | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| a count model (nats) | 3.013 | 2.373 | 1.924 | 1.577 | 1.395 | 1.361 | 1.374 |

She draws on about twenty-four places, and with all of them she codes what a count of three places codes. (Her short regions are states
she was not compared on, so her left columns read high; the right columns are the fair ones.) A count of five places reads 1.36 on this
text. So her context is wide and soft, where a word needs the last five symbols held sharply together. That is §9's reading measured:
nothing binds. It is also what the boundary chart alone will not change, and what the work after it is for.

## 15. The control: the same books under the old kind of comparison

§12's reading rested on a run that changed two things at once, the state compared and the text (fifty storybooks). The control changes
one (G-N2, `night_text.txt`): the same fifty books from the same start, read as the first dwell read its three, rows of 48 known places
and a run of 32 with a keyed half open, for the count of compared places the night's run had made.

| at equal compared places | 0.9 million | 9 million | the panel's words in the lexicon |
|---|---|---|---|
| each place compared as the boundary of what is known (the night's run, passes 1 and 10) | 1.732 | 1.536 | 73% at pass 10, 76% at pass 15 |
| a keyed half of a run open (the control, passes 1 and 10) | 1.922 | 1.813 | 56% (51% by the law's writer in place order) |

(The held next place on its whole left context, nats; 2.050 before either.) By eye the control writes almost-words again and the run
writes real words in broken phrases. Both guesses of G-N2 held. So the comparison at the boundary is what text needed first, and the
register by itself does not give it. The night's run stood at 1.527 nats at pass 15 and goes on to pass 40.

## 16. The backward trace: of the letters that go in, about one and a half come back

Brandon, 23:06 UTC (in my words): the run of the night was a heavy bet on a reader that showed no coherence in two hours, and I go
forward without analogizing the backward pass. The run was stopped at pass 16 on its own number (the held code fell 0.0013 nats in
that pass), and §13's build is not started: a chart 48 times cheaper is an efficiency bet on a reader that does not yet bind, and the
trial's tool already gives a pass in ten minutes.

The analogy, taken as one. A forward pass gathers from the sources to a place. The backward pass carries the comparison back through
the same contacts to what caused it. The two are a round trip, and what survives it is what the path keeps. So the question §14 left
(she draws on 24 places and codes like a count of three) is asked backward: of the symbols that went in, which can be read back out of
her state at the place? This is the guide's own rule of November 16 (a premise is a presence at the consumer, read link by link before
a build), which I had not applied to text.

`tools/trace_ruler.py` on the pass-15 state (`backward_trace.txt`): 5,164 held rows, the place's charts at each tick read by least
squares for each earlier symbol's identity, fitted on half the rows and read on the other. Share of the symbol's identity present, in
thousandths:

| the symbol | at the opening | after tick 1 | tick 2 | tick 3 | tick 4 (what the face reads) |
|---|---|---|---|---|---|
| 1 place back | 981 | 964 | 903 | 746 | 664 |
| 2 back | 360 | 374 | 537 | 413 | 355 |
| 3 back | 126 | 151 | 212 | 195 | 171 |
| 4 back | 46 | 59 | 107 | 77 | 67 |
| 5 back | 0 | 7 | 35 | 12 | 10 |
| 6 and farther | 0 | 0 | 0 | 0 | 0 |
| the pair before the place, jointly | 334 | 299 | 368 | 303 | 264 |
| the triple, jointly | 169 | 170 | 213 | 203 | 195 |

- The opening gives one symbol whole, the one before the place (its strand contact's row). The moment's chart brings a third of the
  second, an eighth of the third and a twentieth of the fourth.
- The ticks add little: the second symbol gains eighteen points at tick 2 and loses them again, and the nearest symbol fades from 98%
  to 66% as the ticks write over the place.
- The rows that do the gathering are soft. Two heads keep three quarters of each row on sources eleven places away or more; the other
  two spread theirs over the five nearest places, a tenth to a third on each, their largest single share 0.2 to 0.6.

So at the place where her face is read, about one and a third symbols of the last five are there (0.66 + 0.36 + 0.17 + 0.07 + 0.01),
the rest of her 24 places being diffuse (register, the shape of the word), and the fourth and fifth symbol never arrive at all. §14
called the limit binding. The trace puts it one link earlier: there is nothing at the place to bind. The carriers are narrow (a
moment of 32 complex modes for the whole past, a head's current of 16 numbers) and the lock that would address "the source three back"
does not close, the same link that slipped on the sums on November 16.

What it changes. More passes of this reader, or a cheaper way to make them, cannot give words, because five symbols do not reach the
place by any path it has. The object the theory holds for exactly this is the strand: the residue of a running word on a few coprime
rings keeps the last several symbols whole and in order, as one address (the located transport of October 5; the strands of October
26), and rows met at that address are a law's own entries. The next reading is that premise on this text, before any part: what a
strand's residue of the last five symbols carries to the place, against the count ruler's 1.36 nats.

## 17. The trace on the passage's own clock: she opens units and does not close them, and nothing coarse-grains

Brandon, 23:17 UTC (in my words): why is this quantified by letters; where is he losing me on the coarse graining and the tokenization.
§14 and §16 are stated at the codec's grain, a byte as the unit and an offset as the distance, and so were the 48-place rows and the
ruler I had begun for §16's last paragraph (windows of bytes and a word boundary I authored). That is the recorded failure of a design
thought in offsets and windows. The theory's units were already in the guide and the atlas: a byte is a digit of the passage and a
symbol a length (its news); the passage's clock is its running news `S`; a reader of period `σ` begins a unit where `S` carries
(`deposition.return-on-news-clock`, `helical.closure-remainder-held-by-the-locale`); a completed unit is one symbol of the next ring;
and the past is a word in that radix. The same dump, read in them (`tools/news_ruler.py`, `news_trace.txt`; a place's news is its code
length under a count model of the fitted text, a ruler's stand-in for her own):

**Where her cost is.** The arriving place's news under the ruler, her code there, nats:

| the arriving place's news | places | the ruler | her | her excess | share of her whole excess |
|---|---|---|---|---|---|
| under 0.25 (the passage has nearly decided it) | 34% | 0.065 | 0.340 | +0.275 | 48% |
| 0.25 to 1 | 23% | 0.567 | 0.958 | +0.391 | 45% |
| 1 to 2 | 18% | 1.474 | 1.829 | +0.355 | 32% |
| 2 to 4 | 20% | 2.789 | 2.874 | +0.085 | 9% |
| over 4 (a landmark) | 5% | 6.152 | 4.833 | −1.319 | −34% |

Nine tenths of her excess stands at places that carry under one nat, the inside of a unit, and at the landmarks she codes 1.3 nats
under the ruler. She opens units and does not close them.

**What she holds, against distance in nats of passage.** A symbol's identity present in her state where her face reads: 446
thousandths within 1 nat before the place, 353 at 1 to 2, 242 at 2 to 4, 38 at 4 to 8, none past 8. Her span is about four nats; a
word of this text is eight to ten.

**What carries.** The unit in progress, as one identity, present where her face reads, by the reader's period: 200 thousandths at 2
nats, 106 at 4, 7 at 8, none at 16; the unit before it, none at any period. (The identity read is starved for long units at 2,582
fitted rows, so the figures at 8 and 16 are floors.)

So nothing coarse-grains: no unit reaches a place whole and no completed unit crosses to the next. Everything she holds is on the
fine ring and spans half a word. The engine's grain diverges from the theory's at exactly this: one site a byte at every scale, a level
whose sites are landmarks of news but which hands down mixtures and commits no unit, and a comparison counted a byte. §16's "the
fourth and fifth symbol never arrive" is this reading at the wrong grain, and its last paragraph's premise is restated: what the unit
in progress and the completed units before it, each one address and cut by news with nothing authored, let a place code and write.

## 18. Rulers for the other side, and what they are worth

After §17 I priced the theory's side with rulers outside the machine on the fifty books, three in an hour
(`rulers_whole_context.txt`; each a count reader's kin with rows shared on two coprime rings; counts and codes only).

- **Windows of symbols** (the codec's grain; a yardstick). The last one to six symbols as nested addresses: held next place 2.43, 2.00,
  1.70, 1.50, 1.43, 1.40 nats; its panel 90% of words in the lexicon, written in a minute of the host. What a place writes when its
  context arrives whole is plain.
- **Units cut at landmarks of news as addresses for the next symbol.** One period at a time: 1.95, 1.83, 2.03 nats; six periods at
  once: 1.63 and 76%, her own level.
- **Two levels**, the record of November 12 read as written (a site of the level above is an epoch of the clock of news; a composite
  is a prime of higher rank whose own length is shorter than its bytes' added): units cut at landmarks of a three-symbol reader's
  news, each completed unit one symbol of a count reader of units, the held text coded as units against the same bytes one by one:

| mean unit | distinct units | bytes one by one | units as symbols | units met before | a unit shorter than its bytes added | longest run shared with the books |
|---|---|---|---|---|---|---|
| 2.1 symbols | 4,750 | 1.430 | 1.508 | 100% | 49% | 19 octets |
| 2.8 | 14,136 | 1.430 | 1.550 | 99% | 48% | 26 |
| 3.8 | 41,465 | 1.430 | 1.606 | 95% | 41% | 49 |
| 5.8 | 82,448 | 1.430 | 1.577 | 81% | 34% | 64 |

  Written a unit at a time the words are real (81% to 88%), and at the larger units it is recitation: a panel line of 64 octets copied
  whole.

These do not show the theory's coarse graining paying on this text, and they are a verdict on my constructions. Each unit there is a
free row addressed by its content, the index of contexts the lessons refuse, which recites as it grows; in the theory a unit shares
its rings with its kind (the record of November 12, §10: a key factors as its family and its member; rows shared along the ladder) and
a level is a receiver compared at its own grain. I built neither, and I built three rulers at the speed Brandon had named the same
hour. None becomes a part.

What follows is slower. The machine has a level whose sites are landmarks of her own news, in lap 94's state and in tonight's, and no
reading of this record has looked at it. Its records of November 13 to 15 are read first, then that level is traced on tonight's state
as §16 and §17 traced the byte path: where her epochs fall, what an epoch holds of itself, and whether anything crosses from one epoch
to the next.

## 19. Her own level, traced: the units are cut, and the level holds almost nothing of them

The machine has a coarse grain of its own, built on November 13 from the record that owns it
([the level's design](2026-11-13_A_LEVELS_SITES_ARE_THE_EPOCHS_OF_ITS_NEWS_BEGUN_AGAIN_AT_EACH_OPENING_ITS_CLOCK_IS_THE_NEWS_BETWEEN_THEM_A_PLACES_NEWS_IS_READ_AT_ITS_CAVITY_FACE_AND_EACH_NAVIGATOR_KEEPS_ITS_LOCATED_CLOCK.md),
§4.2 to §4.7): a level's sites are the landmarks of the news below it (a place no larger news stands within a section of, the section
the flat face's code, 5.50 nats here); a place's news is read at its cavity face; an epoch has no row, its face is its moment on the
news phase (six harmonics of its places' reads) restricted to a level state 64 wide, which ticks on its own clock and hands harmonics
back to the epoch's places. It stands in lap 94's state and in the night's. §16 to §18 never looked at it.

`Constitution::level_trace` and `athena host complete-language read-level` write it out, and `tools/level_ruler.py` reads it
(`level_trace.txt`; the night run's pass-15 state, the 5,164 rows of §16; 32,584 epochs):

- **Where her epochs fall.** A place's news at its cavity face is 1.15 nats in the mean. A whole epoch is 8.6 places and 9.5 nats on
  average (median 7 places), about a word of this text in news. Its leading place is the first letter of a word in 36% of epochs,
  inside a word in 55%, a space or a mark in 9%. Her landmarks stand where she is surprised, and §17 read that she is surprised inside
  units.
- **What the level's state of an epoch holds**, read by least squares on half the regions, in thousandths: the epoch's first symbol
  68, its second 70, its third 47, its last 102, its size in places 164, the epoch as one identity 171; the epoch before it as one
  identity 24; the symbol that leads the next epoch 43.

So the units are cut by the theory's law and at about a word's news, and the level carries almost nothing of them: an epoch is not
held as a symbol, the epoch before it does not cross, and the level says nothing of what follows. With §17: she loses inside units
because nothing closes one, and the level that would hold a unit and give its interior back is nearly empty.

The cause is in the source (`field/scale.rs`): the level has no comparison at its own grain. Its state is trained only through the
prolongation's effect on the byte faces, several operands downstream, and nothing asks it to hold its epoch or to read the next. The
objects give every receiver its own receipt, and #405 names learning per contact; the level is a receiver without one. This is §4's
fourth fault of the step back, found at the one place where the theory's grain was built.

**Where this stops.** No part follows from tonight. What is owed first is reading: the rest of the level's records (the landmarks'
ruler, the return on the clock of news of November 15, the news clock of October 27), then what a comparison at a level's own grain
is on the objects: the epoch's closure (its state gives its interior back, which is what would take the news out of a unit's inside)
and the next epoch read from the epochs before. It is written before it is built, with its acceptance on the passage's clock.

