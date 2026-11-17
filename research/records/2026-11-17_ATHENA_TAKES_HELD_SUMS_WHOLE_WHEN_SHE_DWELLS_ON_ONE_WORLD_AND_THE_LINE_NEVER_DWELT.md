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

