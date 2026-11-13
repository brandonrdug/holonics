# Hand-off: the engine and the level's first build pass to a new thread; the state, the queue, the fixed guesses, the open readings and the standing flags

November 13, 2026. A hand-off note, written when Brandon moved the engineering and the PC's runs
from this thread to another to save usage. It states position and intent. It adds no law: each
law is in its own record, cited here, and a successor reads those. Figures are from the receipts
the cited records name. The order of work in §4 is the writer's (`agent-inferred`), and each
step in it fixes its guess before its read.

## 1. Position

- **The trunk.** `main` stood at `4f1347a6b` before this change. Merged on November 13: the one
  law of sites (a level's sites are the landmarks of its news; G137 held 40 of 40), the law of
  the opening's comparison at every place (G132, G139 fixed), the timing of every layout change
  on copies of the pair kernels (G138), the guess for a site's maps (G117), and with this
  change the widths' reading ([the engine record](2026-11-12_A_SITES_ARITHMETIC_IS_COUNTED_AGAINST_THE_CARDS_LANES_THE_STORE_TRAINER_RUNS_AT_ONE_FORTIETH_OF_THEM_A_PAIRS_SKIN_IS_FORMED_ONCE_A_CLOCK_AND_COST_FOLLOWS_SURPRISE.md) §9), the candidate law of the
  contact's receivers ([the design record](2026-11-13_A_LEVELS_SITES_ARE_THE_EPOCHS_OF_ITS_NEWS_BEGUN_AGAIN_AT_EACH_OPENING_ITS_CLOCK_IS_THE_NEWS_BETWEEN_THEM_A_PLACES_NEWS_IS_READ_AT_ITS_CAVITY_FACE_AND_EACH_NAVIGATOR_KEEPS_ITS_LOCATED_CLOCK.md) §4.8) and its guess (G140).
- **The engine against the card.** The bar is one millionth of a second a computed site, 40.7 ms
  a section of 40,741 computed sites. An unprofiled section takes 279 ms, 6.9 times the bar.
  The profiled kernels take 267.4 ms by family: the contact 115.6, a site's maps 56.3, the small
  site kernels 34.3, moments and clocks 29.9, blank clocks 16.5, carry circles 9.8, faces 4.9.
  A section is 218 regions, 41,462 sites and 45.7 million pair-terms.
- **What the pair kernels' readings settled.** Every layout change together leaves the family
  at 0.77 to 0.83 of its time, so no layout is built (G138). Their widths are a realization
  worth about 10 ms a section, every bit kept (the engine record §9). Their multiple lies in
  which rows are computed and which sources a row meets.
- **The level above.** Designed on the news ([the design record](2026-11-13_A_LEVELS_SITES_ARE_THE_EPOCHS_OF_ITS_NEWS_BEGUN_AGAIN_AT_EACH_OPENING_ITS_CLOCK_IS_THE_NEWS_BETWEEN_THEM_A_PLACES_NEWS_IS_READ_AT_ITS_CAVITY_FACE_AND_EACH_NAVIGATOR_KEEPS_ITS_LOCATED_CLOCK.md)): each navigator
  keeps its located clock, a level's sites are the landmarks of the news below it, its clock is
  the news between its sites, a place's news is read at its cavity face, and the opening is
  compared at every place. One program reads every stream
  ([the record of the landmarks](2026-11-13_A_LEVELS_SITES_ARE_THE_LANDMARKS_OF_ITS_NEWS_A_PLACE_NO_LARGER_NEWS_STANDS_WITHIN_A_SECTION_OF_THE_CLAIM_THE_CARRIED_CUT_AND_THE_ODOMETER_ARE_ONE_LAW_ANCHORED_NEARER_AND_FARTHER_AND_ONE_PROGRAM_READS_EVERY_SYMBOL_STREAM.md)).

## 2. The PC's queue

Orders are numbered and sent as plain text. P45 to P61 are sent. Their texts and the operating
details are in the project's private hand-off folder and are not in git.

- **P60, the opening's comparison at every place** (a change of law, the level's first build;
  G139). Branch `claude/opening-compare`. Reported at the hand-off: the declaration, the layout
  and the state version for the opening's block; the cavity moments and cavity openings from a
  region's sums; and the first check, which passed (the largest difference 0 over 56, 88 and
  128 words at 2^-16 against a rounding bound of 5, on three fixture regions, with a check that
  the test is not vacuous). Owed: the comparison and its return, the parity fixtures, gates 1
  and 3, the reproduction of the line with the new law off, the trained read, the receipt
  `p60_opening.txt` on `claude/carry-reads`, and a pull request read at source and merged from
  the cloud.
- **P61, a site's maps in the tile form** (a realization; G117). Branch `claude/site-maps-tile`,
  from `main` as it stands when the build starts. Its first item sets the ruler branch
  `claude/contact-copies` aside by tag (`archive/claude/contact-copies`); that build passed
  gate 1 and is not merged, because generated copies bound to asserted counts would go stale at
  the first change of an entry or hold that change back.
- **P62, the reading of which rows the open places need** (G140). Drafted and not sent. It runs
  after P60's run is out and before P61's build, as a ruler build on a branch of its own that
  is set aside by tag after its receipt `p62_receivers.txt`, with no pull request.
- **Live runs.** Read `python3 tools/runs.py status` on the PC at the take-over. The PC's
  session of this thread is stopped once its work in progress is pushed, and the next thread
  starts its own.

## 3. Guesses fixed and not yet read

All three blocks, with their rules, are in [the guess file](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD_receipts/guess_capacity_44_55.txt). The next guess is G141. The
next order is P62 as drafted, then P63.

- **G139 (P60).** The trained opening code 3.3 nats pooled (2.7 to 4.2). The last tick against
  its control: -0.01 at one-place masks (-0.08 to +0.04), -0.02 at whole masks (-0.10 to
  +0.05). Landmarks on the machine's own news at 8 bits: a mean epoch of 3.2 places (2.6 to
  4.2), 0.97 kept under a start seven places later, 0.80 under doubled leading spaces. A
  section's time 1.06 of its control (1.03 to 1.12).
- **G117 (P61).** The seven entries of a site's maps 20 ms a profiled section (13 to 32) from
  56.3. A 64 by 64 forward launch 85 millionths of a second (55 to 130) from 247. An unprofiled
  section 0.885 of its controls (0.85 to 0.93). At 0.9 or more of the transposed and outer
  launches (0.6 to 1.0) every tile's two limbs stand in 64-bit sums. Rules: 25 ms or under
  carries the form to the remaining maps; over 40 the premise failed.
- **G140 (P62).** Open places 0.15 of a section's sites, written rows 0.65 of its pair-terms.
  Open rows alone cost 0.45 nats at one-place masks; open rows with the written landmarks 0.22;
  as many written places at random 0.08 more; the far sources of uncomputed places 0.35. Under
  the landmarks' cut the rows are 0.34, the pair-terms 0.50 and the forward's time 0.58 of
  every row's. The reading is zero-shot, so it sizes and confirms and cannot refute.

## 4. Intent, in order

1. P60 lands: read its pull request at source, merge, score G139 and apply its rule, record the
   result in the design record §4.4a and in the state file.
2. P62's reading: score G140 and apply its rule.
3. P61 lands: read, merge, score G117; at 25 ms or under carry the tile form to the remaining
   maps.
4. The law of the contact's receivers, built on the machine's own news (the design record
   §4.8) and trained from the founded line's state against its control at lap means, with its
   guess, its atlas rows and its statement in #410. It is checked first against the two
   recorded failures that section names.
5. The forward contact's widths as a realization (the engine record §9), after a reading of
   the covector's word, with its guess. About 10 ms a section.
6. The level's second part (the design record §9): its sites, its clock, its phase chart, a
   field of its own, and the length of a region under it, with its cost read against the card
   before any run.
7. The small site kernels and the moments (34.3 and 29.9 ms a section).
8. The engine record §6 listed a row's carrier anchored at its peak with terms released at a
   tolerance. The November 1 record's §14.11 retired that form (no term is released without
   its remainder), and the item is struck with this change. It is never built.
9. The pass over the first 1 GB of the documents store, ordered only once the engine stands
   near its count. A projection of an hour or more is read against the card first.
10. A second specimen through the one program (an image through a third boundary of
    `tools/site_ruler.py`), and the widening of the data as the November 12 records set it.
    Nothing in either branches on the kind of input.

## 5. Readings no log holds

- The occupied bits of the contact's covector word (P54 read every other word).
- The split of a section's rows and of its pair-terms between open and written places (G140).
- The landmarks' epoch on the machine's own news (G139, after P60).
- The share of transposed and outer launches whose tiles prove 64-bit sums, and the width a
  site's maps' outputs need: 64-bit outputs are about two thirds of what a 64 by 64 launch
  moves (`agent-inferred`).
- The commit of the tag `archive/claude/contact-copies`, owed in one sentence in the engine
  record §9.
- Two boxes owed in #410, added from the PC: the nearest quotient that keeps its bits when a
  common even factor leaves numerator and divisor (the engine record §9), and the receivers'
  law when it is built.

## 6. Standing flags

Each is a rule with its reason in the guide ([CLAUDE.md](../../CLAUDE.md), Method and the laws
above it). They are listed because each was raised more than once and fell out between context
windows or threads.

- **A size belongs to its part.** No width, reach or count is reported or reasoned from as the
  machine's. No extent is a copy, a doubling or a pad to a power of two. Entries are given by
  block.
- **"The field" names no one object.** The constitution, a region's current and a receiver's
  locale are kept apart, and a batch is a schedule.
- **A symbol is a word.** Its key on located rings, the rows its rings share, its code length.
  Never a class index into free rows, and an encoding's bytes are not "the letters".
- **One law reads every stream.** Nothing branches on the kind of input, no clock or frame
  length is privileged, and a specimen never stands for the subject.
- **A rate is judged against the card.** A long projection is the realization's defect first.
  The workload is never cut to fit, and learning runs on the card.
- **No one mean speaks for every unit.** A rate, a bar or a projection is given by its
  partition (the forward by site, the return by surprise, each slice apart). Predicted input
  goes dark, unevenly, with landmarks, and cost follows surprise.
- **Search every name before a statement.** A unification is one computation under two
  notations, and the tree has usually stated it already under another discipline's name.
- **Theory picks, and a guess is fixed before its read**, its premise read from the logs and
  the source first. A build is one attempt. A reading is never reported as a success.
- **Widths are declared and never a dial.** No value is "exact". No carrier is anchored at a
  peak with terms dropped.
- **A ruler never becomes machinery.** The count reader's news in P62 is a ruler.
- **Builds, gates and learner runs happen on the PC.** Two builds are timed inside one hold
  against a repeated control. A build enters a line by reproducing it. No run switch carries
  core behaviour.
- **Stores, never caches; no catered machinery.** No authored tokenizer, merge table or
  boundary rule.
- **A reading names its region**, a line's level is read at its lap's mean, and a law is
  judged by structure with the held code as one reading.
- **Outputs are shown whole in conversation and never committed**, and no plan is brought for
  a nod.
