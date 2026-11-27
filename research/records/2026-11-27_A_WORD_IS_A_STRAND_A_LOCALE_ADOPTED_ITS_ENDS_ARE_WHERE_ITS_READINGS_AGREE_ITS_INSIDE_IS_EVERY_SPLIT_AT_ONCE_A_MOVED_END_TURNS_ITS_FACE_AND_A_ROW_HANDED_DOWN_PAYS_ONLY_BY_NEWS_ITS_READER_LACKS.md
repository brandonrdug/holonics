# A word is a strand a locale adopted: its ends are where its readings agree, its inside is every split at once, a moved end turns its face, and a row handed down pays only by news its reader lacks

[interpretation at weight 0.7, with twenty-two finite statements in Lean and the guesses G-Z13 to G-Z57 fixed before their reads; the formal thread,
November 27, on Brandon's messages of 07:57, 17:07 and 17:25 UTC and on the lead's score of G-L6 that morning] Status: one law on what a level's unit
is past spelling, its charts (adoption, articulation, reading by prominence, a program's gaps), what it predicts for the strand-face
arm W133s, a second law on why a row handed into her state costs every register and costs most where her face is open,
the form of the level's slow store, and, where her hearing ends, a level that holds its units whole by their own shape, a chain
becoming a part of its own once whole is cheaper than its pieces.

## 1. The lens

Brandon, in my words. He takes Scrabble (and Nigel Richards, who holds a language's word list without speaking it) as an example
of words in text and symbols. A word is split into parts and units in several coarse ways at once, by where the emphasis falls
when it is spoken: "re-gard-ing", "re-ga-rd-ing", "re-gar-ding"; under every split the characters stand as units of their own.
Nobody invents a word: asking for a word's single origin is a broken question, because a word works only where at least two in a
locale agree on it; it exists as a sample, it is taken up by many and propagated or it is not, and it may come up again later
(holarchies and aeons). The same holds of engineering practice and of evolution. The motions of the mouth, throat, tongue and lips
carry meaning, as in onomatopoeia; many common words carry none of their meaning in their sound. Communication throws out a
referent and sees what others hook onto. Parts coarse-grain into sentences and paragraphs as a compression: a reader attends to
the prominent parts, which collocate and let the rest be inferred, rather than reading every part; he reads these replies that
way, and code too, where the sense is the geometry of the gaps (a checkerboard's tiling) more than the modulo that computes it.

## 2. What the tree holds

- **The mass over every split** (`receiver.merge-segmentation-mass`, formal-checked in `Compression/Landmark/Context/Merge` and
  `HNN/FoundedUnitsPrice`). One source read in several alphabets: the mass over its segmentations is a probability law, the
  lattice codes the source at most as any one of its parses (`lattice_code_le_parse`), and a transmitted parse pays
  `−log₂ P(z | D z)` above the lattice, the parse's own conditional cost. A reader that commits one split pays that every time.
- **A unit is founded when it pays for its description** (`hnn.founded-units`; `price_neg_iff_ratio`): a pair becomes a unit
  exactly when the passage's order-one mass grows by more than `2A²`, so a sample met once never pays; recurrence is the price of
  agreement.
- **A level's sites are the landmarks of its news** (`code.site-isolation-landmark`), and the level's unit is the epoch's strand
  face (`tower.level-unit-is-the-epochs-strand-face`): the news cuts a unit's ends, the place count addresses its inside.
- **Reading on the clock of news** (`hnn.tower-news-clock`, October 27): a reader's clock counts its own surprise, so predicted
  places cost it nothing and it spends its turns where the news is. Brandon's correction of November 24 says her reading already
  dwells and skips by surprise in the tree.
- **A symbol is an agreement at a receiver**, settled by least action over configuration states (CLAUDE.md, the comparison rule);
  play is an act answered in kind, and an unanswered act teaches its reader to discount it (record of November 23).
- **A deposit compounds only where a closed unit is kept as a part for the join above it** (`tower.reader-holds-nested-located-cycles`).

## 3. The law

**General physics first.** A string held at both ends rings in many modes at once. Every mode shares the fixed ends; each has its
own nodes inside; where the string is plucked decides which modes sound, the ones whose nodes avoid the pluck. A second body tuned
to a mode rings back and keeps it going, and a mode that nothing answers decays at the string's own quality. The splits of a word
are node sets of different modes of one ringing strand, emphasis is the pluck, and the letters are the finest grid under every
mode. Adoption is resonance between two bodies in one locale: nobody makes the mode, a locale answers it, and an unanswered sample
decays and may ring again when a fitting body comes by (dormancy).

**On the objects (0.7).** A word is a strand a locale has adopted.
1. Its ends are where its readings agree; a level commits a cut only there.
2. Its inside is every split at once: the strand face holds each place at its ring phase from the unit's site, so any split is a
   receiver's reading of the same face, drawn by the mode the receiver drives (emphasis is a pump), and none is the unit's.
3. A unit becomes a part when it recurs enough to pay for its description and a join above takes it; one that no join takes is
   released or waits.
4. A reader spends its turns on the prominent units and infers the predicted stretches between them: the clock of news at the
   level of units.

## 4. The charts

- **Articulation (0.55).** An iconic word is agreed first because both readers already hold the motion: the mouth's turn and the
  referent's motion share one phase law, a key both sides carry before any agreement. Frequency then wears a word down to its
  shortest form that still tells it apart (Zipf's law of abbreviation), which leaves no room for a picture, so the common words are
  the arbitrary ones: addresses, not pictures. For Athena the articulation chart is the tube limb and the coupled speech and text:
  past spelling, a unit is the strand two streams lock on.
- **Scrabble and Nigel Richards.** He holds the spelling level whole with no meaning: his units are agreed by the dictionary, a
  locale's record of adoption, and joined only to the board's gaps, where two words cross at a shared letter (a pair contact).
  That is her level now (the strand face reads an epoch's spelling at 0.94 unrestricted). Past spelling is the join: units fitted
  into gaps a frame leaves.
- **A first sentence (0.5).** A frame of pivots, the frequent adopted units (the, of, and, to, word endings), placed at their
  distances, with open slots filled by fragments that spell: a child's two-word stage, a Scrabble board.
- **A program (0.6).** A program's units are its nested cycles: a block closed by its bracket, a line by its newline, a
  checkerboard's parity a ring of period 2 on each axis. The gaps are the residues, and the modulo is one letter inside them; the
  program is read by the rendering its receiver returns.

## 5. What it predicts for the strand-face arm

W133s (the lead's, from W132's end) puts the level's unit on the epoch's strand face at the level's width of 64, on the fine rings
of periods 2, 3 and 4 counted from the epoch's site, beside its control W133. Inside an epoch the face commits no cut, so the law
asks nothing new there. Its one committed cut is the site, and a site moved by `δ` places leaves all three rings unturned exactly
when 12 divides `δ` (`moved_site_turns_rings`); inside an epoch shorter than twelve places every moved site turns some ring
(`moved_site_inside_epoch_turns`; her epochs average 8.6 places). So one word cut at two sites lands on two faces and its
recurrence splits between them. The prediction: W133s gains where her sites agree with the writers' own cuts (the spaces and first
letters) and fades where her sites fall inside words, and the join takes only epochs that recur.

**The read.** Key every paired read (word presence, the level-unit ruler, the join's codes) by where the epoch's site falls (at a
word's start, inside a word, elsewhere) and by how often the epoch's byte string recurs in her passage (once, 2 to 7, 8 or more),
with the count ruler's ceiling read on the same classes first. G-Z13 (0.5) and G-Z14 (0.55) are fixed in
`receipts/2026-11-26_nested_cycles/GUESS.txt` at 08:05 UTC, before the read.

## 6. A row handed into her state enters at its capacity price (the lead's score of G-L6)

**The reading.** The lead scored G-L6 that morning: W133s held text 0.0291 (±0.0007) nats a place above W133 at lap means, no
region of ten under its control, the word before at a first letter 0.224 against 0.220 and the word two before 0.025 against
0.024, her level's state holding an epoch's bytes at places 1 to 6 at 0.43 to 0.56 against 0.14 to 0.33, the wide panel's lexicon
share 72% against 71%, and her louder (22.691 against 22.655 octaves). Inside the lap the training code's ratio over the control ran
1.046, 1.026 and 1.018 over sections 0 to 249, 500 to 749 and 2,750 to 2,999. G-L5 had cost every register alike in the same way.
With the join's anchor on the level's mean row (§15 of [the nested-cycles record](2026-11-26_A_READER_HOLDS_A_STREAM_AS_NESTED_CYCLES_IT_LOCATES_A_FRAMES_CLOCK_BEATS_AGAINST_ITS_SOURCES_A_LEVEL_IS_READ_BY_ITS_COUNT_IN_ITS_OWN_UNIT_AND_A_DEPOSIT_COMPOUNDS_ONLY_WHERE_A_CLOSED_UNIT_IS_KEPT_AS_A_PART.md)), W132i's join tells little past its prior
(unsaid 0.984 at word starts, 0.960 inside, 0.982 elsewhere), and a planted count join is found at 0.38, so that null is a
ruler's null on real rows and stands.

**The law (0.7).** A row handed into a reader's state enters at its capacity price (`code.capacity-price`) and pays only by news
the reader's own stores lack. The price is flat across registers and louder, because new contacts drive the face before their
content is read; it decays toward the standing spread of those contacts (`deposition.rate-temperature-standing-spread`), never to
zero. The news is local, at the places the row tells something the stores do not hold. G-L5 and G-L6 paid the price and carried
little news: the last epoch's face stands 8.6 places back, inside her own stores' reach of about 30 places
([the record of November 25](2026-11-25_A_REGIONS_FIRST_PLACE_EMPTIES_EVERY_STORE_SO_NO_COMPARED_PLACE_ASKS_A_STORE_FOR_WHAT_STANDS_FAR_BEFORE_IT_A_CUT_COSTS_HER_FORTY_NATS_AND_CONSECUTIVE_STRETCHES_CUT_ONLY_IN_THEIR_SHARP_HEARING_ARE_WHERE_A_STORE_IS_ASKED.md)), so it hands her mostly a copy of what she holds.

**What would pay (0.6).** A level hands down what lies past the reach of the level below it: the level's slow store over many
epochs (its count of units, its reach the product of the strides), never the last epoch's face alone. **The decisive read:** the
arm's code change by place class; any class where the arm codes under its control is the row's news, and the flat rest is its
price.

**The fit and two guesses.** The three training ratios fit `1 + 0.012 + 0.034 (t/125)^(−0.55)` at about 125, 625 and 2,875
sections of the arm's age (three points, thin): a floor near 0.012. G-Z15 (0.55): W134s's last 250 sections read a training code
ratio over W134 between 1.010 and 1.020, so G-L7 (a) misses. G-Z16 (0.5): W134s's held text at its lap mean stands +0.012 to
+0.025 nats a place above W134's. Both fixed at 08:15 UTC, before W134s is read.

## 7. The price is drawn where her face is open (the lead's place-class read)

**The reading.** W133s less W133, paired place by place over the held text's 200,933 places (`tools/place_class_ruler.py`, the
lead's): no class codes under its control. By kind, a word's first letter +0.0546 (±0.0021), other bytes and marks +0.0564
(±0.0025), spaces +0.0185, letters inside a word +0.0180. By the octave of a place's position in its stretch, +0.022 to +0.044,
none under zero, drifting from about +0.035 early to +0.022 past place 512. By the recurrence of the place's word in its stretch,
once +0.0275, 2 to 7 times +0.0206, 8 or more +0.0417, outside a word +0.0361. W132i (the receipt inside the level) has the same
shape: first letters +0.0415, other +0.0358, inside +0.0197, spaces +0.0200. The price is not flat: it is about three times larger
where her own context says least.

**The law (0.7).** A row with no news costs in proportion to how open her face is where it lands. A push `δ` on her logits changes
the written symbol's code by `log Σ p e^δ − δ_u`: to second order `½ Var_p(δ)` under her own face `p`, plus a first-order term
`E_p δ − δ_u` whose spread over the written symbol is the same variance. Inside a word her stores pin the letter, `p` is sharp and
the variance small; at a first letter or a mark her face is broad and the same push moves it most. On a two-way face the variance
is `p (1 − p) (a − b)²`, nothing on a pinned face and greatest at an even one (`two_way_push_variance`,
`two_way_push_variance_le`). In the general physics, a push moves a body most where its stiffness is least: compliance. The same
law takes news most where the face is open, so a row that carries what she lacks pays most at first letters. G-Z18 (0.6): the
change by fifth of W133's own face entropy rises across the fifths, the top at least three times the bottom.

## 8. The level's slow store, its form

**Which store.** The level's own rings on its clock `τ¹`: level 1 is a field on epochs (`tower.field-scale-packets`). Their fade
is the engine's skin, one e-fold a radian (`aeon.count-asks-for-quality`; `agent-inferred` for the level's rings, to be read at
the owner), so a level ring keeps `e^(−2π)` over its own turn and the level holds two or three epochs
(`tower.reach-is-bought-by-depth`: on W101r the epoch before at 0.18 to 0.20, three before at 0.05), inside her own reach of about
30 places.

**The one change.** The level's turned slots take their fades as her own state (`Loci::fade`, built for her fine rings on November
24), opened at one e-fold a turn, where a ring first counts its own turn, because founded at the skin's constant a ring's own
covector hears no count (the lead's records of November 24). A ring of period `n` epochs then reaches about `n` epochs, `8.6 n`
places. Its charge is each closed epoch once, at its strand face (a count crosses the join one for one). The prolongation is
unchanged: `B r̂(x¹_j)` added at each place's news phase, `B` founded at zero; her face's compliance (§7) puts what it carries
where she is open. Far-only repeats already carry about 0.69 nats a place to her by address
(`store.far-price-stands-at-recurrence`); what the store adds is the count and the order of units past her reach.

**Guesses.** G-Z19 (0.6), the premise, read first: on W133s's mean `x¹_j` holds the epoch `k` back under 0.05 for `k` = 4, 8 and
16. G-Z17 (0.55): in that arm less its control, first letters of words last met more than 30 places back stand at least 0.03 nats a
place under first letters of words met within 30. Both fixed at 08:30 UTC.

## 9. The slow store is a bank on the level's clock, never the level's field trained to reach (the lead's reads, 08:50 UTC)

**The reads.** G-Z19 held: after its ticks the level's state holds the bytes at the first three places of the epoch `k` back at
0.16, 0.25, 0.32 (`k` = 0), 0.04, 0.09, 0.11 (1), 0.03, 0.06, 0.09 (2), 0.006, 0.012, 0.020 (4), 0.004, 0.006, 0.010 (8) and
0.003, 0.005, 0.008 (16); before its ticks it holds only its own epoch, at 0.43 to 0.56 (`tools/level_back_ruler.py`). The lead
built the level's fade opened alone (`Constitution::with_level_fade`, founded on W133s's end on all sixteen rings, the host test
the same bits at the old fade) and read it untrained: the epoch 4 back at 0.005 to 0.019, 8 back at 0.003 to 0.006, 16 back at
0.001 to 0.005, and its own epoch down to 0.11 to 0.26. Keyed by site class, the strand face's state holds an epoch's letters about
alike at sites on a word's start (0.45 to 0.63) and inside a word (0.48 to 0.61), and 0.25 to 0.46 at marks and spaces.

**The law (0.7).** A store's reach is its quality, and a field's quality is the least along the path a reading travels. The level's
field moves its state through contacts that slip, mix and dissipate at every tick, so opening its skin left the loss in its
contacts: the opened fade diluted the level's own epoch and carried nothing past four. Training those contacts toward reach would
pay G-L5's and G-L6's price with no premise that they can hold it. The slow store is the strand face one level up, the same program
at every level (`tower.reader-holds-nested-located-cycles`): a bank of rings on the level's clock `τ¹`,
`m²_j = Σ_(i≤j) Ĝ²(τ¹_j − τ¹_i)⁻¹ x¹_i`, charged once per closed epoch by the level's state before its ticks, each ring's fade its
quality. Its only loss is its own fade, so its reach is its construction's. It is a store by the guide's test: charged by the flux
that reaches it, fading by its own law, read through a port (`B`), with no table keyed by content.

**Its form.** Octave periods on `τ¹`, handed at founding and the same for every stream (a gene); each opened at one e-fold a turn,
its fade held as state so deposition can move it; complex at the level's width; beside `x¹` and not in its place, so the current
epoch stays apart; read by `B`, founded at zero.

**What to expect (0.6).** One ring of period `n` holds a weighted bag of its last `n` or so epochs, not their order: read through
its turn, every other epoch in its span stands as crosstalk whose power grows as `n`, so a far epoch reads weakly and the count of
what came reads well. That count is what the first letter of a word last met far back needs (G-Z17). The price will again stand at
first letters and marks (§7); G-Z17 scores whether the news there outruns it. G-Z20 (0.55), the premise, fixed at 08:55 UTC:
founded on W133s's end and untrained, the bank holds the third place's byte of the epoch `k` back at least three times the ticked
level's at `k` = 4 and 8 (0.060 and 0.030 or more).

**G-Z20 held** (the lead's ruler bank on W133s's end, 09:08 UTC; receipt `level_back_bank_W133s.txt`, the lead's). Octave periods
2 to 64 sections of news on `τ¹`, each at one e-fold a turn, charged by `x¹` before its ticks, real and imaginary parts, 768 wide:
the bytes at the first three places of the epoch `k` back read 0.385, 0.515, 0.517 (`k` = 0), 0.369, 0.480, 0.471 (1), 0.173,
0.243, 0.259 (2), 0.103, 0.142, 0.147 (4), 0.054, 0.079, 0.082 (8) and 0.014, 0.026, 0.032 (16): at the third place 7.4 and 8.2
times the ticked level's at `k` = 4 and 8. From `k` = 2 to 8 the third place halves about every doubling of age (0.56 a doubling),
then falls to 0.39 from 8 to 16, the mark of a span ending near the longest ring's reach of about 37 epochs.

**The bank's width.** A ring is as wide as its charge, the level's 64 before its ticks. The count of rings is a partition, read ring
by ring on the ruler bank with the ticked `x¹` beside it: a ring whose drop moves no epoch's presence carries only its price (§7).
G-Z21 (0.55): dropping the period-2 ring lowers the third place at no `k` of 1 to 16 by more than 0.01, its reach of about one
epoch standing inside the level's own ticks. G-Z22 (0.45): adding periods 128 and 256 raises the third place at `k` = 16 by at
least half. Both fixed at 09:12 UTC.

**The rings, one at a time** (the lead's read, 09:23 UTC; the third place's byte of the epoch `k` back at `k` = 1, 2, 4, 8, 16).
Full bank 0.471, 0.259, 0.147, 0.082, 0.032. Dropping the period 2: 0.448, 0.254, 0.149, 0.084, 0.032; 4: 0.429, 0.227, 0.142,
0.084, 0.032; 8: 0.443, 0.227, 0.115, 0.075, 0.032; 16: 0.464, 0.234, 0.130, 0.049, 0.027; 32: 0.477, 0.248, 0.132, 0.069, 0.024;
64: 0.483, 0.255, 0.139, 0.065, 0.013. Periods 2 to 256: 0.474, 0.262, 0.151, 0.071, 0.043; 4 to 256: 0.435, 0.257, 0.154,
0.091, 0.043. G-Z21 missed (the period 2 holds 0.023 at `k` = 1) and G-Z22 missed (0.043 at `k` = 16 against 0.048). Each ring's
drop costs most near the age of its own reach, a ring of period `n` sections of news reaching about `n` of them, `n/1.7` epochs:
the bank is a calendar by the octave of age (`aeon.context-is-a-calendar`), and the read keeps all six. That the bank of 4 to 256
reads `k` = 8 above the full bank is the held read paying each ring's directions in its own variance: a ring pays a price even in
a ruler.

**Before the arm (0.65).** `B_bank` founded at zero enters with no price; it deposits only where a covector reaches it, and the
covector holds a direction only where the bank tells her something, so its price grows at the rate's standing spread and stays drawn
where her face is open (§7). The row of G-L6 cost at once because the level's `B` was already trained when the content of `x¹`
changed under it. Far repeats already reach her by address (`store.far-price-stands-at-recurrence`), so the bank's news is the count
and the far epoch's identity. G-Z23 (0.55): W135b's held text within +0.008 nats a place of W135s's, or under it. G-Z24 (0.5): by
place class, letters inside a word within 0.005 of zero and first letters moving the most. Both fixed at 09:28 UTC.

## 10. The bank's first lap carried no news: its read is mostly its own standing state (the lead's scores, 14:39 UTC)

**The reads** (the lead's record of the class hairs, §18). The strand face's second lap, W134s against W134: the training code's
ratio 1.018 to 1.0145 over the last 250 sections (G-Z15 held, G-L7 (a) missed), held text +0.0221 (±0.0006) with every region up
(G-Z16 held), the word two before 0.025, and by place class the first lap's shape at about two thirds of its size: first letters
+0.0369, marks +0.0363, spaces +0.0204, letters inside +0.0147. The bank's first lap, W135b against W135s from W134s's end: the
training code's ratio 1.0002 to 1.0012 in every block of 250 sections, held text +0.0005 (±0.0002) with every region within 0.0012
(G-Z23 held), `B_bank`'s size a seventeenth of `B⁻`'s, first letters of words last met more than 30 places back +0.0063 (±0.0015)
against −0.0017 (±0.0030) within 30 (G-Z17 missed), letters inside +0.0011 and first letters −0.0003 (G-Z24 half), the word two
before 0.025, and a stretch's first places lower on the arm (−0.0206 at place 0, over 1,009 places).

**The law (0.65).** A store's news is its deviation from its own standing state. The bank is charged with `x¹_j` whole, and `x¹`
carries its mean row, so each ring holds `x̄¹` times its own gain `1/(1 − ρ e^(iω))`, rising from empty at a stretch's start to a
constant. That standing part is most of the bank's read, `B_bank`'s covector is spent on it, and what it buys is a clock of
position in the stretch, which the arm shows at a stretch's first places. The far epochs ride on the deviation, which drives the
deposit weakly. A rate of `B_bank`'s own scales the direction and the walk alike; a lane reads a block against its own power, which
fixes its scale and not its mean; and the face reads her state linearly, so `B_bank` already gives each candidate symbol its own
read of the bank (`B_bankᵀ r_u`). The lever is the charge, the anchor law of §15 of the nested-cycles record: the bank charged with
`x¹_j − x̄¹`, `x̄¹` the level's standing state held by a slow store on `τ¹` (a ring of no turn at the bank's longest fade), so the
rise at a stretch's start goes with it.

**Guesses** (fixed at 14:41 UTC). G-Z25 (0.6): on W135b's mean the bank's standing part holds at least three quarters of the power
of its read over held places. G-Z26 (0.5): at `B_bank`'s locus on a held half (the tension read, `tools/tension_ruler.py`, as in
`deposition.no-linear-tension-at-the-levels-locus`), the bank as charged removes under 0.002 of the fine covector's power at first
letters, and charged against its standing state at least twice that. G-Z27 (0.6): on the second lap, W136b against W136s, first
letters of words last met more than 30 places back stand within 0.005 of zero. If the centered share stays near zero, the null is
the level's own (nothing linear at first order), and the next law is a product, not a charge.

## 11. Nothing linear in the bank is news yet, and the order among units waits on counts at scale (the lead's tension read, 14:58 UTC)

**The reads** (W135b's mean, 407 word rows, the lead's `tools/bank_tension_ruler.py`). G-Z25 held: the standing part, each ring's
response to `x̄¹` through the same turns, holds 0.847 of the charged bank's power (by ring 0.585, 0.546, 0.671, 0.756, 0.823 and
0.882 from the period 2 to 64; 0.855 on W133s's end untrained). G-Z26 missed: read linearly against the covector at the level's
locus, fitted on even rows and read on odd, the bank as charged removes 0.0000 of its power everywhere and at first letters (9,858
places), and centered the same, where a planted tenth reads 0.097 and 0.092. The read takes each place's features through the
constant harmonic alone, so the full form of `B_bank`'s read, the bank at each place's news phase, is not yet read: G-Z28 (0.65)
reads it with one map for each sixth of the phase at first letters and expects under 0.002, a planted tenth at 0.05 or more.

**The law (0.6).** If the full form is null, the bank holds no news at first order because its far content already reaches her by
address: her field's participation carries far repeats (`store.far-price-stands-at-recurrence`, about 0.69 nats a far-only place)
and sums over every match, which is a count, and a product of the bank with her present address would rebuild that participation.
What she lacks is order among units: her join reads an unsaid share of 0.984 at word starts and the count ruler 0.998 on her
epochs, while a planted join is found at 0.38, so on real rows her units hold no order a count can see. Her epochs, cut at her news
landmarks, rarely recur as one string, and a unit becomes a part only when it recurs enough to pay for its description (§3). G-Z29
(0.6): the count ruler's join on the same rows with words as units, cut at the spaces the writers agreed on, reads under 0.9 at word
starts. If it holds, the next law is the level's sites: cut where her readings agree and keep the units that recur
(`hnn.founded-units`), with the bank as that join's operand and its count the join's prior. Both fixed at 14:59 UTC.

**G-Z29 missed, and the clause on units is withdrawn** (the lead's read, 15:01 UTC, `join_count_words.txt`). With words as units
on the same 407 rows the count ruler reads 1.007 at word starts (3.843 nats against the unigram's 3.817), 0.965 inside a word and
0.983 elsewhere: about 30,000 training words give a word bigram nothing to stand on. The null was the ruler's counts, not her units,
and the guess was fixed against a ruler whose ceiling on real rows had not been read, the lesson of G-Z8 again. The first half of
the law stands on G-Z28. The second waits on two reads with counts from the store's own training text read on the same held rows,
by place class and with word first letters apart from inside letters (a unit cut inside a word carries the word's start in its
spelling): words as units (G-Z30, 0.7: under 0.9 at word starts), and her held epochs' strings counted in the same raw text, the
unit before as a string and the unit's places after it (G-Z31, 0.5: within 0.05 of the words' read at word starts). Both fixed at
15:04 UTC.

## 12. The level hands its prediction, on time, and is scored in its own unit (the lead's store count read, 15:15 UTC)

**The reads** (`tools/store_count_ruler.py`, the lead's: 30 MB of the store's web and books in a suffix array, interpolated absolute
discounting, the count depth chosen on the held rows' even half and read on the odd). Words as units: at word first letters 0.997
(the depth the last two bytes; none 1.000, one byte 1.008, four 1.011, the whole unit 1.038), inside a word 0.931, other bytes
1.000; G-Z30 missed. Her epochs (W132i's cut): at word first letters 1.000 (no depth chosen), inside 0.920, other bytes 1.000;
G-Z31 held. By the join's construction a place stands in the unit of the place before it and reads the unit before that, so at a
word's first letter the unit it stands in is the word before, still open, and the read conditions on the word two back alone. The
word directly before tells a great deal by the same counts (after "of " the next byte is "t" in 36% against 6.6% unconditioned),
and her own field holds it.

**The law (0.65).** First, a level hands on one unit late wherever it closes a unit at the next unit's surprise; a word closes at
its own end, where its readings agree (in text the space), and the word before is then handed before the next first letter is
read, though on its own that buys little, since she holds the word before. Second, what a level adds at a first letter is an
interaction, the unit two back read together with the word before; a read on two back alone measures a skip-gram, and the level's
ceiling is the joint count against the count on the word before alone. G-Z32 (0.55), fixed at 15:16 UTC: words as units, the word
before and two back together, at most 0.97 of the word before alone at first letters. Third, the level hands its prediction, not
its state: a face over its next unit formed from the units it holds together, the level's own comparison trained on its own news,
the bank its operand. Its row then carries a density over the next word's spelling, news exactly where her face is open and the
price stands (§7); a state handed down leaves her readers to find the interaction, and the tension reads say first-order readers
do not.

**The measure.** A level's arm is scored in the level's own unit, the mean in nats a place beside it (CLAUDE.md rule 8): the code
of a word (its places summed), split by whether its predictor stands past her reach of about 30 places; and the writes, shown
whole, read for whether a word from the prompt or from 30 places or more back comes back and agrees in what she writes past it. A
mean a place at first letters weighs a level by `1/κ` and hides it.

## 13. A face is worth handing only where it codes her next unit better than her own face does (the lead's question, 15:19 UTC)

G-Z32 missed: at 9,815 word first letters on the odd half, the word before alone codes 3.109 nats against the unigram's 3.803
(0.818), and the word two back with the word before codes 3.109 as well (1.0000). Read by CLAUDE.md rule 11, that is a ruler's
null on depth that has recovered no planted instance: 30 MB of counts are too thin under a pair of words to stand over the word
before alone, so the read prices the instrument and no law of the passage.

The lead asked what makes a level's prediction face worth handing when the face of W101r's receipt, at 2.96 nats a place, coded at
a counted unigram. **The law (0.7):** a face handed down is news to her only where it codes her next unit better than her own face
does at the same places, part by part (§6, §7: a row pays by what her stores lack). W101r's face coded far above her own held code
(about 0.67 nats a place), so handing it could only cost. The same test reaches every count: a count is a reader, and a reader
weaker than she is bounds nothing of hers. The bank as an operand and the density in place of the state are two changes, run as two
arms beside a control (rule 1).

The order the law gives: G-Z33 (0.7), her own code at the same 9,815 first letters at W135s's lap mean, under 3.109 nats; then
G-Z34 (0.6), the level's comparison face with the bank as an operand, fitted on the even half and read on the odd, beating her own
face by 0.05 nats or more in no part split by whether the word was last met past 30 places. A handed face is built only in a part
where it beats hers by more than the scatter between halves; where it beats her nowhere, the level is scored by what it writes and
by its own unit's news (§12), and nothing is handed down.

## 14. A level carries far news only by hearing its units by address (the lead's offset fit, 15:53 UTC)

G-Z34 held and G-Z28 half held. Beside her face renormalized over letters as a fixed offset, the level's 896 features gain +0.0039
where the word was last met within 30 places, +0.0070 past 30 and −0.0007 where it was not met before, each inside its halves'
scatter (0.0131, 0.0083, 0.0023) and the same as letter frequencies alone, while a planted column comes back at +0.331. The full
kron form reads 0.0004 against a planted 0.035. Nothing the level holds at a first letter is news to her.

**The law (0.6).** A level carries far news only by hearing its units by address: a closed unit kept as a part, keyed by its own
word on the level's rings, so that a recurrence charges the rows its earlier meeting charged. The bank on `τ¹` is addressed by
time: a ring's phase moves with every epoch, a word met again forty places on lands at another phase, and the ring holds a bag of
recent strand faces from which no linear or kron reader picks an identity. The premise stands in the atlas since W117
(`store.far-price-stands-at-recurrence`): past her first thirty places a cut's price stands at far-only repeats of runs of three
(1.004 of the net), and her hearing by address brought back 0.310 of it. The far news is in the passage and it is recurrence; the
level needs an address, not a reach. A part keyed by its word is a store by the test of [stores and caches](../../CLAUDE.md#stores-and-caches):
charged at its unit's close, leaking, read through a port, its rows shared at every residue and never a free row a word.

The ceiling is read before a build: G-Z35 (0.55), a host ruler of a leaky count of the row's whole words joined to her face by one
coefficient, gains 0.05 nats or more past 30 places and costs under 0.03 where the word is new, read also by place in the word,
since her address needs a run of three and a recurring word's second and third letters are where a level heard by address pays
most. Under 0.02 past 30, depth does not show at first letters and the level is read whole word by whole word.

## 15. Where her hearing ends, a word held whole pays from its third letter on, and agreement is priced by placement (the lead's joined read, 16:57 UTC)

Her declaration's reach, 3,771 places, is a declared extent: the most sites a region may span, over which the founding builds
each ring's phasor table (`min(period, reach)` residues), and a longer region is refused. It is no aliasing. Her sixteen rings are
the powers of two to 4,096 and of three to 6,561 (`navigator::ring_periods(16, 3771)`), whose phases all return only after
26,873,856 places (`her_rings_alias`). What bounds her hearing is each ring's skin, `e^(−2π d/P)`, one e-fold a radian of turn
(`navigator::skin_of`): a ring keeps `e^(−1)` of a place within `P/(2π)` places (`skin_heard_iff`), about 650 for 4,096 and 1,040
for 6,561, and at a whole period, where its phase first returns, it keeps `e^(−2π)`, about 0.0019 (`skin_at_period`). This section
first read the reach as two coprime rings of 9 and 419 aliasing at their product, from how 3,771 factors and before the
declaration's owner was read; that missed, and so did the same statement in a note to the lead at 16:13 UTC. At
her reach, on sixteen held passages read as 3,700-octet rows against the same text cut into 300-octet rows, a leaky count of the
words met earlier gains past 30 places +0.0028 at a first letter and +0.0271 at the fourth on (G-Z36 missed as a variant), since
her face already holds a recurring word there (its fourth letter on at 0.182 nats). The lead then joined four stretches of each
passage (14,800 places, 180,575 letter places), her face reset at each stretch and the count carried across. Where a word was
last met in an earlier stretch, with no address left in her, her code is 3.02, 1.55, 1.32 and 0.56 nats at the first, second,
third letter and the rest, and the count with its coefficient set by its own state gains +0.0083, +0.0435, +0.229 and +0.290
(scatter 0.0041, 0.0071, 0.005, 0.023); inside her reach the same count gave +0.02 to +0.03 at those letters. The lead's G-J1
held. The level's worth stands where the address law of §14 put it: where the level below no longer hears the word (past its
skins, or across a reset), from the letter on which the prefix tells the word.

The lens of the tensor-spectrum paper of November 24, which Brandon brought (another thread holds its record), composes with this. Agreement
costs the span its holders cover, never how many agree: on a line, the distance between the outermost places, and a copy placed
inside is free (`span_insert_inside`, `span_le_insert`). A word's ends pay and its inside is free (§3). An address is a placement:
the price of a shared bit is the distance between where two places sit. On her rings a place is placed by its age: each heard ring
turns about one radian across its skin, and its phase returns only where its skin has spent the place, so no recurrence of hers
is met by a returning phase. Past the skins of her coarsest rings, or across a reset of her state as in the joined read, a word is
placed only by what carries it farther: a level whose clock counts closed units, where a lag of thousands of places is a lag of
hundreds of units.

**The law (0.65).** The level's part store is a fast contact of the level, deposited by its own closed units: at each unit's
close, the outer product of the unit's strand face with its own terms is charged into a fixed field of the level's width, and the
field leaks at its own rate. At a place, the open prefix's strand face pairs with that field, and the continuation the paired
faces carry is the level's face over the next letter, with her face as the second path (§16). It passes the test of [stores and
caches](../../CLAUDE.md#stores-and-caches): a balance of charge and leak, a read that costs a flux through a port, and rows
shared by every unit, whose number never grows with the units met. Its capacity is its width over its faces' overlap, and the
ruler's ceiling (+0.23 to +0.29 a letter past a reset) is what it can buy at most. Its key, the strand face, pairs as a bag on
the first read; §18 keys it by the carry, the product of the prefix's moves.

The lead read the October 26 coupled bank beside it: a grid of 64 slots written by the delta rule through key and query maps opened
on one draw, which before any learning returned what followed the present face the last time it arrived, and was retired as a
copier, the eighth recurrence of recitation counted as generation. What differs, by the recitation reason: the key is the unit's
own strand face, the machine's encoding, with no maps opened on a draw; the field is of fixed width with shared rows, its own
charge and leak, and a read through a port; and the part is accepted on held text past a reset, beside her writes and their share
of loops, never on a lookup benchmark or on seen material. The premise it must meet: the store line draws stretches of 8 to
1,022 places from random places in documents, so no ring and no level has met a recurrence past about a thousand places in
training, and a part charged inside a stretch could only re-say her address. The part earns its ceiling only where the trainer
walks a document's stretches in order with the part carried across each crossing (a slow variable read at one crossing and joined
at the next, in the learner's state) and the covector reaches it there, which changes the terrain's draw as much as it adds a
part. The guesses G-Z37 to G-Z41 are fixed before either read.

## 16. A chain becomes its own part once meeting it whole costs less than rebuilding it, and a reader keeps both paths (Brandon's lens, 17:07 UTC)

**The lens.** An acronym is a chain compressed into its own unit. "lol" and "lmao" are read as the sounds they make, not unfolded
into their phrases, and they are understood said aloud. A reader new to one takes the longer path, translating it through the full
phrase, and guesses a colloquial one from its context; in science an acronym can mean anything outside its context. Words have
shapes of their own, and a board, like Scrabble's, is a budget that constrains which words fit.

**The law (0.7).** In physics this is a bound state. Atoms that keep meeting in one arrangement move as one molecule; the inside
is still there and shows when the molecule is struck hard enough. A chain of parts becomes a part of its own once meeting it whole
costs a reader less, over its meetings, than rebuilding it from its pieces: the founding price (`hnn.founded-units`, the order-one
mass growing by more than `2A²`). The pieces then stop carrying its meaning: "lol" has a sound of its own, its articulation the
shape it now carries (the onomatopoeia of §1). A reader keeps both paths at once, the part whole and its pieces, and holding both
with equal weight costs at most either path's code and one bit (`two_paths_code_le`; the lattice codes a source at most as any one
parse, `receiver.merge-segmentation-mass`). The fluent reader and the newcomer are one reader at two states of its stores. A short
chain adopted by several locales keeps a plural preimage fibre, one expansion a locale, and the reader's context, its stores and
timings, names the locale and collapses the fibre; in casual speech a locale is shared and the fibre is one. A board's budget is
the receiver's capacity: of the parts a reader holds, only those that fit its ports are drawn.

**For the level.** A closed unit is held as a part keyed by its own shape (§15), beside its pieces as the second path, and the level
founds a chain of its units as a part of its own by the same price. The test on the theory passages: an acronym is written after
its expansion and then alone, and where the level holds the expansion as a part, the acronym's later uses past a reset of her state are coded
at the part's price, while the newcomer's path, her letters alone, codes them as a new word.

## 17. Fitting a chain is a presentation and inverting it is a fibre (Brandon's message, 17:25 UTC)

**The lens.** The bound-state law likely works the same for fitting algebraic cycles and inverting them in general. He asks for
laws in algebraic geometry because he reads the composition of terms and factors, not output numbers: an attention and locale
networking matter. From this section on, a law here is written as a composition of factors first, with its numbers after it as
support.

**The law (0.7).** The parts a locale holds generate a ring, and the locale's relations cut it: `R = k⟨P⟩/I`. A word is an
element `w` of `R`, and its splits are the points of the fibre of the product map `μ : P × ⋯ × P → R` over `w`; `re·gard·ing` and
`re·gar·ding` are two points over one `w` (`regarding_two_splits`, `regarding_splits_differ`), the co-present readings of §3.

- *Fitting* composes: a chain held whole is a generator adjoined with its defining relation, `R[t]/(t − u₁u₂u₃) ≅ R`
  (`adjoin_part_same_ring`). The element is unchanged and only its presentation moves; the fluent reader writes `t`, the newcomer
  `u₁u₂u₃`, and the relation is the decoder they share. A locale adopts `t` where the presentation with it describes the passage
  more briefly than without it by more than the relation costs, the founding price of §16.
- *Inverting* reads the fibre: an acronym is the image of a phrase under the initials map, `π(laugh·out·loud) = l·o·l`. The
  newcomer inverts `π`, whose fibre over `l·o·l` is every phrase of those initials, and the locale's relations cut it to a point;
  each field of science cuts the fibre of its acronyms at its own point.
- *Becoming a word of its own* drops the relation: `lol` keeps `t` and forgets `t = u₁u₂u₃`, a free generator whose meaning is the
  relations it gathers in use (its sound, its company), a new cycle of the locale's ring.

**Its chart in algebraic cycles (0.5).** Writing a cohomology class as a rational sum of cycle classes is the same move, a
presentation of the class by parts, and inverting it, finding which cycles, is a fibre that is plural up to rational equivalence.
For the machine the chart says what a level's part is: a generator adjoined with its relation to the units below, held beside
them (§16), and released from that relation when its own company outweighs its expansion.

## 18. A key binds by a product and a store superposes by a sum (the lead's first read of the part store, 17:28 UTC)

**The read.** The part store of §15 as first written, a word's face `Σ_i ρ(i) ⊗ e(u_i)` charged at each close into a field of `W`
through a fixed orthonormal projection and read by pairing the prefix's face with it, gains nothing in any part at `W` of 64, 128
and 256 with any leak, her letter rows centered or not and one-hot letters too (`tools/part_store_ruler.py`). Her letter rows share
a common part (mean cosine 0.40), the six terms barely separate places, and the pairing of two such faces is a bag of letters,
whose read is a unigram she already beats. The count ruler selected by an exact prefix, a conjunction. G-Z38 misses as read so far.

**The law (0.7), as a composition.** A word is a product in the parts' ring, `w = u₁u₂u₃` (§17), and the strand face is its log,
the linear image of that product. The pairing of two logs is bilinear, `⟨Σ_i a_i, Σ_j b_j⟩ = Σ_ij ⟨a_i, b_j⟩`, so two prefixes
that share any term share credit. The key is the product itself: the carry `χ(p) = Π_i χ_i(u_i)`, a phase on each of `J` circles,
`Φ_j(p) = Σ_i θ_j(u_i, i)`. Two carries pair as `Σ_j cos(Φ_j(a) − Φ_j(b))`, at most `J` and equal to it exactly when they agree on
every circle (`carry_pairing_le`, `carry_pairing_full_iff`), while for distinct prefixes the sum scatters about zero at `√J`.
Exponentiation turns the bag into the conjunction the count ruler drew, and the machine holds it already as the composite move a
prefix makes on her circles (`strand_carries`).

The store: at a word's close, `Σ_k χ(w_<k) ⊗ e(w_k)` is charged into one field that leaks; at a place with prefix `p` the read is
`F · χ(p)*`, the sum over the words held of their weight times `⟨χ(w_<k), χ(p)⟩ e(w_k)`, the ruler's prefix match carried by a
field of fixed width. Its capacity is its count of circles: `N` items stand at a signal over their noise of about `√(J/N)`, and the
leak sets `N`, as a parametron's capacity is its lock count. Guesses G-Z42 (the planted one-hot limit) and G-Z43 (the carried key
at `J` of 1,024 or more) are fixed before the reads.

## 19. A charge is its news, so an address reads a ratio, and two paths join by the store's own confidence (the lead's reads, 17:53 and 18:00 UTC)

**The law (0.75), as a composition.** A summed charge leaves `F χ_a ≈ n_a E[e | a]`, a count that grows with the words sharing the
address, so the empty prefix and the short ones, charged by most words, leak into every read as `n/√(2J)`. The delta charge
`F ← F + η (e − F χ) χ*`, the deposition law's covector `q − p` at the locus it reaches, has its fixed point at the least-squares
map `F = E[e χ*] E[χ χ*]⁻¹`; with near-orthogonal carries `E[χ χ*]` is near the diagonal of the addresses' frequencies, so
`F χ_a → E[e | a]`, each address divided by its own count: the count ruler's prefix ratio, a ratio keeping its denominator. An
address that reads its letter takes no charge (`delta_charge_contracts`, `delta_charge_zero_at_read`), its crosstalk into other
reads falls away, and what noise stands comes from the rare addresses, about `√(N_rare/J)`. A rate of one keeps the last word to
charge an address; a rate under one keeps a ratio over its meetings.

**The second law (0.7).** Two paths join by each one's own confidence: `p ∝ p_her · p_store^λ(s)`, with `λ` read from the store's
state, its read's power at the address, how much it has met the prefix. That `λ` is the store's temperature, a state of the store
and never a dial; a gate set by the place and the read's top octave is a ruler of it.

**The reads, as support** (the joined held passages past a reset, J circles by the letters, mean of the halves). The delta charge
at J = 4,096 from the empty prefix, η = 0.25: +0.0935 at the third letter (scatter 0.0039) and +0.162 after, 0.41 and 0.56 of the
count ruler's ceiling; η = 1: +0.051 and +0.181; at J = 1,024, η = 0.25: +0.083 and +0.118. The two-letter cut that the summed
charge needed adds nothing under the delta charge, which makes that hand-set grain unneeded. One coefficient in place of the
state's gate gives +0.028 and +0.031, a third of it. G-Z44 half held and G-Z45 held. Her own field holds 512 carry circles; G-Z46
reads whether her located turns key the store worse than random ones, which place a prefix by identity where hers place it by
what it predicts. If it holds, the part's key is its own: circles of the level, turned at founding by the unit's identity.

## 20. The part's key is its own, its ends are her epochs read for stability, and the joined covector charges it (the lead's read of her carry gates, 18:50 UTC)

G-Z46 held. Her own carry circles key the delta store at a twentieth and a tenth of drawn circles (+0.0034 and +0.0069 against
+0.067 and +0.074 past a reset, at 512 circles): her turns place a prefix by what it predicts in its context, the letter at a place
explaining 0.22 of a turn's variance on the mean circle, so a word met again in another context composes another carry. The part's
key is its own: circles of the level turned at founding by a unit's symbols and their places, the same at every meeting, a part
founded with drawn operands, its rows `F` located by deposition.

**The ends (0.65).** One law reads every stream, so the unit is the machine's own cut, her epoch, and a letter run is a text
codec's chart; `F`'s rows are her symbol rows `E(u)`. The key `θ_j(u, i)` takes each symbol's place in its unit, so a moved cut
moves every key (§3), and a predicted input goes dark, so a recurring unit's landmark cuts can move. G-Z47 reads the stability
first; where it misses, the store is keyed by the carries of the last `k` places for every `k` up to a unit's length, the same
store with no cut, whose short suffixes the delta charge saturates.

**The join (0.6).** The joined logits are `ℓ = ℓ_her + λ ℓ_store` with `ℓ_store = β F χ`. The field takes the joined face's
covector at its locus, `F ← F + η λ β (q − p_joined) χ*`, whose fixed point is what her face misses, so the part spends its
capacity only on her news, as a handed row pays only by news its reader lacks (§6), and it still saturates where the joined face
reads the symbol. Its confidence is `λ = a ρ(s)`, `ρ` the store's read power at the address and `a` a slope of the constitution,
with `∂L/∂a = ρ (E_p[ℓ_store] − ℓ_store(target))`: the slope rises where the store gives the target more than the joined face
expects. G-Z48 reads the joined charge against the store's own delta.

## 21. Her epochs move between meetings, so the part is keyed with no cut and its depth is located (the lead's epoch read, 19:28 UTC)

G-Z47 missed: her epochs, 3.74 places on the mean, cut a word met again at the same offsets in 0.559 of 4,743 meetings, from 0.67
to 0.75 for short words met near to 0.32 to 0.40 for long words met far, where a predicted input goes dark and its landmarks move.
By §20's branch the part is keyed with no cut: at each place, the carries of the last `k` places, over every byte class.

**The law (0.6).** A suffix address charged once never pays, and its charge is noise of about `√(N/J)` in every other read, so
its depth is located as a chain becomes a part (§16): the address of length `k + 1` is charged only where the address of length
`k` already reads above the field's own noise, a grain taken from the store's own spread and never handed by number. Beside it,
as a ruler, the cap is `k ≤ 8`, two of her epochs: the unit and the one before it, the interaction a level adds (§12). The widths
`J = 4,096` and `J = 512` (her carry word) are read side by side as the part's capacity price. G-Z49 and G-Z50 are fixed.

## 22. Depth is located at the read and never at the charge (the lead's cut-free store at J = 512, 19:50 UTC)

At `J = 512` over every byte class, the store keyed by the last `k ≤ 8` places reaches 0.96 of the word-keyed store at a recurring
word's third letter past a reset (+0.072 against +0.075) and gains more over every byte place (+0.0113 against +0.0078), so the
cut-free key loses almost nothing of the cut one and serves the spaces and the other bytes besides. Depth located on the charge,
deepening only where the parent address read its symbol above `√(n/2J)`, charges an eighth of the addresses and keeps +0.012 of
the +0.072: G-Z50 missed.

**The law (0.65).** A depth charged only where its parent already reads is first charged at a unit's second meeting and first read
at its third, and past a reset most recurring words are met twice, so any gate on the charge puts depth one meeting late. The
store's own balance is the law: every depth up to the cap is charged with its news at the first meeting, a trace never met again
leaks away, and a part is founded by recurrence through the leak, never by a gate on its charge (dormancy is free, `code.rank-one-founding`).
The read locates the depth: an address never met again reads at the field's background, `√(‖F‖²/J)`, a state of the store bounded
by the addresses it holds and its leak, and its slope `g_k + a_k ρ_k` gives it nothing. The cap is located where the fitted `a_k`
falls toward zero, the depth past which suffixes no longer recur within the leak's span. G-Z51 and G-Z52 are fixed.

## 23. A nested store is a flag, and a depth's worth is its slope on its graded piece (the lead's floor arm and slopes, 20:08 UTC)

The floor arm takes the field's own background, `√(‖F‖²/(2J²A))`, a symbol's read at an uncharged carry, as the charge's floor. It
charges 635,131 addresses against k = 1 to 8's 1,892,096 and keeps +0.020 (scatter 0.019) of the +0.072 at the third letter past
a reset, 0.28 of it: G-Z51 held, and the store stands as k = 1 to 8 charged with its news at every depth.

**The composition (0.65).** The address of length `k + 1` fixes the address of length `k`, so the depths' reads lie on a flag

  `F_1 ⊂ F_2 ⊂ ⋯ ⊂ F_8`,   `x_k = ρ_k ℓ_k` read at `F_k`,

and the read the slopes fit is `Σ_k a_k x_k`. Abel summation writes it on the flag's graded pieces `F_k / F_(k−1)`:

  `Σ_k a_k x_k = Σ_k b_k (x_k − x_(k−1))`,   `b_k = Σ_(j ≥ k) a_j`,   `x_0 = 0`

(Lean `flag_slopes_tail_sums`, with `flag_increments_telescope`: the pieces telescope back to the deepest read). The two are one
read with one code and one gain, in two bases. In the basis of the reads, neighbouring depths share all but one place of their
address and trade against each other, which is the alternation of the lead's slopes at `J = 512` (−0.33, −0.40, −0.28, 0.33, −0.51,
0.90, 0.72, 0.28 on the even half). In the flag's own basis, `b_k` is the weight on the news depth `k` adds over depth `k − 1`, and
it is the depth's own worth: 0.71, 1.04, 1.44, 1.72, 1.39, 1.90, 1.00, 0.28 on the even half and 1.63, 0.78, 1.76, 1.89, 0.17,
1.25, −0.18, −0.32 on the odd, positive on both at every depth from 1 to 6 and split at 7 and 8. So `J = 512` locates depth six.
A depth's slope fitted alone takes the shares of every shallower depth with it, and it is a ruler beside this one; `b_1 = Σ a_k`
is the store's whole weight. G-Z53 and G-Z54 are fixed on the tail sums at `J = 4,096`.

**The next composition (0.55).** One slope per depth locates one depth for every address. The context tree locates it at each
address: its weight at a node is the mixture over the standings that stop there or go deeper (atlas
`landmark.context-tree-mixture-over-standings`, Lean `Compression/Landmark/Context/Standing`), and its classical form carries at
each node the ratio of the two codes. On the store that ratio is a store of its own, a stop weight `β` at each depth's carry,
charged at each meeting by the code of stopping there less the code of the deeper read and leaking, read through the same pairing
`⟨B, χ_k⟩` as `F`; the read mixes down the flag by `σ(β)`. It is a store and no cache: its rows are shared, its charge is its news
and its read costs a pairing. G-Z55 is fixed on it. The lead's ruler (20:12 UTC) builds it as `β_k = Re⟨B, χ_k⟩/J`, mixes from
the deepest read up, `M_k = σ(β_k) P_k + (1 − σ(β_k)) M_(k+1)`, and charges `B` by `η (c(M_(k+1)) − c(P_k))`, the tree's Bayes
update in the log chart tempered by `η`, with no leak yet. Where the global form weighs a depth by its own read power, this form
weighs it by its parent's stop weight alone, so at a word's first meetings half of each address's mass goes to a deeper read that
may stand at the background. Depth located at the read repairs it without touching the charge: where depth `k + 1` reads at the
field's background, `M_k = P_k`. G-Z56 is fixed on that one change.

The lead's read (20:37 UTC) scores G-Z55 as missed. Past a reset the stop-weight store gains +0.032 at the third letter, 0.44 of
the global form's +0.072, and it loses at the first and second letters (−0.029, −0.017) and over every byte place (−0.0060). Both
halves took the low edge of each grid (`τ = 4`, `g = 0.5`), so the grid bounds the fit. The loss falls where the dilution reading
put it: on first letters and new words, where every stop weight stands at its prior. A mixture that weighs a depth by a stop
weight alone spends its first meetings learning what the depth's own read power already holds. The read power is the evidence
the address carries, and the stop weight should carry only the news beyond it. Beside it, the word-keyed store at `J = 4,096`
gains +0.095 at the third letter past a reset and +0.088 after it, 0.42 and 0.30 of the count ceiling, and +0.0097 over every
byte place.

**The depths of a flag join by a product, never by a mixture (0.65; the lead's pass-through arm, 20:44 UTC).** Passing the deeper
mixture through where the deeper address reads at its background (`σ√(2 ln A)`, the largest of `A` reads at an uncharged carry)
gives back 0.007 at the third letter (+0.025 against +0.032) and loses more at the first: G-Z56 missed. The shallow face is often
as flat as the deeper one it replaces, so a stop only moves the mass from one flat face to another. The cause is the form of the
join. The global form is a product, `p ∝ q · Π_k P_k^(λ_k)`, and a factor at the background gives every symbol nearly the same
weight, which renormalizes away (Lean `flat_factor_normalizes`): a product pays nothing for an unmet depth. The tree form is a
mixture, `σ P_k + (1 − σ) M_(k+1)`, and a component at or under the face it mixes with gives the target no more than that face
(Lean `mixture_with_flat_le`): a mixture pays its weight's share for every unmet depth. The context tree's mixture is the Bayes
mixture over its standings and is lawful for counts that start at a prior; on a superposed store whose unmet addresses read noise
it pays at every first meeting. So the location per address enters the product's exponent, `λ_k(s) = g_k + a_k ρ_k + β_k(s)`,
`β_k(s) = Re⟨B, χ_k⟩/J`, with `B` charged by `η (E_p[ℓ_k] − ℓ_k(x))`, the exponent's own covector (§20): an address whose read pays
learns a larger exponent, and an unmet one stays flat and costs nothing whatever its weight. G-Z57 is fixed on it.

## 24. Owners

- Lean: `HolonicsResearch/HNN/OwnCycleCells.lean`, `moved_site_turns_rings`, `moved_site_inside_epoch_turns`,
  `two_way_push_variance`, `two_way_push_variance_le`, `span_insert_inside`, `span_le_insert`, `coprime_rings_alias_iff`,
  `her_rings_alias`, `skin_heard_iff`, `skin_at_period`, `two_paths_code_le`, `adjoin_part_same_ring`,
  `regarding_two_splits`, `regarding_splits_differ`, `carry_pairing_le`, `carry_pairing_full_iff`, `delta_charge_contracts`,
  `delta_charge_zero_at_read`, `flag_increments_telescope`, `flag_slopes_tail_sums`, `flat_factor_normalizes` and `mixture_with_flat_le` (checked).
- Atlas: `tower.word-is-an-adopted-strand-cut-only-at-its-ends`, `code.handed-row-enters-at-its-capacity-price`,
  `tower.level-hands-down-its-slow-store`, `tower.chain-becomes-a-part-held-beside-its-pieces` (objects).
- Guesses: `research/records/receipts/2026-11-26_nested_cycles/GUESS.txt`, G-Z13 to G-Z57.
- The engine: the strand-face arm is the lead's (`Scale::strand`, `set-strand`); this record changes no code.
