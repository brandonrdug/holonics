# A word is a strand a locale adopted: its ends are where its readings agree, its inside is every split at once, a moved end turns its face, and a row handed down pays only by news its reader lacks

[interpretation at weight 0.7, with four finite statements in Lean and seven guesses fixed before their reads; the formal thread,
November 27, on Brandon's message of 07:57 UTC and on the lead's score of G-L6 that morning] Status: one law on what a level's unit
is past spelling, its charts (adoption, articulation, reading by prominence, a program's gaps), what it predicts for the strand-face
arm W133s, a second law on why a row handed into her state costs every register and costs most where her face is open,
and the form of the level's slow store.

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

## 10. Owners

- Lean: `HolonicsResearch/HNN/OwnCycleCells.lean`, `moved_site_turns_rings`, `moved_site_inside_epoch_turns`,
  `two_way_push_variance` and `two_way_push_variance_le` (checked).
- Atlas: `tower.word-is-an-adopted-strand-cut-only-at-its-ends`, `code.handed-row-enters-at-its-capacity-price`,
  `tower.level-hands-down-its-slow-store` (objects).
- Guesses: `research/records/receipts/2026-11-26_nested_cycles/GUESS.txt`, G-Z13 to G-Z24.
- The engine: the strand-face arm is the lead's (`Scale::strand`, `set-strand`); this record changes no code.
