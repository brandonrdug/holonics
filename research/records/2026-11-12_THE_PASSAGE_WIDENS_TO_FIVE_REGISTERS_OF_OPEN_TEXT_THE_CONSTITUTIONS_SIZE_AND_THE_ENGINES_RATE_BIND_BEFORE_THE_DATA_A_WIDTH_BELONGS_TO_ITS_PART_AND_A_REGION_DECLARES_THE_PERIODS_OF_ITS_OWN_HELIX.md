# The passage widens to five registers of open text, the constitution's size and the engine's rate bind before the data, a width belongs to its part, and a region declares the periods of its own helix

Refs #404 #407 #410. Status: [design and measurement; agent-inferred, November 12], written by the
Fable theory thread at Brandon's direction of November 12 (16:13Z). Nothing here is built. The
measurements are count rulers on a cloud host over public data (one shard of Common Corpus, MNIST's
training images); a ruler is an instrument and never machinery. The PC side (the fetch, the
conversion, the lap profile, every learner run) is the circle line's thread's.

Owners named: `hnn::tower::field` (`Region`, the contact's distance, the near field, the strand
mates, the carry circles' scans), the trainer (`field_train.rs`, the passage's record form),
`tools/listener/compose.py` and `examples/listener/sections.rs` (the October 25 boundary charts).
Atlas: `tower.region-helix-periods`, `compression.receiver-family-kernel-antitone`,
`tower.raster-mate-across-a-winding`, `tower.face-lane-composition`,
`compression.value-word-rank-registers`.

Corrected the same day (16:52Z), on Brandon's reading of this record's first draft: the draft said
the constitution held 175,104 entries and that its width took the card's memory. Both were repeated from
a summary line without the code read. The state's material is 80,182 entries (175,104 is the
learner header's count of key draws), and the card's memory follows pairs of sites in a region, not
the width (§4.1). The draft also carried "width 64" as one size of the machine; §4.1 states the
field by part and what a width is.

## 1. The direction, and the failures it works on

Brandon's direction, in the agent's words: the code passage is small and of one kind, and the line
has grown comfortable with it; widen the passage with neutral English and code that he can read and
judge, in slices of Common Corpus (`PleIAs/common_corpus`), never its government slice, at most
about 50 GB; let the demand for data be a demand on the engine; keep the Holonics material for
later, since it reads abstract too early to judge; later still, a passage of the project's own
history in its order of time; and plan multimodality now, since MNIST and the speech set have stood
untouched since October 25. His hypothesis: more than one medium exposes more of the dimensions in
which information compresses, shows as phases and modes of behaviour, and speeds the forming of
connections by its variety.

The recorded failures this plan could repeat, and where each is met:

- **Text run on its codec's grain as the exception** (the lessons' third most repeated). The built
  law (`hnn::tower::field`) is a line's (§6). This is the plan's second subject.
- **A learner shrunk to fit its time** (October 27). The tiers of §4 are set by the constitution's size in
  entries, never by the clock; a pass's time is projected and scheduled as a stated long run.
- **Seen material graded as unseen.** Held documents come from the far end of the shard order and
  share no document with training by a hash of their text (§5).
- **Bits read as progress.** The widened passage is judged by what the attempt writes from held
  prompts, shown whole, by slice; a level is read beside it by slice and by quarter.
- **An authored routine standing in for learning.** Everything medium-specific here is a boundary
  chart: a filter on a row's columns, a fixed grid of windows, a raster's width, a chart of sound.
  No receiver computes an answer.

## 2. What the logs already print

Read before any guess is fixed on this plan (the method's rule).

- **The passage now.** `flytech/python-codes-25k`: 24,557 trained problems, about 11.6 MB, read as
  16.5 million sites a lap; 128 held problems, 43,470 places. te7's lap on the card took 1,268 s:
  about 13,000 sites, or 9.2 KB of passage, a second (the circle line's thread, 16:20Z and 16:35Z;
  G112, PR #714). The state holds 80,182 entries of material (`FIELD_GROW_CARRY … drawn=175104
  material=80182`, the turn carry's receipts; by block in §4.1). The card stands at 10.6 GB of the
  12 GB it is allowed, which is its allocator's budget and no measure of the constitution (§4.1).
- **Trained against unseen.** At te6's lap mean the attempt codes 128 trained problems at 1.621620
  nats a place and 128 withheld ones at 1.676714: 0.0551 apart, and 0.049, 0.054, 0.056, 0.055 and
  0.055 from te2 to te6 (G111, the guess file of the circle line). The lead does not grow.
- **One listener over three media** (October 25, host, a gated tower of width 64): after four
  passes it coded held GSM8K at 2.689 bits a class against its single-medium sibling's 2.572, MNIST
  strokes at 3.084 against 2.984, and speech half-cycles at 3.270 against 2.820
  ([the record](2026-10-25_ONE_LISTENER_HEARS_GSM8K_MNIST_AND_SPEECH_AS_SECTIONS_OF_ONE_PASSAGE.md)).
  Every medium coded worse beside the others than alone.

## 3. The source, read

Common Corpus at revision `307910e4` (last modified 2026-05-06): 10,000 parquet shards,
`common_corpus_{1..10}/subset_{N}_{M}.parquet`, 420 to 450 MB each (433.4 GB in the first directory's
999 listed), one row a document with the columns `identifier, collection, open_type, curator,
license, date, title, creator, language, language_type, word_count, token_count, text`. The card
states 2,267,302,720,836 tokens and 4.49 TB.

One shard was read whole (`common_corpus_1/subset_100_1.parquet`, SHA-256 `4ee719a1…530f07`;
`shard_read.py`): 69,907 rows in one row group, 798.3 MB of text as UTF-8, 217.4 million tokens by
its own column, which is the card's total over 10,000 within 4%. Its rows arrive shuffled, and its
shares by `open_type` stand within a few percent of the card's. [agent-inferred from one shard] So
a run of shards is a fair sample of the corpus, and a slice is a filter on a row's columns.

| `open_type` | Rows | Text, MB | Share | English or code, MB | Largest collections, MB |
|---|---|---|---|---|---|
| Open Culture | 11,626 | 324.7 | 40.7% | 148.1 | English-PD 69.8, US-PD-Newspapers 49.8, French-PD-Newspapers 38.0 |
| Open Government | 21,732 | 233.2 | 29.2% | 150.8 | USPTO 87.5, Chinese-Court-Decisions 32.9 |
| Open Science | 1,912 | 100.9 | 12.6% | 71.7 | OpenAlex 69.0, French-Science-Pile 15.7 |
| Open Source | 20,284 | 89.2 | 11.2% | 89.2 | Github Open Source 89.2 |
| Open Web | 11,233 | 31.4 | 3.9% | 18.2 | Wikipedia 13.1 (2.0 English), StackExchange 10.4, CCC 6.0 |
| Semantic data | 3,120 | 18.8 | 2.4% | (mixed) | Wikidata 18.8 |

**How each slice reads** (rows read by the agent; no text of the corpus is kept here), with a
general compressor as a ruler of how much a byte has to teach (`slice_rulers.txt`, xz at preset 6
on up to 16 MB a slice, bits a byte):

- **Semantic data** is Wikidata as lines of subject, property and value, each entity restated in
  several languages; 0.795 of its bytes are ASCII. xz takes it to 0.94 bits a byte, the lowest of
  any slice. Its name promises meaning and its text is the most repetitive in the corpus, with a
  syntax as plain as TinyStories'. It keeps one use: a value found by its key (subject and property
  given, value open) is the lock and key read at its plainest.
- **Open Source** is whole GitHub files with their licenses: Java 13.9 MB, Python 10.3, JavaScript
  9.7, C# 7.8, PHP 6.7, C++ 6.3, C 4.8, TypeScript 3.2, Go 2.5, Rust 1.7. xz 1.36 bits a byte.
- **Open Web**: Stack Exchange threads (questions, answers and comments with code, 2.14), English
  Wikipedia (2.43), the Creative Commons crawl (articles and reference pages, 2.21). Youtube-Commons
  is machine transcripts of speech with their errors, and is left out.
- **Open Science** is article text from PDFs, sound in its prose and broken in its tables and
  figures, which arrive one number a line (1.82 on OpenAlex's English). A rule on a window's mean
  line length at the boundary removes them (§5).
- **Open Culture**: books read well (2.44 to 2.51); newspapers are OCR of adverts, notices and lists
  of names (2.71), and are left out.

**The slices** [agent-inferred; Brandon's order of priority kept, his "semantic" priority given to
explanatory English, since the slice of that name is triples]:

| Slice | Filter on a row | Yield a shard, MB | Share of the passage |
|---|---|---|---|
| code | `open_type` Open Source, every language | 89.2 | 40% |
| web | Open Web, English, collection Wikipedia, StackExchange or Creative Commons Common Crawl (CCC) | 16.7 | 20% |
| science | Open Science, English | 71.7 (66.3 after §5's rule) | 20% |
| books | Open Culture, English, collection English-PD or US-PD-Books | 89.3 | 12% |
| wikidata | Semantic data | 18.8 | 8% |

Open Government is never taken. The web slice binds: 11.9 shards give 1 GB of the passage, 96
shards give 8 GB (41 GB of transfer, filtered as it streams), and 50 GB would take 597 shards and
259 GB of transfer (`slice_yield.txt`). Shards are taken in the order directory, `N`, `M`, and each
slice takes whole rows in that order until its share is full, so a smaller passage is a prefix of a
larger one and no tier is fetched twice. The manifest holds the revision, each shard's SHA-256 and
the kept rows' identifiers; the text stays under `.local/`.

TinyStories is not used: its language has too little pattern to read a learner by. MNIST and
LibriSpeech (the October 25 listener's media) stay the image and sound terrains.

## 4. How much: the constitution's size and the engine's rate bind before the data

Two readings of §2 decide the amount.

- **Size.** The constitution of the circle line's attempt has 80,182 entries, and the code passage gives it 145 bytes an entry each
  lap. Its lead on trained problems over unseen ones is 0.055 nats a place and has not grown in
  five laps. [from training: a learner's lead on the material it trained on bounds, roughly, what
  more material of the same kind can buy at the same size] So more code of this kind buys about
  0.05 nats a place at most. The level is set by the constitution's size and the built law.
- **Rate.** At 9.2 KB of passage a second, one pass over 1 GB takes about 30 hours and one over
  50 GB about two months.

So the widened passage buys breadth and a legible read at once, and it buys level only where the
field grows, part by part, at the parts whose lack a reading names (§4.1). The card's memory does
not bound that growth: a coordinate of the face costs 100 bytes a site against 260,000 a site at a
mean problem. The demand for data is a demand on the engine twice: sites a second, and bytes of
card a pair of sites.

**The tiers**, each set by the constitution's size and scheduled as a stated run:

| Tier | Passage | Bytes an entry a pass, at 80,182 entries | A pass at 9.2 KB a second | Taken when |
|---|---|---|---|---|
| A | 1 GB, the prefix of B | 12,500 | 30 hours | now: one continuous pass, no repeated laps |
| B | 8 GB, 96 shards | 99,800 | 10 days | fetched now; trained when a pass over it takes under two days (5 times today's rate) and the constitution has grown where §4.1's census names a lack |
| C | 50 GB, 597 shards | 623,600 | 63 days | fetched when B's pass stands; the ceiling, never a target |

A pass of tier A already gives this constitution 86 times the bytes an entry of one lap of the code
passage. The larger tiers wait on its growth, sized by §4.1's law from a reading with its
guess fixed first, and on the engine's rate.

**The prediction to score** (the launcher fixes its numbers before the read): as the passage
broadens at this size, the code passage's held joint rises, as every medium's did beside the others
on October 25; the worth shows as English and code the reader can judge, and as the codes by
slice, not as level on code.

### 4.1 The constitution by part, the card by term, and a width as a composition

Read in the code on November 12 (16:45Z to 16:52Z) after Brandon asked what "width 64 takes 10.6 of
the card's 12 GB" meant, and why the machine was reported with one width. Receipt: `card_octets.py`
(arithmetic copied from `FieldLayout::new` and `read_octets`; it reads no state).

**Names** (corrected the same hour, on Brandon's reading). This record's first draft said "the
field" for three different things, and the guide has barred the word for a realization since
November 9 (a build is one attempt). Here: the **constitution** is the store, 80,182 entries with
their loci, changed only where a covector reaches a locus; a **current** stands over each region;
and each **receiver** (a head's mode at a site, a contact, a place's face) has its own locale, its
support, frame, clock and width. A locus is read by many receivers and a receiver reads through
many loci. An **attempt** is named by its state head (`hnn-field-v14e` on the circle line). The
batch the card's lanes compute together is a schedule and no object of the theory. The module's
name `hnn::tower::field` is the code's and is kept where the code is cited. The declaration's
single integers (one width, one reach, one near radius, one tick count, one alphabet, one base
rate) are the same singular written as law; the width is taken up here, and the rest in the review
pass that follows this record.

**The constitution by part.** The state head is `hnn-field-v14e 100 64 4 8 2 128 4 4 3771 2 0 32`: 100
classes, face width `D = 64` in two lanes of 32, four heads of eight complex modes (`2M = 64` real
modes), 128 pair contacts of which 32 complex contacts are carry circles, four ticks, reach 3,771.

| Block | Shape | Entries |
|---|---|---|
| Pair contacts: the drives `a`, `b` and the return `W` | 128 × 64 each | 24,576 |
| Heads' charts: key, value, probe, out, the moment's chart | 64 × 64 each | 20,480 |
| Letter rows: the encoding, and a letter as the mate before and after | 101 × 64 each | 19,392 |
| Moment rows, before and after | 101 × 32 each | 6,464 |
| Carry charts: turn and leak | 32 × 64 each | 4,096 |
| Readout lift | 64 × 64 | 4,096 |
| Biases, temperatures, paces | | 1,078 |
| All | | 80,182 |

**The card by term** (a training read, which keeps every tick for the return):

- 280 octets for every pair of sites in one region: each kept tick reserves the heads' weights and
  shares at their dense address (`K · H · 8 · 2 = 256`), and the return holds the contact's `δs` and
  one head's covector (24). Only a site's support (its near field and its resonance class) is ever
  written or read; the dense address was chosen on November 1 so that a column's return reads
  `e_ij` without an index.
- 71,486 octets a site in carriers. Of these 6,400 follow the width `D` (100 a coordinate) and
  15,360 follow the contacts.
- At a mean problem (672 sites) the pairs are 188,160 octets a site, 0.725 of the whole, and the
  width's share is 0.025. A region at the reach takes 4.25 GB, 0.937 of it pairs. A 514-site window
  of §5 takes 143,920 a site in pairs.
- The board's 10.6 GB is the budget: the allocator opens with 12 GiB less what the desktop holds
  and a 1 GiB margin, cuts batches at four fifths of it, and keeps freed buffers until the budget
  is reached. By that rule it stands near the budget at any width [read from the allocator's
  source; no profile was read for it].

So the card's memory names its own first waste, the dense pair table, whose cost grows with a
region's length and not with anything learned. The profile (G113) reads the support's
size, the pairs a row meets; a table on the support takes that many entries a row.

**What a width is** (the theory's rule since November 10, atlas `radix.register-composition` and
`code.register-content-by-distance`, from Brandon's corrections of October 31 and November 3, 5,
10 and 12): a width is a need read from a partition and kept as its own expansion; widths add over
branches and multiply along independent registers; growth is a partition sized from a lack, never a
factor; and a width belongs to its part. The built declaration departs from it in three ways.

- **One count is every part's row length.** `FieldDeclaration::width` is the columns of the letter
  rows, of every mode's charts, of every contact's drives and of every circle's charts.
- **It was reached by copies.** The face was founded at 32 and a second lane of 32 was added on
  November 4; the contacts stand at 32, 64 and 128 in turn; the heads are 4, their modes 8, the
  ticks 4. Only the alphabet and the reach are read from the passage.
- **The law can only copy.** `FieldDeclaration::laned` adds a lane as wide as the others
  (`width % lanes = 0` is required), and `grown` multiplies the width, the contacts and the lanes
  by one factor.

The rule was applied to the carriers' bit widths (the row limbs, the number system) and to the
wording of growth. It was not applied to this count, and each lap inherited the declaration because
a build enters a line by reproducing it.

**The face as a composition** (design; agent-inferred; not built; atlas
`tower.face-lane-composition`). The lanes become a composition of the width, `D = w₁ + … + w_L`,
each lane a register of its own length, and each block declares the lanes it reads, so a block's
rows are as long as its lanes together. The chart by lanes already reads each lane as a ratio to
its own power (`lane_chart`), which is what lets lanes differ. The built field is the composition
`(32, 32)` with every block reading both, so the change enters the line by reproducing te7's lap.
Growth is then one move: a lane of the width a reading names is founded beside the trained ones,
read by the blocks whose lack it answers, with every other read from it at zero, so every face is
kept (as `Field::laned` founds a lane now). A lane of 11 coordinates is 11.

**The reading that sizes it** (ordered from the circle line's thread, 16:52Z; host, from saved
states, no card time). The census of directions by block: with four distinct lap means,
`Δ₁ = mean(te4) − mean(te2)` and `Δ₂ = mean(te7) − mean(te5)`, and for each block with its face
side as columns, whole and by lane, the singular values of `Δ₁ᵀ Δ₂` (the travel both spans agree
on; the heat of two disjoint spans cancels in the mean) and `k`, the least count of directions that
hold 15/16 of their sum. A float decomposition on the host is a ruler here. The ruler is
`tools/block_directions.py` (the circle line's thread, the same day), which prints `k` of each span
alone beside it.

The guess, fixed at 16:52Z before the read: the three letter rows each have `k ≤ 16`, and the
widest block's `k` is at least twice the narrowest's. Reasons: the letter rows hold a quarter of
the lasting fall on 2% of the heat (atlas `deposition.block-polarization`), a consistent
travel in few directions; and the count rulers of November 10 read the pair law as a lexicon, which
no small set of classes compresses. Refused if every block's `k` lies within a factor 1.5 of every
other's: then the deposit uses one width, and an unequal need lies by lane or by class and is read
there next.

**The score** (17:38Z; the guess file of the circle line; receipt `g114_block_directions.txt`).
Both parts missed. The letter rows read `k` = 38, 40 and 40 of 64, and the widest block's 40 stands
1.67 times the narrowest's 24. The three blocks under the rest are the three whose moving rows
number 32, which caps `k`. The ruler was then drawn on spans of known kind
(`census_ruler_drawn.txt`): two independent spans of full rank read `k` = 44.6 at 101 rows of 64
columns, 40.9 at 64 rows, 45.4 at 128 and 26.4 at 32. Against its own shape's drawn count each
block stands between 0.78 and 0.95. So every block's travel fills the directions it has, none is
confined, and the census names no block apart from the rest.

Three faults of the guess, all the guesser's. Its reading put a block bound by its row length at
60 of 64 without drawing the ruler, where full rank reads 41 to 46. Its premise took a large share
of the lasting fall on little heat as travel in few directions, and a share of heat says nothing
of rank. And the drawn ruler shows that `k` reads the same for two spans that share their
directions and two that share none (43.1 to 44.7 against 44.6), so it detects a confined column
space and nothing else. The method rule it repeats: before a guess is fixed on a ruler, the ruler
is drawn on a case whose answer is known.

What follows. The composition of lanes stands, since it is the declaration's own defect that it
repairs, and it enters at `(32, 32)`. The census sizes no lane. A lane's width is derived from the
partition its readers hold (atlas `radix.register-composition`) and fixed as its own guess before
its build.

## 5. The form at the boundary

Corrected the same day (17:40Z), after the trainer's region code was read: the first form cut every
document on one grid of 256-byte answers, each with the 256 bytes before it. Under it every answer
would begin at one phase of every ring, every question would have one extent, and a document's end
would fall at a fixed place in a region. A cut is the trainer's, keyed like its other draws, and the
boundary keeps documents.

- **The store** (`tools/corpus_passage.py`, 199 controls in `tools/test_corpus_passage.py`). A slice
  is its documents' bytes one after another, raw, with an index of one row a piece: the document's
  ordinal, the title's octets, the text's octets, and two marks, whether the piece opens its
  document and whether it closes it. No byte is a separator. A document whose text an earlier one
  holds (by SHA-256) is left out and counted.
- **The science slice's rule** stays at the boundary on its own grain: the text is measured on
  windows of 256 bytes and a window whose bytes a line average under 25 is left out (tables and
  figure axes from PDFs: 7.6% of its windows on the shard read, none of the books',
  `slice_yield.txt`). The runs that stay are the document's pieces, which is why a piece carries
  its marks. The 256 is the grain the rule's rate was measured at and no extent of a region.
- **The cut** (the trainer's; agent-inferred design, not built). A piece's stream is its title line
  where it opens, then its text. Answers tile the text: every byte is an answer once. A region is
  an answer and the bytes of the stream before it, its question; a piece that does not open gives
  its first question's bytes to be heard only. The answer's extent and the question's are two
  keyed draws, each an octave of the distance drawn equally often from the near field's `[4, 8)`
  to `[256, 512)` and then a place in it. Reason for the octaves: the contact hears a source `d`
  sites away at `⌊log₂ d⌋` fewer bits, so each cost of hearing is met as often as each other.
  Reason for the top: the card holds 280 octets a pair of a region's sites (§4.1), so a region
  costs its sites squared, and the top octave holds the code passage's median answer, 256 (its
  quartiles are 148, 255 and 495). The draws' mean extent is 108 bytes each, and the cost an answer
  byte `E[(q + a)²]/E[a]` is 752 pairs against the fixed grid's 1,024. The top rises when the pair
  store stands on its support. No cut follows a word, a sentence or a line, so no grammar is
  authored.
- **A true end.** The void follows the last answer of a piece that closes its document. Every other
  region is cut and its answer goes on, as the trainer's cut regions already read. So the length
  law is learned from documents' ends and from nothing a grid placed.
- **The order.** The trainer draws its next piece from the slice of least progress (the text bytes
  cut over the slice's part of the tier), as the October 25 passage interleaved its media, so every
  stretch of the pass holds the mix. The smaller tier is each slice's front documents.
- **Held**: 128 whole documents a slice from the far end of the shard order, sharing no text with
  training or with each other; 128 is the count of the code line's held problems, whose reads'
  spread is on record. How much of a held document a read takes is the read's, cut by the same law
  under a fixed key. The code passage's 128 held problems stay as a sixth held region, so the
  line's level stays readable across the change of passage.
- **The letters.** The built codec's letters are the bytes its first passage used (99 on the code
  passage, and the void), and it refuses a byte it has not met (`field_train.rs`, `FieldCodec`).
  The wider passage needs the chart's letters to grow by arrival: at the crossing into a stretch,
  each byte the stretch holds and the chart lacks is founded as a letter, its rows drawn as a
  founding draws them and its face bias set at the least trained letter's, and the old held read
  is printed before and after. The letter-sized parts are the three letter rows, the read bias,
  the moment rows and the pace. With no new letter the build reproduces te7's lap.
- **The pass** runs from the circle line's state, with no reset, once the letters grow and the
  trainer reads a store by stretches (it reads a passage whole under 64 MiB now). A stretch is
  1,535 sections, the circle line's lap in sections; a stretch's mean of states is read as a lap's
  mean (atlas `tower.field-lap-mean`), by slice and by quarter of open sites.
- **The product read**, every few stretches: one release from a held prompt of each slice, shown
  whole in the conversation.
- **Later passages**, in Brandon's order: the Holonics material once the neutral passage reads well;
  then the project's own history in its order of time (commits, the tree's files, the two harnesses'
  logs and the account exports). That passage is private and stays under `.local/`; its order of
  time is its clock, an aeon's own epochs, and it needs no shuffle.

## 6. A medium is a boundary chart: what the built law takes from one

A text, image, acoustic or motor application is a boundary chart of the elementary objects. Read at
the law's owner, a chart hands a region two things: **letters** (a class at each site, resolved or
open) and **incidence** (which sites are mates). Today the letters are the bytes the code passage
used, 99 of them, and the void (§5), and the incidence is unstated because it is a line. The law names the line in six places (the
module text of `hnn::tower::field`):

| Law | Where the line stands |
|---|---|
| opening | a site's face holds its neighbours' rows, `E₋(u_(t−1))` and `E₊(u_(t+1))` |
| moment | `s_t = Σ_k ζ^(k−t) D(|t−k|) E±(u_k)` |
| support | the near field `0 < |i − j| < 6` |
| contact | a source `d = |i − j|` sites away pays `⌊log₂ d⌋` bits, and a ring's skin decays as `e^(−2π d/n)` |
| pair, triad | the strand mates `t − 1` and `t + 1` |
| carry | a circle scans the strand a site at a time, left or right |

For text this is the terrain's own incidence. For a raster in row order it is not: the pixel one row
up sits `w` sites back, outside the near field, and pays `⌊log₂ w⌋` bits (4 at MNIST's 28) to be
heard at all. That is text's grain inside the law.

**What the neighbour across a row is worth** (`helix_ruler.txt`; counts on MNIST's training images
0 to 49,999, read on 50,000 to 50,499, 392,000 pixels, the October 25 listener's held images; nats a
pixel):

| Mates known | 16 levels | 2 levels |
|---|---|---|
| none | 0.8464 | 0.3782 |
| `t − 1` | 0.5642 | 0.2175 |
| `t − w` | 0.5604 | 0.2079 |
| `t − 1 … t − 4` on the line | 0.5090 | 0.2119 |
| `t − 1`, `t − w − 1`, `t − w`, `t − w + 1` | 0.3824 | 0.1247 |
| both sides, `t ± 1` | 0.3547 | 0.1131 |
| both sides, the line's whole near field `t − 5 … t + 5` | | 0.1060 |
| both sides, `t ± 1` and `t ± w` | 0.2638 | 0.0669 |
| both sides, the eight around | | 0.0580 |

The mate one winding back is worth the mate beside (0.5604 against 0.5642). With both sides known,
as a receiver reads an open site, the four mates on the raster code a pixel at 0.0669 nats where
everything within a line's near field codes it at 0.1060: the two mates across a winding carry 0.039
nats a pixel, over a third of the code, that no site near on the line holds.

## 7. The region's helix

[definition; agent-inferred, November 12; not built] A raster in row order is one strand wound on a
tube: `t = w r + c` is a circle of `w` places with its carry `r` (the raster-is-a-helix point of the
October 16 listener design; the module text of `hnn::tower::field` already reads the contact's `⌊log₂ d⌋` as a wave
on "the strand's ring-wound tube surface"). The winding is the second dimension. So:

- **A region declares the periods of its own helix**, `w₁ | w₂ | …`: none for text; `(w)` for a
  raster of width `w`; `(w, w h)` for frames of `w` by `h`. This is exterior codec information, as a
  region's port is. The law is told a region's incidence, never what the region shows.
- **The mates of a site** are `t ± 1` and `t ± w_k` for each declared period.
- **The distance** `d(i, j)` is the count of pair contacts on the shortest path between two sites on
  the tube: with `j − i = b + w₁ a₁ + w₂ a₂ + …` in balanced digits, `d = |b| + |a₁| + |a₂| + …`.
  With no period it is `|i − j|`.
- **Each law reads the helix**: the near field is `0 < d(i, j) < 6`; a source pays `⌊log₂ d(i, j)⌋`
  bits and a ring's skin decays by `d(i, j)`; a pair contact and a triad take their mates among the
  site's mates, by the contact's index over the region's directions; a carry circle scans along one
  of the region's strands, by its index, and a scan along `± w` is `w` scans side by side; the
  opening and the moment take the mates' rows. The ring phasors stay functions of `t`: a ring whose
  period divides `w` reads the column, and a ring of period `w 2^k` reads the rows.
- **Text declares no period and keeps every bit.** That is the build's receipt on entering the line.
- **A declared period is a ring of its own, and a seam is declared with it.** The turned heads'
  rings are drawn from the dyadic and triadic towers because a line declares no period. A region
  that declares `w` hands its rings `w` and its multiples by the towers, so 28 columns are read as
  28 (`4 · 7`) and nothing is padded to a power of two (the first draft padded MNIST to 32, a width
  the card's towers would have picked). A raster also declares its seam open: a row's last site and
  the next row's first are no mates, so the helix joins no two pixels the image does not. A text's
  line end is a letter and its seam is closed. [design; which slots take a declared ring is owed
  with the build]
- **The cost** is in the support: a near field of radius 5 holds 60 sites on a tube against 10 on a
  line.
- **Located periods come after declared ones.** A code file's indentation, a verse's line and a
  voice's pitch are periods the passage holds and no chart knows. Locating them is the key machine's
  work (a paced head's clock is already its own), and it is the same object: a period of the
  region's helix, found instead of given.

A motor chart stays attached by the same object: a pose is a word of joint screws, and its period is
the count of joints.

## 8. Letters that are values

A text's octet is a letter. A pixel's intensity and a sound's pressure are values, and the precision
law says what a value is: a word of digits in a chosen basis, across registers threaded by a
parameter and chained by carries. [agent-inferred design]

- **A value's word is its registers in the order of their content, and a register exists only
  given the nearer ones** (atlas `radix.register-composition`, `code.register-content-by-distance`).
  The first register separates what the value's own distribution separates first; an atom of that
  distribution (MNIST's zero, 0.81 of its pixels) is a level of its own; past the atoms a digit is
  the value's rank by equal masses, most significant first, so every digit it sends is full.
- **A fixed radix of the raw value is not that word.** By the count ruler `digit_ruler.py` (MNIST,
  nats a pixel with no mate known): one digit of 16 equal steps holds 0.846 of its register's 2.773,
  a fill of 0.31, and 0.34 with its cuts located. The first register, ink or none, holds 0.481 of
  0.693. The second exists at the 0.19 of pixels that carry ink, and there 2, 3 and 4 levels cut at
  equal masses hold 0.693, 1.099 and 1.374 nats an inked pixel, fills of 1.00, 1.00 and 0.99. The
  first draft's page of radix-16 digits is withdrawn.
- **The page is shared by rank.** The alphabet gains the classes of a rank's digits, shared by
  every medium whose letters are values: an image's brightness and a band's level then meet as
  places in their own distributions. The radix of a rank's digit is the page's one choice, and the
  radix economy reads three (atlas `radix.economy`); it is fixed by a ruler on the paired port
  (what the label's code can use) before the chart is built. The octets and the marks stay text's,
  and a text's numeral stays a letter.
- **The chart's cuts are its boundary table.** The table and the digits a chart keeps back are a
  typed remainder at the boundary (the October 25 charts kept an intensity's remainder inside its
  octave the same way), so the chart with its remainder returns the source.
- MNIST's first chart sends ink or none at each of an image's 784 sites, and one rank digit of the
  ink where there is ink.

## 9. Sound

A second of speech at 16 kHz is 16,000 values. The built reach is 3,771 sites, so a region holds
under a quarter second of raw pressure at one digit a value, and an utterance cannot stand beside
its transcript in one region. The October 25 chart (half-cycles, about 4,300 octets a second) does
not change that. Two ways meet, and they are the plan's two subjects again:

- **A boundary chart that folds scale**: a raster of time by octave band, a few hundred sites a
  second, each cell a band's level as a word of digits, the phase and the fine pressure kept as the
  remainder at the boundary. Its width (bands a frame) is a period of the region's helix, so sound
  arrives as an image does, and §7 serves both. The owners to recover from are the half-cycle chart
  in `tools/listener/compose.py` and the pre-reset record of the pressure's dyadic fold
  ([July 21](2026-07-21_THE_SOUND_FOLDS_AS_EXACT_PRESSURE_THE_INSCRIPTION_RIDES_THE_BUTTERFLY.md)).
  The chart's claim, fixed before it is built: with its remainder it returns the pressure at the
  source's width, and the receivers hear only the chart.
- **A longer region**, which is the engine's demand of §4 once more.

## 10. What more than one medium can show

Brandon's hypothesis has a precise form on the objects, one bound, and one measured reading against
its loose form.

- **The form.** Retention is the quotient sufficient for the admitted future: the kernel is the
  differences no admitted receiver tells apart. For receiver families `ℛ₁ ⊆ ℛ₂`,
  `ker ℛ₂ ⊆ ker ℛ₁`, so the retained quotient under `ℛ₂` maps onto the one under `ℛ₁` and has at
  least its dimension; the new dimensions are `ker ℛ₁ / ker ℛ₂`, what the first family could not
  tell apart and the second can. A new medium adds receivers. That is the added dimensionality, and
  it is a statement about the receivers, whatever the constitution's size.
- **The bound.** A joint code is shorter than two separate codes by the information the two share,
  `H(X, Y) = H(X) + H(Y) − I(X; Y)` [from training], and a passage carries `I` only where its
  sections pair the media. For an image and its label `I ≤ log 10 = 2.30` nats an image, 0.0029 nats
  a pixel over 784 sites: the image's own code cannot show it, and the label's code can fall from
  2.30 nats to near none. So what media share is read at the short side of a pair, at its port,
  beside a foil (the label after its own image against the label after another's).
- **The reading against the loose form.** On October 25 unpaired media in one small constitution
  each coded worse than alone. A deposit changes a constitution only by the covectors that reached a
  locus. Where two media reach one locus their covectors add where they agree, and are heat to each
  other where they do not (atlas `deposition.rate-temperature-standing-spread`). Variety speeds the
  modes the media share and warms the rest.
- **What the media share before any pairing** is the navigator's own geometry: the octave ladder,
  the near field, the rings, words within words. A constitution that has met only text can fit those to
  text's grain. This is the near worth of a second medium: it trains the part of the constitution
  that is not letters.
- **Phases and modes.** Five registers of text are already five phases to hold at once (code,
  questions and answers, articles, books, triples). The readings are by slice: the held code, the
  release from a held prompt of each slice (does it keep its register), and the deposit's heat by
  block and by slice (atlas `deposition.block-polarization`): blocks that take heat from one slice
  alone are that phase's, and blocks that take it from all hold what they share.

## 11. The order, and what each step must show

Data and engine (the circle line's thread; #404, #407):

1. **Fetch** tier B as a store of documents (§5) with its manifest; the fetch prints, by slice,
   its documents, pieces, bytes and what the line rule left out, and every store file's hash. Tier
   A is each slice's front documents. The codec is `tools/corpus_passage.py`.
2. **Profile** a lap; the largest entries name the engine's next build. Two figures are kept beside
   every later run: sites a second, and bytes of card a site and a pair of sites (§4.1).
3. **The letters' growth** and **the trainer's read of a store** by stretches with its keyed cut
   (§5), each entering the line by reproducing te7's lap; then **the pass** over tier A from the
   circle line's state, with §4's prediction scored at each stretch's mean, and the product read
   shown whole.
4. **The census of directions by block** (§4.1), scored 17:38Z: both parts missed, every block's
   travel fills the directions it has, and the census sizes no lane. **The face as a composition
   of lanes** enters by reproducing te7's lap at `(32, 32)`; a lane's width is then derived from
   the partition its readers hold and fixed as its own guess. Tier B when its pass takes under two
   days.

More than one medium (planned now, run after the pass has begun):

5. **The region's helix** in `hnn::tower::field` and its card realization. Receipts: a text region
   reproduces the line's lap lines; the parity of card against host on a raster region. Claim, fixed
   before the read: on MNIST sections at one digit a pixel, the same state reads an open pixel with
   its mates on the helix below its read on the line, in the ruler's direction (0.067 against 0.113
   nats at two levels cut at 128 with both sides known is the count ruler's own gap, not the attempt's
   guess).
6. **The rank page** (§8), its radix fixed by a ruler on the paired port first, and MNIST's sections, paired both ways (`image US label RS` and
   `label US image RS`): one open site is recognition, an open image is generation, under one law.
   Claim: the label after its own image codes below the label after a foil's.
7. **The acoustic chart** with its remainder, and LibriSpeech sections paired with transcripts.
8. **The hypothesis's test**: the text slices' held codes with and without the image and sound
   sections in the passage, at equal text bytes. The loose form predicts a fall on text. This plan
   predicts none at this size, a small rise, and the gain read at the paired ports and in the
   field's far reads on text.

## 12. Owed to #410

One box: **a wider receiver family retains more.** For families of readings `F ⊆ G` on one space,
`ker G ⊆ ker F` and the quotient by `ker G` maps onto the quotient by `ker F`
(`Foundation/Standing.lean`, beside the retention quotient). The helix's distance is a definition
with no theorem owed until it has a consumer.

## 13. Receipts

In this record's receipts, all counts on public data, run on a cloud host on one thread (a ruler,
no machine, no learner run): `shard_read.py` and `shard_read.txt` (the shard's census),
`slice_yield.py` and `slice_yield.txt` (the slices' yields and the line-length rule),
`slice_rulers.py` and `slice_rulers.txt` (xz and order-0 codes by slice), `helix_ruler.py` and
`helix_ruler.txt` (MNIST, `train-images-idx3-ubyte.gz`, SHA-256 `440fcabf…523609`), and
`card_octets.py` and `card_octets.txt` (the constitution's entries by block and the card's octets by term,
arithmetic copied from the source at main `8854c9693`), and `digit_ruler.py` and `digit_ruler.txt`
(MNIST, a leading digit's content by radix and cut), and `census_ruler_drawn.py` and
`census_ruler_drawn.txt` (the census's count on drawn spans of known kind, numpy on the cloud
host). The census's own receipt and the two timing reads' are in the circle line's receipts
(`g114_block_directions.txt`, `g113_tp1.txt`, `g113_tp2.txt`, the PC, November 12). No text of the
corpus and no private passage is in the repository.
