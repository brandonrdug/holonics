# The store codes held text at the level of two known neighbours a side: a symbol is a word on rings whose address is located, a code point's coprime residues carry no more than a scramble, and a dark place is the interior of a composite

Refs #404 #406 #407 #410. Status: [measurement, review and design; November 12], by the theory
thread that holds the PC's runs and the engineering. The measurements are the store's held reads
on three states (P49, on the card), one profiled read and the card's two yardsticks (P50 step 0),
and four count rulers on a cloud host over public shards. The symbol's law of §8 is a design,
agent-inferred, and nothing of it is built. Its guess is fixed when its build is ordered, before
any read of that build.

Amended November 12 near 22:50Z, after the first deposit (PR #730) and after the repository's
encoding owners were read at source, which the first deposit had not done: §7.2 gains the read on
the helix's own rings with a control, §8.4 composes a composite where the first deposit founded it by a table,
§8.8 is new (what the repository already held), §10.4 is new (the first repair's read) and §11 is
restated. Each amended passage says so.

Owners named: the store's trainer and its reads (`store_train.rs`: `read`, `write`, `state_of`),
the codec and the layout (`field_train.rs`: `FieldCodec::found`, `FieldCodec::extended`,
`FieldCodec::encode`; `crates/holonics/src/hnn/tower/field.rs`: `FieldLayout`, `Field::lettered`),
the card realization (`crates/holonics-cuda/src/hnn/field.rs`: `CardField::yardsticks`,
`FieldProfile`; `kernels/field.cu`: `field_yard_*`, `contact_body`, and from PR #731
`field_skin_fill`), and the located encoding of October 5 that §8.8 reads
(`crates/holonics/src/compression/keys/transport.rs`: `CarryHelix`, `TransportLocation`,
`LocatedTransport`; `crates/holonics/src/hnn/encoding.rs`: `Encoded`, `PortCell`,
`LocatedAdvances`). Atlas: three rows enter with
this record, `code.neighbour-count-level`, `code.symbol-word-located-rings` and
`code.composite-reach`; `tower.field-engine-count` and `deposition.cost-follows-surprise` are
amended; read with them `radix.register-composition`, `radix.residue-address`,
`radix.digit-shift-spectrum`, `compression.value-word-rank-registers`,
`code.pair-contact-conditional`, `code.capacity-price`, `code.register-content-by-distance`,
`tower.field-growth-by-letters`, `tower.field-support-stride`, `hnn.base-four-byte-boundary`.

Guides: the method rule "A symbol is a word, never a class index with free rows" enters
`CLAUDE.md` and `AGENTS.md` with this record, and the chart "Character sets, code tables, code
lengths" enters the atlas's [charts](../../docs/atlas/CHARTS.md).

Receipts (`..._receipts/`): `neighbour_ruler.py`, `neighbour_ruler.txt`, `symbol_word_ruler.py`,
`symbol_word_ruler.txt`, `symbol_located_ruler.py`, `symbol_located_ruler.txt`,
`symbol_located_ruler_towers.txt`, `composite_ruler.py`, `composite_ruler.txt`; in the passage
record's receipts `store_reads.txt` (P49's reads, writes' rulers and reproduction); in the engine
record's receipts `p50_step0.txt`, `head_profile.py`, `p50_step1.txt` and `reservation_census.py`.
The writes themselves are private text and are in no repository.

## 1. Why this record exists

Three things arrived within two hours of November 12 and belong together.

The store's line had three states (A the crossing, B after 2,001 sections, C after 5,001 sections
of the 1 GB prefix, about 0.08 and 0.2 GB), and P49 read them: the held code by slice and kind,
the count of compared places by octave of surprise, and writes from held prompts by slice. No
state writes language. The question the read leaves is what holds the level.

Brandon read the writes the same hour and saw the backslash escapes in them: bytes of characters
of several bytes, drawn without their partners. His reading of it (21:22Z, in my words; his are
not in git): the machine is still on a primitive alphabet, the bytes of UTF-8; a symbol is a code
word, and its code length is the same thing the precision law calls a width for an arithmetic
symbol; what a character mapping is used for is the arithmetic of the numbers it maps to, their
primality, and a mapping whose arithmetic is unused is only a character map; and he is worried
about the encoding logic for helical code lengths.

The engine's step 0 (a profile by head and the card's two yardsticks) reported, with a forecast
that the first repair's store, at the address I had fixed, would not fit a quarter of the
sections in one batch.

The record answers the three in order: the level (§2 to §4), the symbol (§5 to §9), the engine
(§10).

## 2. The held read, by slice and kind

The held role is 128 documents a slice from a shard the pass never reads. A stretch takes one
keyed state as in training: a mask over the whole stretch, a mask over its run, or a release with
only the context known (k = 0) or with the first k places of the run known. Nats a compared
place, at the mean of states where one exists (`MEAN`; B's is over 100 states, C's over 1,000)
and at the end state where it does not (A):

| slice | places | mask, whole: A | B | C | mask, run: C | context only: C | first k known: C | all: C |
|---|---|---|---|---|---|---|---|---|
| code | 106,856 | 2.747 | 2.423 | 2.385 | 2.400 | 3.380 | 3.318 | 2.960 |
| web | 106,591 | 2.802 | 2.534 | 2.496 | 2.590 | 3.477 | 3.336 | 3.025 |
| science | 105,098 | 3.006 | 2.664 | 2.617 | 2.664 | 3.422 | 3.483 | 3.145 |
| books | 107,336 | 2.683 | 2.411 | 2.379 | 2.450 | 3.203 | 3.110 | 2.848 |
| wikidata | 105,713 | 5.141 | 3.025 | 2.928 | 2.852 | 3.913 | 3.749 | 3.430 |

The partition beside the totals: of a slice's compared places about 26,000 to 27,500 are a whole
mask's, 14,400 to 15,200 a run mask's, 8,200 to 9,100 a release's with the context only and
55,500 to 57,700 a release's with k places known. So about 0.61 of a held read's places are open
places of a release, and a total over all kinds is mostly theirs.

What the read settles, each from its own lines:

- **The step is not the limit.** The mean of states and the end state agree within 0.010 nats a
  place on every slice and kind at C but one (code, all kinds: 2.9596 at the mean, 2.9665 at the
  end; the one is wikidata with the context only, 3.913 and 3.891 on 8,172 places).
- **More text at this rate buys little.** From B to C (0.12 GB more) the whole mask falls 0.03 to
  0.05 nats a place (wikidata 0.10), and a release's far places do not move (code, k = 0, octaves
  2 to 8: 3.32 to 3.55 at B, 3.31 to 3.52 at C).
- **A release reads its nearest places and no farther.** With only the context known, the first
  place of the run codes at 2.31 to 2.55 nats (wikidata 3.10) on 126 to 161 places a slice, the
  next two at 3.22 to 3.35 (books 2.85), and every place from the fourth on at 3.15 to 3.59
  (wikidata 3.75 to 4.31): the level of the slice's own count of bytes (3.16 to 3.51, wikidata
  3.95; §3).
- **The writes agree.** A ruler on the writes at C finds 0.30 to 0.45 of the written strings
  among a slice's words, against 0.75 to 0.97 for reference text and 0.21 to 0.36 for a draw from
  the slice's byte counts (on code the draw finds more, 0.36, than the written text, 0.30). On
  the code line's yardstick the answer codes at 5.37, 5.10 and 5.16 bits a class at A, B and C
  and its context at 0.83, 1.00 and 1.05: the context the code line had learned is coded a
  little worse as open text enters, and the answer a little better.

## 3. A count ruler of known neighbours

A ruler (`neighbour_ruler.py`; a host instrument, a count table that enters no law) asks what a
plain count of a place's nearest known neighbours codes. Its counts are each slice's first 32 MB
of a public shard through the store's own slice rule (web 16 MB, wikidata 20 MB: the shard's
whole share); it reads the held role itself, rebuilt from its public shard (the rebuilt role's
sha256 equals the store's receipt for code, web, books and wikidata; science rebuilt 6,624,256
octets where the store holds 6,642,020, so its row is on nearly the same text and is not checked
equal). The cut and the mask are the pass's law copied (the octaves of a context and a run, the
mask's density drawn as the pass draws it). A place's code is a Witten-Bell count of the class
given its r nearest known neighbours a side, backed off the farthest first.

Nats a compared place under a whole mask, the first 330,000 places a slice:

| slice | the slice's count of bytes | 1 a side | 2 a side | 3 a side | the store at C |
|---|---|---|---|---|---|
| code | 3.459 | 2.833 | 2.492 | 2.333 | 2.385 |
| web | 3.457 | 2.949 | 2.630 | 2.455 | 2.496 |
| science | 3.513 | 2.897 | 2.563 | 2.380 | 2.617 |
| books | 3.162 | 2.644 | 2.347 | 2.174 | 2.379 |
| wikidata | 3.950 | 3.197 | 2.956 | 2.892 | 2.928 |

The store's states stand within 0.13 nats of the count of two known neighbours a side on every
slice: under it on code (0.11), web (0.13) and wikidata (0.03), over it on science (0.05) and
books (0.03). On no slice do they reach the count of three a side (0.04 to 0.24 over it). Under
a run's mask they stand between 0.19 under the count of two a side (wikidata) and 0.19 over it
(books).

The ruler's own partition says where the level comes from. By how many of a place's two
immediate neighbours are known (code, 3 a side): both known, 0.217 of places, 1.10 nats; one,
0.337 of places, 2.01; neither, 0.446 of places, 3.17, and with neither known within two places
3.40, the byte count's level. A mask's code is an average over those three, and a third to a
half of it is places that no near neighbour reaches.

The next place with the whole context known, by how many symbols back the count reads (nats a
place, about 800 places a slice): code 2.75, 2.19, 1.86, 1.77, 1.79; web 2.82, 2.32, 1.91, 1.75,
1.71; science 2.68, 2.31, 1.96, 1.79, 1.77; books 2.52, 2.10, 1.77, 1.53, 1.45; wikidata 2.90,
2.49, 2.43, 2.62, 2.75. The store's first place of a release (2.36, 2.31, 2.31, 2.55 and 3.10, on
126 to 161 places, so about 0.15 either way) reads between one symbol back and two on code, at
two back on web and science, at one back on books and over one back on wikidata. At distance two
and three from the context the count reads 2.65 to 3.01 and 2.92 to 3.35; the store's octave of
those two distances reads 3.26, 3.35, 3.22, 2.85 and 3.32, which is 0.05 and 0.06 over the mean
of the count's two distances on science and books and 0.19 to 0.31 over it on wikidata, web and
code. From the fourth place on the store reads the slice's count of bytes (§2).

**The reading (agent-inferred).** After 0.2 GB the store codes held text as a count of two known
neighbours a side would, within 0.13 nats on every slice, and on no slice as a count of three
would; a word needs more symbols than that, and the writes show none. The step is ruled out by
§2, and a mask has no order of drawing to blame. What holds the level is what the constitution
can hold about a place from its neighbours, and §5 to §9 are about that. Equal codes are not equal knowledge: this says the store codes at a ruler's level,
never that it holds the ruler's law. The check that would say which is a reading owed (§11).

The ruler's price in cells (atlas `code.capacity-price`): on code, two symbols back hold 20,083
contexts and 302,129 pairs, three back 302,129 and 1,123,603, four back 1,123,603 and 2,502,515,
and the fall from three back to four is 0.09 nats for 1.4 million more cells. The store's
constitution is 117,478 entries.

## 4. The dark share, and what cost-follows-surprise needs

The lens of 20:31Z (the engine's record §5) said predicted input goes dark, unevenly, and the
law drawn from it releases a covector under a declared grain. Its premise was to be read first:
the share of compared places by octave of surprise, by slice, on the three states.

Shares of a slice's compared places (B and C at their means of states):

| slice | under 1/16 bit: A | B | C | under 1 bit: C | 8 bits or more: A | C |
|---|---|---|---|---|---|---|
| code | 0.038 | 0.038 | 0.041 | 0.120 | 0.159 | 0.076 |
| web | 0.018 | 0.014 | 0.016 | 0.074 | 0.124 | 0.074 |
| science | 0.013 | 0.010 | 0.012 | 0.061 | 0.143 | 0.085 |
| books | 0.017 | 0.014 | 0.016 | 0.069 | 0.093 | 0.047 |
| wikidata | 0.011 | 0.009 | 0.012 | 0.061 | 0.281 | 0.111 |

The dark share is 1 to 4% of compared places and it moves by under 0.004 from A to C on every
slice. So the law of
`deposition.cost-follows-surprise` has no premise at this constitution: a grain that released
every place under a sixteenth of a bit would spare a return on one place in twenty-five at most.
Two corrections follow.

- **Bright is not learnable.** A release's far place is bright (3.2 to 3.6 nats of surprise) and
  teaches nothing, because the context carries no more about it than the slice's count of bytes
  does. What a place can teach is the excess of the store's code over the code of the best reader
  of the same knowledge, `D(p‖q)`, and the surprise is that excess plus an entropy no deposit
  moves. A law that follows cost by surprise would spend the return on the 0.61 of places that
  are a release's open places. The grain of that law is owed on the excess, read against a ruler
  of the same knowledge, and the row's scope now says so.
- **Where the dark is.** §8.4: a place that its neighbour fully predicts is the interior of a
  composite. The lens's two halves (predicted input goes dark; landmarks are induced into higher
  ranks) are one law, and the dark share is small here because the alphabet holds no composites.

## 5. How a symbol enters today (read at source)

The store's text is UTF-8 and the codec's units are bytes (`Units::bytes()`). `FieldCodec::found`
sorts the byte values a line has met and gives each its rank as its class; `extended` appends the
bytes a crossing meets after the last class in the order met; `encode` maps a byte to its class.
The store's alphabet is 244 classes (the void among them): the code line's 99, then 144 founded
at the crossing (`Field::lettered`, atlas `tower.field-growth-by-letters`).

A class's entries in the constitution are its own: three rows of the face chart's 64 (the
encoding `E` the readout reads, and the two the neighbours' contacts read, `before` and `after`),
its moment rows, its pace on each paced head and its bias, 259 entries a class. 244 × 259 =
63,196 = 2² · 7 · 37 · 61 entries, 0.54 of the constitution's 117,478.

What the index carries: nothing. `A` is 2·32 + 1 and `a` is 3·32 + 1 in the text's own code, the
same residue one winding apart; `7` is 3·16 + 7; a continuation byte of a character of several
bytes is 2·64 plus six bits of payload, and its lead byte says how many follow. The class is the
byte's rank among bytes met, so none of that reaches the machine, no two symbols share an entry,
and a rare byte learns only from its own occurrences. The helical code places a symbol in the
passage (the phase-carried moment `m = Σ_k Ĝ(τ(k))⁻¹E(u_k)` carries where `u_k` stands), and `E(u)`
itself is a free row. In the ten writes read here (two a slice, 2,560 written bytes a state),
bytes that are no valid UTF-8 are 0 at A (a fresh letter's rows open at zero there), 50 at B and
15 at C.

An earlier chart read an octet as a word (atlas `hnn.base-four-byte-boundary`: four base-four
cells an octet, `Base4Bytes`), on a line that is not the store's. The precision law states the
general case for values (a value is a word across registers, an integer carries its
factorization), and the atlas holds it for values (`radix.register-composition`,
`compression.value-word-rank-registers`). It was never applied to the alphabet.

## 6. The lens on the objects

The discipline is coding theory and the character sets of computing; on the objects:

- A **symbol** is a word of the helical code: a strand's address read by receivers' frames as
  residue, winding and epoch. Its **code length** is its word's width, the registers it occupies.
- A **character mapping** is a chart from symbols to integers. What a chart of integers offers a
  machine is their arithmetic: residues on rings, and the fact that coprime rings address an
  integer once modulo their product (atlas `radix.residue-address`). A chart whose arithmetic no
  receiver reads is a table of names.
- The **theorem** taken: functions on `ℤ/M` with `M = Π m_j`, the `m_j` pairwise coprime, are
  the tensor product of the functions on the rings, so a row a symbol is the last term of a
  series whose first terms are rows a ring (§8.1). And Kraft's inequality for the lengths (§8.2).
- **Left behind**: Unicode's numbering and UTF-8's parser as machinery (§7 measures what the
  numbering is worth; §8.6).
- **The test**: §7's rulers before any design, then a guess on the build.

## 7. Three rulers on a symbol's word

All three read one thing: the code of a class given the byte before it, in nats a place, on the
held role's first 330,000 places a slice, with counts from the same streams as §3. Between the
slice's count of classes alone (`order0`) and a free row for each of the 256 byte values (`map`,
a Witten-Bell count) lies what the byte before tells: 0.800 nats on code, 0.625 web, 0.760
science, 0.653 books, 1.154 wikidata. A ruler composes the rows a byte brings its neighbour from
registers, with no term above pairs between a register and the class, `p(x | b) ∝ Π_j F_j[r_j(b),
x]`, fitted to the counts by iterative proportional fitting, and reports the share of that
content it keeps.

**7.1 The code point's own registers** (`symbol_word_ruler.py`). The byte's value split as
winding and residue at a period `m` (`b = q·m + r`), as its eight binary digits, or as its
residues on coprime moduli. The foil is the same split after the byte values the slice met are
scrambled among themselves, four fixed scrambles (their least and greatest in the receipt).

| share kept | rows | code | web | science | books | wikidata |
|---|---|---|---|---|---|---|
| winding and residue at period 32 | 40 | 0.90 | 0.91 | 0.94 | 0.97 | 0.92 |
| the same rows, bytes scrambled | 40 | 0.77 | 0.78 | 0.80 | 0.87 | 0.71 |
| coprime residues (16, 17) | 33 | 0.74 | 0.73 | 0.74 | 0.89 | 0.63 |
| the same rows, bytes scrambled | 33 | 0.74 | 0.77 | 0.78 | 0.87 | 0.68 |
| eight binary digits | 16 | 0.61 | 0.53 | 0.57 | 0.52 | 0.75 |
| the same rows, bytes scrambled | 16 | 0.37 | 0.34 | 0.38 | 0.49 | 0.35 |
| both sides composed at period 32 (1,640 cells for 65,792) | | 0.78 | 0.81 | 0.83 | 0.93 | 0.81 |
| the same cells, bytes scrambled | | 0.59 | 0.58 | 0.58 | 0.74 | 0.38 |

No coprime split of the code point keeps more than a scramble keeps. The receipt holds ten
((16, 17), (13, 20), (11, 24), (9, 29), (7, 37), (5, 7, 8), (5, 7, 9), (3, 7, 13), (3, 5, 7, 11),
(2, 3, 5, 7, 11)) on five slices: of the fifty readings the code point's split codes worse than
every one of its four scrambles on 30, inside their range on 15, and better than all four on 5,
by 0.027 nats at most. The code's power-of-two columns are the only place its arithmetic shows:
at period 32, the column of case and the row of the letter, it codes 0.07 to 0.25 nats better
than a scramble of the same rows. At periods of 2 to 7 the code's own split keeps less than its
scramble on four slices (wikidata is the exception): adjacent code points are unlike symbols.

**7.2 An address located from the counts** (`symbol_located_ruler.py`). Each met byte carries a
residue on each of a few rings; the rows are fitted, then each byte takes, on one ring at a time,
the residue under which its own counts are coded least, and the rows are fitted again, until no
byte moves (5 to 15 rounds). Two starts: the code point's own residues, and a scramble.

| share kept, located | rows | code | web | science | books | wikidata |
|---|---|---|---|---|---|---|
| rings (16, 17), from the code point | 33 | 0.90 | 0.91 | 0.93 | 0.96 | 0.91 |
| rings (16, 17), from a scramble | 33 | 0.90 | 0.90 | 0.94 | 0.96 | 0.93 |
| rings (5, 7, 9), from the code point | 21 | 0.82 | 0.87 | 0.87 | 0.90 | 0.87 |
| rings (5, 7, 9), from a scramble | 21 | 0.84 | 0.85 | 0.87 | 0.92 | 0.89 |
| rings (5, 7), from the code point | 12 | 0.73 | 0.75 | 0.80 | 0.80 | 0.84 |
| rings (5, 7), from a scramble | 12 | 0.74 | 0.75 | 0.81 | 0.79 | 0.83 |
| rings (8, 32) as winding and residue, from the code point | 40 | 0.92 | 0.95 | 0.97 | 0.99 | 0.94 |
| rings (8, 32), from a scramble | 40 | 0.88 | 0.91 | 0.95 | 0.96 | 0.92 |

Three readings. Located, 33 rows keep what the code's best split keeps on 40, and 21 rows keep
0.82 to 0.92. The start does not matter: from a scramble the address reaches the level it reaches
from the code point, within 0.03 nats on the table's coprime rings and within 0.05 on every set
of rings in the receipt, so the code's layout is not needed even as an opening. And the met
bytes share addresses: 178 to 230 met bytes hold 30 to 34 of the 35 cells of
rings (5, 7), 86 to 125 of the 272 of rings (16, 17). To a neighbour most rare bytes are one
symbol.

*The helix's own rings (amended; `symbol_located_ruler_towers.txt`, the same ruler with its ring
sets given as an argument).* The tower's rings are the dyadic and the triadic towers
(`ring_periods`: 2, 4, 8, … and 3, 9, 27, …). Six sets whose product covers the 257 classes, two
of them the towers' own members; each cell is the share kept from the code point's residues and
from a scramble:

| share kept, located | rows | code | web | science | books | wikidata |
|---|---|---|---|---|---|---|
| rings (16, 27) | 43 | 0.91 / 0.93 | 0.92 / 0.93 | 0.96 / 0.95 | 0.98 / 0.98 | 0.92 / 0.92 |
| rings (9, 32) | 41 | 0.91 / 0.89 | 0.93 / 0.90 | 0.96 / 0.95 | 0.98 / 0.96 | 0.92 / 0.92 |
| rings (2, 3, 5, 7, 11) | 28 | 0.85 / 0.87 | 0.89 / 0.89 | 0.91 / 0.90 | 0.95 / 0.95 | 0.90 / 0.90 |
| rings (5, 7, 8) | 20 | 0.84 / 0.84 | 0.85 / 0.86 | 0.87 / 0.86 | 0.91 / 0.90 | 0.87 / 0.88 |
| rings (4, 7, 9) | 20 | 0.82 / 0.82 | 0.85 / 0.85 | 0.87 / 0.85 | 0.91 / 0.90 | 0.88 / 0.89 |
| rings (3, 4, 5, 7) | 19 | 0.83 / 0.82 | 0.83 / 0.84 | 0.85 / 0.86 | 0.91 / 0.91 | 0.87 / 0.89 |
| control, no location: the 41 commonest bytes a row each on (16, 27), every other byte one row | 43 | 0.84 | 0.89 | 0.88 | 0.94 | 0.76 |
| the places those 41 bytes hold | | 0.87 | 0.93 | 0.93 | 0.96 | 0.79 |

The count of rows governs and the choice of rings at a count does not. The helix's own two towers
at the alphabet, (16, 27), keep 0.91 to 0.98 on 43 rows, 0.014 to 0.096 nats a place over the
free map by slice (books least, wikidata most); three or four rings of 19 or 20 rows keep 0.82 to
0.91, and the two sets of 20 rows agree within 0.03. Every location ended with no byte moving, in
5 to 16 rounds, and the two starts end within 0.021 nats of each other on every set. On (16, 27)
the 178 to 230 met bytes hold 103 to 132 of the 432 cells from the code point and 115 to 145 from
a scramble. So the build's rings need no ring the helix lacks.

The control reads how much of that share is a common byte keeping a row of its own. A cell on
the cross of two rings (a residue 0 on one of them) has a free row, so 43 rows give the 41
commonest bytes a row each with one row left for all the others; that alone keeps 0.76 to 0.94.
Location's own part is the difference: 0.04 to 0.16 of the content, which is 0.35 (web) to 0.70
(science) of what the one shared row loses, 0.18 nats a place on wikidata. So most of §7.2's
share is the law of frequencies, and what the composition adds is the rare symbols', which open
on rows their cell's commoner symbols already learned. §7.3's first sentence is read with this
beside it.

**7.3 What the three say together.** A symbol's rows compose from a few rings' rows and keep
nine tenths of a free row's content on an eighth of the rows, when the symbol's address is
located from the text. The Unicode number contributes its columns of 32 and nothing coprime. The
primality the lens asks for is real and is the machine's to locate: it is not in the code table.

## 8. The symbol's law (a design, agent-inferred, unbuilt)

**8.1 The word.** A symbol `u` carries a key `κ(u) = (r_1(u), …, r_J(u))`, `r_j ∈ ℤ/m_j`, the
`m_j` pairwise coprime. By the residue address the key is one address `a(u) ∈ ℤ/M`, `M = Π m_j`.
Each ring holds rows, `F_j[r]` for `r ∈ ℤ/m_j`, and a symbol's encoding is the series

`E(u) = Σ_j F_j[r_j(u)] + Σ_(i<j) F_ij[r_i(u), r_j(u)] + …`,

its terms grouped by the rings they read. The first order holds `Σ_j m_j` rows (`1 + Σ_j (m_j −
1)` free), the second `Σ_(i<j) m_i m_j`, the whole series `M`: a free row an address, which is
what the store holds today with no earlier term. A term is the part of a function on `ℤ/M` that
is constant on every ring it does not name (the characters of `ℤ/M` that are trivial off the
named rings). This is the precision law's storage on the alphabet: a value kept as the terms of
its expansion, grouped over what they share, a term present only where its remainder is read.
§7.2 is the first order's read: 0.90 to 0.96 on rings (16, 17). Every family of a symbol's
entries (the encoding the readout reads, the two the contacts read, the moment rows, the pace) is
such a series on the same key.

**8.2 The length.** With the rings in the order of their content, a symbol's length `ℓ(u)` is the
least `ℓ` at which `(r_1, …, r_ℓ)` is held by no other symbol, its width `Σ_(j ≤ ℓ(u)) log m_j`.
Kraft: `Σ_u Π_(j ≤ ℓ(u)) m_j⁻¹ ≤ 1`. A common symbol holds a cell of the first rings alone and is
short. Symbols that share a cell share those rings' rows and are told apart by a later ring, so a
rare symbol opens with what its cell already learned. A receiver that reads only the first rings
cannot tell a cell's symbols apart, and that difference is in its kernel; the readout, which must
release one symbol, reads every ring. The lengths are read against `−log p(u)` by a ruler on a
state once one exists.

**8.3 The key is located.** A key is a navigator's initial configuration, and learning locates it.
The ruler's routine (a byte takes the residue that codes its counts least) is a host's and never
the machine's. The machine's law is deposition on the key from the covectors that reach it
(picked, agent-inferred; the alternative is a reading): a symbol's rows enter every face that
reads the symbol, so on ring `j` the covector reaching the symbol's row is paired with the ring's
other rows, `g_j(u, v) = ⟨c(u), F_j[v] − F_j[r_j(u)]⟩` summed over the places `u` stood, the
first-order change of the code if `u` stood at residue `v`. The key steps to `v` where that sum
over a declared count of places passes a declared grain: a carry event, discrete as a ring's
winding, carried in the learner's state with its parity of card against host. Spectral placement
(atlas `radix.digit-shift-spectrum`: a ring's order read from the transitions the contacts hold)
is the ruler that reads where a state's keys stand. A fresh symbol opens at the key whose rows
code its first occurrences least, in place of rows at zero.

**8.4 Composites, and where the dark is.** A composite `c` of symbols `u_1 … u_n` (a character of
several bytes, a frequent run) is a symbol of higher rank whose word is its factors' strand:

`E(c) = Σ_k Ĝ(k)⁻¹ E(u_k) + ρ(c)`,

the face the helical code already forms for a run, with a remainder `ρ(c)` founded at zero and
kept only where the factors miss (the three-body part, atlas `code.pair-contact-conditional`).
Its key is located like any symbol's and its length is its own.

A composite stands where a place is dark given its neighbour. A continuation byte is fully
predicted by its lead, the second letter of a frequent pair nearly so: those are the places whose
covector the lens of 20:31Z releases.

*Amended.* The first deposit said here "Founded, the pair is one site" and left the founding to a
count of pairs. A table of pairs at the input is barred, and the repository already says why: the
atlas's chart of tokenizers leaves behind "units as the input codec"; the founded units of
October joined a mark to a digit and spelled one number two ways (atlas `hnn.founded-units`); the
input has been raw bytes since; and in the machine "a unit is a store (a carried state charged by
deposits, leaking by its strides, read through a port), never a table addressed by letters"
(atlas `navigator.unit-composite-move`). So the composite is composed, and the machine holds no
list of composites (agent-inferred, unbuilt):

- A symbol has a stride on a paced clock (§8.8: the pace, a class's own advance). The stride is
  the symbol's width on the place helix. A place the strand predicts advances the clock little
  and keeps what the moment carries; a boundary advances it far and contracts the moment. A host
  ruler on the code passage read the fitted move's multiplier at a modulus of 0.43 for separators
  against 0.86 for the letters of a word (the record of November 10, G32a).
- An **epoch** of that clock is the places between two carries of the accumulated stride `σ` on
  a declared ring. An epoch is a composite: many dark places or one bright one.
- A site of the level above is an epoch. It opens on the moment its epoch composed (the affine
  moves of its places, §8.8, through the chart a site's opening already reads), so `E(c)` above
  is the face the moments already form, and `ρ(c)` is what the level above learns in its own
  rows.

*Amended November 13* ([the design record](2026-11-13_A_LEVELS_SITES_ARE_THE_EPOCHS_OF_ITS_NEWS_BEGUN_AGAIN_AT_EACH_OPENING_ITS_CLOCK_IS_THE_NEWS_BETWEEN_THEM_A_PLACES_NEWS_IS_READ_AT_ITS_CAVITY_FACE_AND_EACH_NAVIGATOR_KEEPS_ITS_LOCATED_CLOCK.md), §4): the clock whose epochs are the level
above's sites is the clock of the places' own news, begun again at each opening, and never a
paced clock's class rates, which stay each navigator's own. An epoch has no row of its own: its
word is the moment its places composed, with a remainder.

The built tower of scales (atlas `tower.field-scale-packets`) is the plain clock's case: a packet
of a fixed six places, whose first reading missed its acceptance and whose record deferred
"packets cut at landmarks". So the lens's law takes its structural form: **a site of the next
rank is an epoch, and an epoch is as long as its places are predicted**; the dark place is not
skipped under a grain, it is inside an epoch, and an epoch of epochs is the lens's higher rank
of crossing classes. The cost follows: the sites of the level above fall as the bytes an epoch
rise (§9: 1.6 to 2.1 bytes a symbol at 256 composites, 2.0 to 2.7 at 1,024). Two things are
open and are the build's first questions. A class's one rate can follow a place's surprise only
in the class's mean, and a blank's stride already reads the face the tick before gave it (the
field record §16.44): whether the stride reads the place's own surprise is not settled. And what
the trained paces hold now is unread (§11). The ruler of §9 founds by count, a ruler's rule.

**8.5 Text, image, acoustic, motor.** A byte of text is a name: its key is located. A pixel's or
a sample's value is an order: its word by rank registers (atlas
`compression.value-word-rank-registers`) is its key's opening, on the same rings under the same
law. A motor chart's serial screw words are words on rings already. Only the boundary codec is
the medium's: bytes in, and a release's bytes out, `decode(encode x) = x`, a composite released
as its factors' bytes and an invalid byte kept as it arrived.

**8.6 What does not transfer.** Unicode's numbering (§7.1: its coprime residues are a scramble's;
its columns of 32 are worth 0.07 to 0.25 nats at 40 rows and location reaches the same from a
scramble). UTF-8's parser, a table of merges, a list of words: each would be an authored routine
standing in for what the machine locates. The rulers' hard assignments and merge tables are
instruments.

**8.7 Which recorded failures the design could repeat.** An authored routine standing in for
learning (a merge table or a parser handed to the machine: barred by §8.6). Text run on its
codec's grain as the exception (§8.5 states the same law for values; the image and acoustic
charts are checked before the build). A width as a dial (the rings' periods are read by a ruler
on the state the build opens from, and a ring is added where a remainder is read, never by
doubling). Bits read as progress (the build is judged by what it writes by slice, with the held
code as one reading). A design thought in the programming language (the address is a residue on
rings, never an index into a table). A located cause carried unrepaired into a new consumer
(amended: §8.8; this record's first deposit repeated it).

**8.8 What the repository already held** (amended; read at source after the first deposit). The
first deposit presented §8.1 to §8.3 as new, and the rule it wrote into the guides gave as its
reason that the word had been held for values and never applied to the alphabet. That reason was
wrong. The miss is of "recover before implementing": I searched the atlas for the alphabet's rows
and did not read the encoding's owners.

*October 5* ([the located transport](2026-10-05_THE_LOCATED_TRANSPORT_EACH_OCCURRENCE_STEPS_THE_RINGS_BY_ITS_LOCATED_ADVANCE.md);
`compression::keys::transport`, `hnn::encoding`; atlas `compression.transport-relabelling`,
`compression.code-relabelling-invariance`, `hnn.encoded-located-relabelling`; Lean
`Compression/Relabelling`; [THE_MACHINE](../../docs/THE_MACHINE.md) guard 9). An occurrence of a
symbol steps the rings' one lift by the symbol's located transport,

`ℓ(k+1) = ℓ(k) + A(u_k)`,  `A(u) ∈ ℤ/D`,  `D = Π d_g`, the `d_g` pairwise coprime.

The odometer chart (digits with a carry) and the residue chart (no carry) are two charts of that
one address. `A` is located by loop closure from the equality of occurrences and from nothing a
code table says. The located code length is the same under every relabelling of the exterior
alphabet, and a chart that reads a code's residues breaks that. Its §10: "an exterior code never
becomes a class", and a class is "a port of the receiving ring, its advance the lift's digits,
not an index into a table". `Encoded::through` refuses the byte chart. So §8.1's key is the
residues of `A(u)`, §8.3's "located, never read off a code table" is that record's law, and
§7.1's reading (a code point's coprime residues keep a scramble's share) is its relabelling
theorem seen on open text. Its locator branches an advance over `ℤ/D` (a helix period of at most
2¹² and twelve labels): a small terrain's method, read on rings (2, 3, 5).

*November, the tower* (`hnn::tower::field`; the field record §16.16). The tower takes its classes
on the class sheet: a codec's cell is a class, each its own port. `FieldCodec` ranks the units a
passage uses, and each class holds a row of its own in every family the layout declares for a
class (`FieldLayout::new`: `enc`, `before`, `after`, `read_bias`, `moment_before`,
`moment_after`, `pace`). None of `Encoded`, `LocatedAdvances`, `LocatedTransport` or `PortCell`
is named under `hnn/tower/` or in the trainers. The tower kept October's blindness to labels:
nothing reads a code's arithmetic, so a relabelling changes its code only through the founding's
draws. It dropped the word: a code becomes a class by the codec's rank, and a class indexes
tables of rows, the two forms October's §10 names. Guard 9's tests stand on `hnn::encoding`'s
entries and do not reach the tower.

*What descends.* One family kept October's form, the pace (atlas `tower.field-pace`):
`κ_h(t) = 1 + c_h[u_t]`, a class's own advance of a paced head's clock, located by deposition.
Through it a symbol is already a move. On a paced mode the moment obeys
`s_t = α(u_t) s_(t−1) + β(u_t)`, `α(u) = ζ^(−κ(u)) e^(−2π|κ(u)|/n)`, `β(u) = E±(u)` (atlas
`navigator.content-stride-moment`, whose restricted case the built clocks are), and a run of
symbols is the composed move (atlas `navigator.unit-composite-move`).

*Two readings of one word* (agent-inferred). October's lift carried two things the tower holds
apart: **which** symbol stands (its address, from which its rows compose, §8.1) and **how long**
it is (its stride on the place helix, the pace). A symbol's word is both, an address and a
width; §8.2 reads the second as the first's prefix. The build's law states what locates the
address and what the stride reads.

*What §7's rulers add.* October's reads were small terrains. On open text at the byte alphabet a
first-order series on a located address keeps 0.88 to 0.99 of a free row's first-order content
on 33 to 43 rows, from either start. And they warn: tied at first order, the byte alphabet keeps
less than free rows keep (0.014 to 0.096 nats a place at one byte back on rings (16, 27)), so a
tied byte alphabet is not expected to code better than the store does today. What it buys is
entries (the alphabet's share of the constitution's 117,478 falls from 0.54 to 0.17 on 43 rows
and to 0.09 on 20, an address a symbol beside) and, with them, alphabets that free rows cannot
hold: epochs, samples of 16 bits, pixels.

## 9. A ruler on composites

`composite_ruler.py`, on the same streams. Composites are founded by count, 32 a pass: the most
frequent adjacent pairs of byte or composite symbols, taken so that no symbol is a first of one
taken pair and a second of another. The held text is cut by the same pairs in the same order.
The read: the next symbol's code given the one, two and three symbols before it (Witten-Bell
counts), summed over the held symbols and divided by the held places, so every figure is nats a
byte of the same text.

Nats a byte of held text for the next symbol. The first three columns are bytes alone with one,
two and three bytes known before it; the rest are the next symbol given the two symbols before
it, by the count of composites founded:

| slice | bytes, one back | bytes, two back | bytes, three back | 64 composites | 256 | 1,024 | 2,048 |
|---|---|---|---|---|---|---|---|
| code | 2.742 | 2.210 | 1.880 | 1.882 | 1.735 | 1.651 | 1.628 |
| web | 2.827 | 2.349 | 1.978 | 1.974 | 1.777 | 1.691 | 1.680 |
| science | 2.773 | 2.356 | 2.002 | 1.956 | 1.757 | 1.662 | 1.643 |
| books | 2.512 | 2.108 | 1.780 | 1.764 | 1.571 | 1.491 | 1.486 |
| wikidata | 2.856 | 2.481 | 2.404 | 2.373 | 2.364 | 2.278 | 2.212 |

The held text's bytes a symbol, and the pairs the count holds at two symbols back (a context of
two symbols with the symbol after it):

| slice | bytes a symbol: 64 | 256 | 1,024 | 2,048 | pairs held, two back: bytes | 256 | 1,024 | 2,048 |
|---|---|---|---|---|---|---|---|---|
| code | 1.49 | 1.87 | 2.46 | 2.86 | 302,130 | 1,199,020 | 2,410,654 | 3,055,391 |
| web | 1.43 | 1.82 | 2.35 | 2.71 | 162,900 | 1,037,849 | 2,154,217 | 2,634,232 |
| science | 1.44 | 1.81 | 2.36 | 2.72 | 158,125 | 1,202,363 | 2,905,408 | 3,822,222 |
| books | 1.56 | 2.08 | 2.72 | 3.11 | 171,351 | 1,736,736 | 4,235,458 | 5,370,055 |
| wikidata | 1.32 | 1.60 | 2.03 | 2.26 | 97,440 | 450,316 | 771,563 | 940,170 |

**The reading.** Founding 64 composites buys, at a reach of two symbols, what a third byte of
reach buys (0.002 nats a byte over it on code, 0.003 to 0.05 under it on the others). At 256
composites two symbols back read 0.15 to 0.25 nats a byte under three bytes back on four slices
(wikidata 0.04), and at 1,024 they read 0.23 to 0.34 under (wikidata 0.13), at 1.6 to 2.1 and
2.0 to 2.7 bytes a symbol. Past 1,024 the count ruler stops paying: 2,048 composites buy 0.005
to 0.022 more (wikidata 0.066), and a third symbol back reads no better than two on four slices.
The count's cells are thin there (0.8 to 4.2 million pairs at two back for 16 to 32 MB of
counts), which is the likely cause and is not tested.
Wikidata's triples gain a fifth to a quarter of what the other slices gain at 256 composites.

The cells grow with the alphabet (the second table), which is what §8.1 is for: a composite's
rows are its rings' and its factors', so thousands of symbols do not cost thousands of free
rows. The ruler founds by count on the whole stream at once; the machine founds as it reads,
and what it reaches is its build's read.

## 10. The engine

**10.1 The card's yardsticks** (P50 step 0, PR #729; `field_pass yardstick`, each reading timed
alone to 1.5 s on the RTX 4080 SUPER, 80 multiprocessors, 256 threads a block). Narrow products
(two 32-bit words into a 64-bit sum) from a 64 by 64 map held in shared memory: 1.4625 × 10¹² a
second with one thread a cell, 5.1914 × 10¹² with one thread a 4 by 4 tile. A store of 2²⁸ words
of 32 bits: 5.7247 × 10¹¹ octets a second read in order, 5.1359 × 10¹¹ written in order, and
1.4451 × 10¹¹ gathered eight words at a random entry of a random row of 209 entries (4.516 × 10⁹
gathers a second).

The count restated on them (`tower.field-engine-count`: 4.356 × 10¹⁰ products and 8.891 × 10⁹
octets a section, 40,741 computed sites): the arithmetic's floor is 8.39 ms a section, the
octets' 15.53 ms, their sum 23.9 ms, 0.587 millionths of a second a site. The count's receipt
read 424.8 ms a section: 50.6 times the arithmetic's floor, 27.4 times the octets', 17.8 times
their sum (42, 35 and 19 on the published figures). The bar of 1 millionth of a second a site is
1.70 times the sum of the measured floors. A tile's thread forms a product in 5.0 of the card's
published lane-steps, where the count chose 6.

**10.2 The profile by head, and G116 (d).** Heads 0 and 1 are still and heads 2 and 3 paced. The
forward contact met 14.78, 9.94, 10.01 and 10.93 million pairs a section by head. Of
`field_contact_rows`' 57.69 ms a profiled section the paced heads hold 0.731 (a paced pair 2.0
ns, a still pair 0.58 to 0.69); of `field_contact_columns`' 33.67 ms, 0.706; `field_pace_skin_back`
is theirs alone, 39.78 ms. **G116 (d) fixed 0.78 (0.70 to 0.86) and read 0.731: inside its
range**, above the 0.65 under which step 1 would not be built. A paced pair costs the rows 3.2
times a still pair where the guess's units gave 3.6.

**10.3 The first repair's address, and a miss of G116 (c)'s premise.** G116 (c) held that with a
pair's skins added at 64 octets a pair of sites the batches a section stay 1.00, "about 0.99 GB
on a peak of 7.54". The batch's cut is four fifths of the batch budget, 8,489,376,152 octets at
this open, and 7.54 + 0.99 is over it: on the reservation's arithmetic about 767 of leg 1's
3,000 sections would take two batches. The premise was readable from the line's own lines before
the guess was fixed, and I did not read the cut: a miss of the kind the method rule names (a
guess's premise is read from the logs first). The repair: the skin's store goes on the row's
support (atlas `tower.field-support-stride`, applied to this new store only: a region's stride
`K_r = NEAR_SLOTS + D_r`, reserved `Σ_r S_r K_r` in place of `Σ_r S_r²`, about 0.3 of the block),
ordered as P51 before the dense build was read, with the count of leg 1's sections that would
pass the cut printed and held to zero. G116 (a)'s own rule named the support as the store's next
address; it is now its first. G116 (a), (b) and (c)'s rates stand as fixed and are scored on the
support's build.

**10.4 The first repair's read: every bit kept, a twentieth off a section, and G116 (a) missed**
(amended; P50 step 1 at P51's address, PR #731, merged at `c04b4e68c`; `p50_step1.txt`). A paced
head's skin is formed once a clock by `field_skin_fill` and held at the row's support stride, a
word of 32 bits an entry. The build entered the line by reproducing it: from run 1's state at
section 101, 600 of 600 section lines equal run 2's, and the state and the mean of states at
section 600 equal byte for byte. Batches stay 600 in 600; of leg 1's 3,000 sections none passes
the batch's cut on the support (the largest 8,380,173,670 octets against cuts of 8,489,376,152 to
8,558,424,880), where the dense store would have sent 287 to 765 over it. The skins hold 0.70
of the dense pairs' entries.

In one hold on sections 2,001 to 2,100: control 451.0, the build 427.5, control 450.8 ms a
section, so 0.948 of the control and 10.49 millionths of a second a computed site.

| contact family, ms a profiled section | step 1 | step 0 |
|---|---|---|
| `field_contact_rows` | 39.79 | 57.68 |
| `field_pace_skin_back` | 37.09 | 39.77 |
| `field_contact_l5` and `_l6` | 32.85 | 45.31 |
| `field_contact_columns` | 27.59 | 33.66 |
| `field_skin_fill` | 10.12 | new |
| `field_exposure` | 9.20 | 15.37 |
| `field_spread`, `field_sums`, `field_classes` | 9.57 | 8.90 |
| the family | 166.2 | 200.7 |

**G116 (a) fixed 130 (110 to 155) and read 166.2: missed.** A paced pair's row fell from 2.0 to
1.16 and 1.12 ns, so forming the skin was about 0.87 ns of it where the guess's units put 1.45;
the skin's return keeps 1.7 to 1.8 ns a pair and the columns 0.85. The rule's remedy for a miss
above 155 (the store on its support) is already spent. The reading (agent-inferred, untested):
a still pair's row costs 0.60 and 0.71 ns, at or under the 0.886 ns the gather yardstick gives
the 128 octets of a source's value row, so the still rows already run at the card's gather rate
and the family as a whole, 3.6 ns a pair met, is bound by the octets it gathers. If that holds,
no repair that keeps a pair's octets takes much more from it, phase 1's remaining steps are
worth about a twentieth each, and the levers are the ones the count named for phase 2: fewer
octets a pair (rows at the widths their information needs), a region's rows staged in a block's
shared memory (read in order at 5.7 × 10¹¹ octets a second against 1.4 × 10¹¹ gathered), and
fewer pairs. It is tested before step 3 by a count of each entry's gathered octets a pair from
source against the two yardsticks, with an ablation timed in one hold (§11).

Step 2 (a turn's phases and the moments' skins once a clock) is being built on a forecast read
first: four kept clocks do not fit a batch (12,800 octets a site more: 1,840 to 2,180 of leg 1's
sections would pass the cut), so one store holds the clock in use and the far skins stand in
step 1's store, 1,920 octets a site more and no section over the cut. A value is then formed
twice a clock, where G116 (b)'s derivation said once in place of three times: (b)'s premise does
not hold for the build that fits, and (b) is scored as fixed with that stated.

## 11. What this record does not read, and what is owed

- **Where the store stands against the ruler by pattern.** `read-store` does not partition a
  mask's places by how many immediate neighbours are known, or a release's by distance to the
  nearest known place beyond its first octaves. That partition, on states A and C, says whether
  the store's shortfall is in pairs of near neighbours or in everything past them. Owed as a
  reading, outside any timing hold.
- **A ruler of the same knowledge for the excess** (§4): the grain of a cost-follows-surprise law
  is owed on `D(p‖q)`.
- **The both-sides and located rulers on the constitution's own rows.** §7 reads counts. Whether
  state C's 244 free rows are near a first-order series on a few rings is a ruler on the state
  (spectral placement of the rows the contacts read), owed before the build's rings are fixed.
  *Amended:* not ordered. §7.2's control says why: a share kept on the state's rows would read
  high for rows of any structure (the commonest bytes keep rows of their own on the cross), and
  §8.8 does not expect a tied byte alphabet to lower the held code.
- **What the trained strides hold, and where their carries fall** (amended; the guess G118, fixed
  before its reads). The store's paces by class and paced head, read on the PC's host; then, in
  the cloud on the public held shard, the epochs those paces cut at a mean of six places: the
  code of an epoch's first place over the code of its other places, beside packets of a fixed
  six places and a cut by the code itself. The code line's paces were read on November 11 (G33):
  the newline strode 13.5 against a word letter's 2.7 on one head, "the line is the grain the
  built clocks already cut". G118's rule decides whether the level above is first built on the
  clocks as deposition moves them or on a stride that reads a place's own surprise.
  *Read the same day* ([the record](2026-11-12_A_SYMBOL_IS_A_LENGTH_A_BYTE_IS_A_DIGIT_OF_THE_PASSAGE_A_TEXTS_PRIMES_ARE_ITS_PRIMITIVE_CYCLES_AND_A_STRIDE_IS_READ_AT_ITS_PLACE_AS_THE_NEWS_CLOCK_OF_OCTOBER_HELD.md) §4 to §6): (a) held, (b) missed (1.018 pooled where
  1.10 was fixed), and the rule gives the stride that reads the place. G119 sized it: one
  constant a symbol lifts under half of what the place's own length lifts.
- **Whether the contact family runs at the card's gather rate** (§10.4, amended): each entry's
  gathered octets a pair counted from source against the two yardsticks, and an ablation timed in
  one hold, before step 3.
- **The image and acoustic checks of §8.5**, on MNIST and the chosen acoustic set, by the same
  located ruler on values.
- **Lean.** Owed in #410: the tensor decomposition of functions on `ℤ/M` by the rings a term
  reads, with the count of rows a term; Kraft's inequality for the lengths of §8.2; the first-order
  identity of §8.3 (the sum `g_j(u, v)` is the derivative of the code under moving `u` to `v`
  with the rows held).
- **The build** (amended). A new line (its first build has no lap to reproduce), in this order.
  First G118's readings, which fix what the design may assume of the trained strides. Then the
  design, as its own record with the recorded failures each choice could repeat: the symbol's
  entries as a series on a located address, with October's located transport as its owner's
  ancestor and guard 9's tests extended to the tower's entries; what locates the address (a
  priced move from the covectors that reach a symbol's rows, or a founding by factoring a trained
  state's rows); what the stride reads; and the level above, whose sites are the stride clock's
  epochs, as the successor of the fixed packets. Then the build on the PC, its device line, its
  acceptance (the writes by slice from held prompts, with the held code by slice and kind at lap
  means, and the addresses and strides read by a ruler) and its guess fixed in its order, before
  it is read. It is ordered beside the engine's steps and ahead of any long pass.
  *Restated the same day:* the stride that reads the place and the level above on its epochs are
  the news clock of October 27, built for the earlier tower with its carry law proved in Lean
  (the same record, §7 and §8). The design joins the November tower to it.
  *Written November 13* ([the design record](2026-11-13_A_LEVELS_SITES_ARE_THE_EPOCHS_OF_ITS_NEWS_BEGUN_AGAIN_AT_EACH_OPENING_ITS_CLOCK_IS_THE_NEWS_BETWEEN_THEM_A_PLACES_NEWS_IS_READ_AT_ITS_CAVITY_FACE_AND_EACH_NAVIGATOR_KEEPS_ITS_LOCATED_CLOCK.md)): what the stride reads and the level above;
  the address half is ordered there after rulers on value alphabets.
