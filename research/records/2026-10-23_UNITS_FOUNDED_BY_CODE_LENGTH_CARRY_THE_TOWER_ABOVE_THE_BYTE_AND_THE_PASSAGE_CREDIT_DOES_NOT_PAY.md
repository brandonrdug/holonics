# Units founded by code length carry the tower above the byte, and the passage credit does not pay

Refs #405 #404. Follows [the moment tower learns GSM8K bytes](2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO.md)
(the gated mode, its working law). Status: [definition; agent-inferred, October 23], built and
measured on the host.

## The failure this step works on

After three gated passes over all 6,726 problems the narrow tower codes the 747 held-out problems
at 2.295 bits a byte, and its continuation of the first held-out question is GSM8K-shaped text
that does not compose: question-like clauses in the tone of the training questions, spelt letter
by letter, with misspellings and invented words (the gated tower's samples are below). The
step before this one was read on the bits line alone; the samples did not move with it. Two
candidate causes, each measured here: the learning covector stops at each section's edge, and the
tower composes letters rather than pieces of its passage.

## The passage credit

**Law** (`hnn::tower`, "The passage credit"; atlas `hnn.tower-passage-credit`). Inside a section
the reverse scan carries the covector of a level's recurrence. Across sections the move's
covector is cut at the section's edge. The passage credit carries the recurrence's derivative
moments forward over the passage, so a section's covector reaches the modes, pushes and gates of
earlier sections through the carried state. For a mode with decay `λ_t`, push `γ_t` and input
`x_t`, the derivative of the state with respect to the push row is carried in closed form over a
section of length `T`:

```text
P_T = (Π_t λ_t) P_0 + Σ_s π_s γ_s x_s,      π_s = λ_(T−1) ⋯ λ_(s+1)
W_T = (Π_t λ_t) W_0 + Σ_s π_s d_s x_s       (the gate's drive, d_s = ∂λ_s/∂q_s)
```

with the sum over `s` taken by `outer_sum` (integer addition is associative, so the bits are one
product a cell's), and the products `π_s` by a backward scan. The section's covector is paired with
these moments at its opening.

**Measured.** On all 6,726 problems from the gated runs' founding keys, the credited tower read
2.462 bits a byte held out after pass 1 and 2.342 after pass 2, against the gated tower's 2.435
and 2.321: 1.1% and 0.9% worse. The online code over pass 2 was 2.326 against 2.321. The
certificate halved 26 and 67 times in the two passes, against 21 and 44. From the first held-out
question the credited tower's prompt reads 2.938 bits a byte against the gated tower's 2.555 (both
after pass 2), and its samples (below) compose no better. Decision (agent-inferred, from this measurement):
the passage credit stays built and tested but is not the working law; the gated tower stands.

**A gate rounding fault, located by the credited run.** At the opening of the credited run's
third pass two workers divided by zero: the gate's unit direction `u = λ/|λ|` had been rounded to
the nearest grain, so for a small founded `|λ|` it could fall outside the unit circle, and a
closed gate (`r → 1`, `|λ_t| → 1`) then read `γ_t = √(1 − |λ_t|²) = 0`. The unit is now taken
with a ceiling modulus and truncated quotients, so `|u| ≤ 1` exactly, and a step that reaches
`γ = 0` refuses as a typed refusal ("a gated move reached the unit circle"). The third pass was not
rerun: the credit had already measured worse at two passes.

## Units founded by code length

**Law** (`hnn::units`; atlas `hnn.founded-units`). A unit is a founded adjacent pair of units
standing, and decodes to its bytes. Pairs are proposed by their adjacent count and **accepted
exactly when the complete code falls**: the order-one Krichevsky–Trofimov code of the passage read
in the units, plus the units' description, with the alphabet's growth `A → A + 1` paid by every
context. Frequency only proposes; the price accepts. A refused pair is priced again when its
count changes, and the founding ends when every standing pair has been refused at its count. The
code is exact on `2^(−32)` bits through a `log₂ Γ(k/2)` table built by its recurrence
`L(k + 2) = L(k) + log₂ k − 1`; a price inside the table's enclosure is refused as undecided (none
were). A passage is read by replaying the founded merges in order, and `decode(parse(x)) = x`.
The merge law is `receiver::population::merge`'s (Lean `merge_cost_mass_iff`). The parse is one
path of the segmentation lattice, so its code bounds the lattice's code from above (Lean
`segmentation_code_le`): a reading in the units is never better than the lattice's.

Nothing in the founding is text-specific: it reads a passage of classes, and a quantized image,
acoustic or motor code founds its units by the same price. No unit is authored: the founding
list is read from the training passage and committed with this record (`UNITS`, 8,171 bytes).

**Founded on all 6,726 training problems** (3,528,168 bytes): 1,062 units founded, 86,262 pairs
refused at their counts, 87,324 priced, none undecided, in 2.9 s. The passage reads in 1,342,760
units instead of 3,528,168 bytes; its order-one code falls from 3.535 to 2.385 bits a byte, and
the units' description costs 0.006, so the complete code is 2.391. The most-read units are
`<<` (11,674), `, ` (11,398), `es ` (10,664), `s ` (10,038), ` the ` (8,468), `and ` (8,195),
`#### ` (6,726, once a problem); the longest are `a total of ` (1,460), `number of ` (3,063),
`ree times ` (341), `find the ` (1,046), `because ` (939), `of the ` (3,424). The units are
morphemes, words, word pairs and the answer's markup, founded by the price alone.

## The tower on units

The gated narrow tower (width 64, 64 modes, 256 contacts, 2 levels, 8 streams, sections of 128
units, rate `2^(−7)`, the gated runs' founding keys) reads the 1,318 units as its classes. Its
material grows from 140,544 to 277,542 weights: each founded unit adds its encoding, its readout
row and its bias (1,062 × 129). The held-out problems are parsed by the same founded merges, and
every reading below is the code of the held-out bytes, in bits a byte, so it is the same quantity
as the byte towers'. A unit's region is the region of its first byte.

| tower | held out, passes 1–3 | Q | P | N | M (pass 3) | online, pass 3 |
|---|---|---|---|---|---|---|
| bytes, gated (previous record) | 2.435, 2.321, 2.295 | 2.446 | 2.180 | 2.746 | 1.739 | 2.235 |
| bytes, wide plain (previous record, the PC) | 2.437, 2.326, 2.266 | 2.388 | 2.162 | 2.818 | 1.739 | 2.235 |
| units, gated | 1.953, 1.876, 1.839 | 1.928 | 1.725 | 2.443 | 1.426 | 1.810 |

The unit tower codes the held-out bytes 19.8%, 19.2% and 19.9% below the gated byte tower at each
pass, and below it in every region at pass 3: questions −21.2%, answer prose −20.9%, digits
−11.0%, markup −18.0%. Its first pass reads below the byte tower's third, and below the wide byte
tower's sixth (2.162). The online code over pass 3 (1.810) sits 0.03 below the held-out code.
Every one of the 1,311 sections deposited in every pass, and the certificate halved 3 times, all
in the first 32 sections, against the gated byte tower's 21, 44 and 26 a pass. The tower's online
code (1.810) is 24% below the founding's own order-one code in the units (2.385): the units were
priced by a cheaper receiver than the one that reads them.

A section of 128 units on 8 streams carries 1,024 units, about 2.6 times the bytes of a byte
section, so a pass is 1,311 sections instead of 3,445. A section took about 0.24 s against the
byte tower's 0.12 s (the readout and the face over 1,318 classes), so a pass with its held-out
read took 320 to 326 s against 414 to 430 s: about 0.09 ms a byte of text against 0.12. The
mode's clock is the unit's, so a mode of the same decay spans about 2.6 times the text.

## Samples

The prompt is the first held-out question, as in the previous records: "John volunteers at a
shelter twice a month for 3 hours at a time.  How many hours does he volunteer per year?" Each
sample opens at the prompt and releases 400 bytes (a unit tower releases units until it has
written at least 400), each class drawn exactly from the face, with the same key stream, alone
(one draw) and by agreement of two draws. Nothing is graded against the answer.

**The byte tower, gated, after pass 3** (the prompt reads 2.844 bits a byte). One draw:

```text
Jask wark.
Vibleves mays. How much, on. If incount buy is?
There year big fither by now?
Dast onse one?
First?
Rick sciil. Ind are Mitmay  aad 2=<<20*12=350>>350 fewor longs she toys to tilck 2 mubile carnjmons his orang and in speed
#### 3040

A trippens leed orlonany adseanins, they resses to stop, and shishdws, Many have, then sisted to a people to leve the seanes vaida chirked hor earlights in
```

Two agreeing draws:

```text
She drardeds $30 everyons. How many needs as many hours on the shown and 10 store the total thirn bears he kither to can she seads each we can creends of the number of money she toys.
#### 18

Jow can cards to finished to has to she a needs to the total she has to she candy minutes to show to spend for the students been on the house to is the number of buras.
#### 20

Card and the number of to he 
```

**The byte tower with the passage credit, after pass 2** (the prompt reads 2.938). One draw:

```text
Jarofuar. 5in one times tree. Jo woving of the teckets hours is Judracef * $60 gads = <<3*$5=$<<90*30=80>>80.
#### 34.
#### 75

Maganinat  a colten orden share a fays 125 more ansit from. He bagsled B. 28.00, she sing for 8 miles.
#### 12

Juset aprees longe 2 more his = <<12/3=5>>600 per more sotal.
#### 2500

Rold ependy.  What shove is taded. Toes each + 20% = <<4*80=120>>120 finiah in levoth 3
```

Two agreeing draws:

```text
The drammented both three for theasing a day one the the were toys to deabe to seat toys a total of 150 cards/does to game rese to counts $1/3 from the mile to day words.
The face the his her and 10 bag to spends to the bards to the a parden toy counts to seach toy per bentame will to the reft toys as for the buy.  He deculin hours to for the hours to of has 5 reads creads for the hours to hours a
```

**The unit tower after pass 1** (the prompt reads 2.343). One draw:

```text
The basks, Micha has are hadary - 210 = <<10-18=5>>50 left overs.
#### 10

Divitb be the length have left. He two crooms does the discount buyants sell 2500 visitches to libruding soda: 70+plat/250= <<300-90=25>>26 stickers per minut
He buys 80 student left a on the first 100 degrees on 30/3 = all kounting in her friends on billium. If each room is 60 € sizts and multiply) Byegare two and vought 
```

Two agreeing draws:

```text
The movie has 16 + 30 + 6 = <<12+6+12=14>>14 mages of cookies.
#### 5

Bob is currently only has to be second. If he has twice as his friends than Tony supplial number of sitten and just week. Le's he's homen has two members in all the first week. Adam has 1 cards up for a flavort. If he will spend 10 years old as the speed of a year, how many people are there are as Sarri's the number of bags befor
```

**The unit tower after pass 3** (the prompt reads 2.420). One draw:

```text
The basket's grade, there will be now 18 10 = <<20+5=15>>15 sides.
Thus, his rud was ap meantle that day she would have a total of 5*4=<<2*4=12>>12 miles per hour.
So the combined to drink to get to the esterday to is 26/2=4 pages of fruit every year during the third games.
T*60 = <<2*3=.09>>36 last if it and wide m cheems. How many people does Mariy spend from now?
Each day, it takes 4*2 = <<4*2=
```

Two agreeing draws:

```text
The movie has 16 + 10 = <<2+5+10=30>>30 minutes.
This morning up to a day for the first hour eats 30 minutes per hour, so he is 140+30 = <<150+60=60>>60 minutes of watermelon homen to the first week, Suni has 5 hours, she will be 300 stop. In one hour (1/2*2=<<20*2=40>>40 minutes.
#### 50

There are 200 students in the first hour. The team has to eat in the seam camp, how many penses does A have left
```

The letter towers write GSM8K's form (calculation lines with `<<a op b=c>>c` markup and a `####`
line, then a new question) in misspelt fragments. The unit tower writes clauses and sentences
with their grammar ("There are 200 students in the first hour.", "So the combined to drink to get
to the esterday to is 26/2=4 pages of fruit every year during the third games."), its markup is
well formed, and its arithmetic is wrong. Every sample, at both towers, opens a new answer on
another subject: none continues the question's subject (John, volunteering, hours a month).

**Read over eight key streams.** The same prompt, eight further 16 KiB key streams, 400 bytes
each, one draw and two agreeing draws, from both final towers. An observer read of the samples,
outside the machine: the share of the letter words written that occur as words in the training
text, and the share of adjacent word pairs inside a clause that occur adjacent in it
(`words.py`), and the longest run found verbatim in the training text (`recite.py`):

| tower | draws | words found | pairs found | longest copied run | bytes in copied runs of 24 or more |
|---|---|---|---|---|---|
| bytes, gated, pass 3 | one | 0.649 (519) | 0.259 (436) | 19 | 0 of 3,200 |
| bytes, gated, pass 3 | two agreeing | 0.870 (625) | 0.556 (595) | 25 | 25 of 3,200 |
| units, gated, pass 3 | one | 0.806 (484) | 0.496 (409) | 27 | 27 of 3,200 |
| units, gated, pass 3 | two agreeing | 0.939 (524) | 0.755 (453) | 29 | 108 of 3,200 |

The copied runs of 24 bytes or more are GSM8K's phrases (`The total number of `,
`divide the total number of se`, `50>>150 minutes.\nIn total, `), not recited problems.

## Not claimed

The founding is classical: a pair-merge segmentation (byte-pair encoding's proposal) with a
minimum-description-length acceptance under an order-one receiver. The parse is the greedy replay
of the merges, not the lattice. The tower is the gated state-space tower of the previous record,
reading a larger alphabet. A lower code in bits a byte is a reading beside the samples, not their
success. Nothing here grades a generation against an answer.

## Owed (#410)

- The passage credit's closed form: the carried moments `P_T`, `W_T` equal the derivative of the
  state with respect to the push and gate rows over the passage
  (`the_opening_credit_completes_the_passage_covector` checks it in Rust).
- The order-one price: the founding's `Δ` is the change of the complete code, the order-one KT
  code in the units plus the description, with the alphabet's growth
  (`each_price_is_the_change_of_the_order_one_code` checks it in Rust).
- The lattice read of the units: the code of all parses, beside the greedy parse's bound.
- The gated mode's bound under a moving radius stays owed from the previous record.

## Receipts

[`RUNS.tsv`](2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/RUNS.tsv) holds each run with its binary, projection, deadline, wall time,
peak resident set and hashes; [`SAMPLES.tsv`](2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/SAMPLES.tsv) each sample's;
[`UNITS`](2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS) the founded units (`founded-units-v1`, one ordered pair a line). The
founding keys and the 16 KiB sampling key stream are those of the previous record.
