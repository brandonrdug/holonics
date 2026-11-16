# The arithmetic world's held reads and writes, lap by lap (November 16)

The line trains on the store of November 16 from lap 71 (`../2026-11-16_arithworld/`). After each lap, on the lap's mean and on the host's
threads beside the card's next lap (`forms19.sh` in the line's run directory), three things are read:

- **The forms read** (`read-forms` on `FORMS_arithmetic5.tsv`): each held sum of two operands (37 at met lengths, 49 at far ones) followed
  by its value after five prompts, and the 256 held records cut after `= `. The prompts are symbols `a + b = `, words `a plus b equals `,
  the foil `a plux b eqvals `, a null foil of the same lengths, and swapped words. The null foil draws its letters by the world's key from
  those the operator's word and `equals` lack. The swapped words put another operation's word before this one's value (`times` before a
  sum, `plus` before a difference, `minus` before a product). The last two are the theory thread's controls of 17:58 UTC: `plux` is one
  letter from `plus`, so for a field that reads word shapes it is a noisy source of the operator, not a null.
- **The writes after the arithmetic prompts** (`write-forms`, added here: the writer `write-store` runs, released after each row's prompt
  with 16 places open, the key file's seed). The world is synthetic, so the writes are kept in this directory.
- **The writes after 24 GSM8K test questions** (`write-forms` on `FORMS_gsm8k.tsv`, `tools/forms_table.py gsm8k`: each question and a line
  feed, 192 places open). GSM8K's test split is public.

## Before any arithmetic

Bits a place over the value's places (its digits and line feed), met rows, at the lap's mean (`forms5_69.sum`, `forms5_70.sum`):

| prompt | lap 69 | lap 70 |
|---|---|---|
| symbols `a + b = ` | 4.453 | 4.345 |
| held records after `= ` | 4.617 | 4.552 |
| null foil | 5.984 | 5.720 |
| foil `plux … eqvals` | 6.466 | 6.441 |
| words `plus … equals` | 6.973 | 7.035 |
| swapped words | 6.986 | 7.046 |

Before the arithmetic world, the field's own words lead furthest from a number. The null foil, letters it has never seen together, leads
nearest after the symbols. Matched and swapped words code alike (0.01 bits apart at both laps), so no word yet carries its operation to
the value.

The writes after the prompts at lap 70's mean (`wf70.written`, 16 places, 107 s on eight host threads) are scattered bytes: digits and
punctuation after the symbols, word fragments after the words.

## Guesses

The build's own, fixed at 17:20 UTC before any read (`../2026-11-16_arithworld/`, G-an0 and G-ar1, G-ar2, G-an1 to G-an3 on lap 71), and
the theory thread's of 17:58 UTC, in nats a place on met rows at a lap's mean (bits × 0.693):

- **G-an4**: from the first lap where words code the value at least 0.2 nats under the null foil, `plux` stands between them, at least a
  quarter of the way down from the null toward the words.
- **G-an5**: from that lap, swapped words code at least 0.1 nats above the null foil; before it, swapped and matched words differ by under
  0.1.

The theory thread's earlier set is cited as "G-an1–3 (17:08)", apart from the build's lap-71 G-an1 to G-an3.

## Lap 71, the first on the joined store

Lap 71 trained 3,000 sections in 1,414.7 s (lap 69: 1,432.6 s on the old store). Its sections drew about 56 arithmetic and 64 word-problem
regions in some 215, with the old five's in proportion.

**Loudness and code by region at lap 71's mean** (`loud71.txt`; nats a place, loudness in octaves; lap 70 beside):

| region | lap 70 | lap 71 | loudness 70 → 71 |
|---|---|---|---|
| code | 0.4901 | 0.5449 | 19.82 → 19.85 |
| web | 0.8494 | 0.9061 | 19.93 → 19.94 |
| science | 0.6979 | 0.7566 | 20.01 → 20.02 |
| books | 0.8131 | 0.8654 | 20.16 → 20.14 |
| wikidata | 1.0157 | 1.0509 | 19.87 → 19.89 |
| arithmetic (256 held records, 11,493 places) | | 1.5425 | 20.23 |
| words (GSM8K test, 20,496 places) | | 0.8106 | 19.97 |

The old five rose 0.035 to 0.059 nats a place in one lap, more than the line had fallen in the nine laps before (0.002 to 0.006). The
held arithmetic is the loudest region (20.23 octaves), and its loud places are its cheap ones (Spearman −0.46 between loudness and code;
words −0.28, the old five −0.10 to −0.21, wikidata +0.30).

**The forms read** (`forms71.sum`; bits a place, met rows, all the value's places; lap 70 beside):

| prompt | lap 70 | lap 71 |
|---|---|---|
| symbols `a + b = ` | 4.345 | 3.554 |
| held records after `= ` | 4.552 | 3.645 |
| null foil | 5.720 | 5.702 |
| foil `plux … eqvals` | 6.441 | 5.956 |
| words `plus … equals` | 7.035 | 6.282 |
| swapped words | 7.046 | 6.344 |

The symbols, the words, the foil and the swapped words each fell 0.5 to 0.8 bits a place in one lap. The null foil did not move (−0.02).
Words and swapped words still code alike (0.06 bits apart), so the drop under the words is the field reading `<number> <word> <number>
<word>` as a place where a number follows, not yet a word carrying its operation. The foil, one letter from the words, fell with them.

**The guesses on lap 71:**

- **G-ar1, missed.** The line feed ending a met answer codes 4.07 bits over all held records (3.55 on the sums of two operands), not under 2.
- **G-ar2, held.** The units digit of a met two-operand sum codes 3.59 bits, above 3.0.
- **G-an1, held.** After symbols the value codes 2.40 bits a place under the foil (3.55 against 5.96).
- **G-an2, missed.** Words do not stand between symbols and foil: they code 0.33 bits a place above the foil.
- **G-an3, held.** On the symbols form, far rows' digits code 3.70 bits and met rows' 3.56 (0.15 apart); far rows' line feed codes 5.56
  bits against the met rows' 3.55 (2.01 above).
- **G-an4 and G-an5** (the theory thread's): words code 0.40 nats a place above the null foil, so the lap that opens G-an4 has not come.
  G-an5's first clause holds so far: swapped and matched words differ by 0.04 nats.

**The writes** (`wf71.written`, `wg71.written`). After the symbols the writer now writes a number, a line feed and the next record's
expression, the world's own record shape (`878893 - 35917 = ` → `665349`, a line feed, `5125 - 73`); after words it writes word
fragments. After GSM8K's questions (written on the card in the gap after lap 71's reads, 9.7 s for 24 questions of 192 places) it writes
the word problems' solution form: lines of `name = expression` whose names it builds from the question's words (`eggs_pugs__per`,
`meter_1`, `price = 15`, `total = …`, `result … = 10 576`).
