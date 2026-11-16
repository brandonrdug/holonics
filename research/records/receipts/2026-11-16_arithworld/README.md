# The line joins an arithmetic world and word problems (November 16)

Brandon, November 16 17:00Z and 17:06Z: the writes pick up word shapes but do not compose; switch back to arithmetic in symbols and in word
problems, with TinyGSM and a synthetic world that answers each problem as an interpreter would, and watch how the words warp around the
problems, the symbols' certainty anchoring the words (`x + y = z` beside "add", "equals"). The theory thread's Build A of 17:05 UTC: the
arithmetic world as a slice of the store, held problems at the met lengths and at longer ones, and the line continued from its state as one
life. Refs #404.

## The two slices

- **The arithmetic world** (`tools/arithmetic_world.py`, key `arith-2026-11-16`). A record is `EXPR = VALUE` and a line feed: two to four
  operands of one to six digits, uniform in length and in digits, joined by `+ - *` with a space on each side, every operation below the
  outermost in parentheses (nesting at most two deep). The world evaluates each record by integer arithmetic at the boundary, and the field
  meets only the records. 32 records a document; a record whose keyed mark falls under one in a thousand is held out.
  - Training: 17,185,570 records drawn, 536,521 documents, 500,000,032 octets (SHA-256 `9d19e37d…0887`). 90 s on one host thread.
  - Held: 128 held-out records at the met lengths and 128 whose operands have seven to nine digits (lengths no training record has), one
    record a document, 9,957 octets (`73d7018e…e9e8`). `HELD_FORMS_arithmetic.tsv` gives each held record of two operands (86 of the 256) in
    three forms: symbols `a + b =`, words `a plus b equals` (`minus`, `times`), and a foil of the same lengths the passage never writes
    (`plux`, `minux`, `timex`, `eqvals`).
- **The word problems** (`tools/words_passage.py`, from TinyGSM, MIT). A document is the problem's question, its solution's statements (the
  function's body without its docstring or its `return`), and the world's answer, `answer = VALUE`. The answer is interpreted at the boundary
  from the solution's syntax tree on rationals (a straight line of assignments of `+ − × / // %`, bounded powers); no downloaded code is run.
  - Read 2,500,077 problems in the dataset's order. 245,823 left out for sharing an eight-word run with a GSM8K question (the train split and
    the 128 held problems), so GSM8K stays a yardstick. 780,267 refused: 464,093 with an answer that is not an integer, 173,672 with an
    expression outside arithmetic (a call, a comparison), 125,817 with a statement outside a straight line of assignments, 16,646 with a
    power past its bound, 30 others. 1,473,987 kept: 500,000,389 octets (`287be304…ae6d`). 100 s on one host thread.
  - Held: the line's 128 GSM8K problems as GSM8K writes them, one document each, 66,476 octets (`548c3f68…359e`). Their form is GSM8K's
    (its reasoning lines and `#### N`), not the training documents': the yardstick reads the words across that change of form.
- Every byte of both slices is in the line's codec (18 byte values in the arithmetic world, 169 in the word problems), so the join grows no
  letter.

## The store and the join

The store of November 16 is the store of November 12's five slices (code, web, science, books, wikidata; the same files) with the two new
slices after them: `STORE.tsv` SHA-256 `79db8227…8187`. The trainer's prefix role draws each slice in proportion to its prefix octets, so a
section's draws are about 20% code, 10% web, 10% science, 6% books, 4% wikidata, 25% arithmetic and 25% word problems.

`join-store STATE STATE_SHA STORE STORE_SHA OUT` (`crates/athena/src/store.rs`, beside `next-pass`) writes the state with its pass line set
to the grown store, its slices those of the store's role in order, every slice at its first piece, its count of stretches kept, and every
other line byte for byte (read back and checked). Why at a new pass (`agent-inferred`): the cut draws the slice whose places taken stand least
against its quota (`Cut::next`), so a slice joined in the middle of a pass is drawn alone until it reaches the others' share, or, set to their
share, alone once theirs end. On November 16 the line stood at 0.609 of its pass, and either join would have run about five laps on the new
slices alone. Joined at a new pass, every slice is drawn at its quota from the first section, and the pass ends for all of them together.
What the old five had left of their pass is read on the next one, the same law over the same passage. Tried on lap 69's end state: one line
changed (the pass line, line 11 of 11), the written state restores byte for byte (`STORE_RESTORE equal=true`).

## The reading of forms

`read-forms` (store.rs; on the card under `train`, or on the host's threads under `host`, which opens no card) codes a continuation after its
own prompt: each row of a table (`label`, `prompt`, `run`) is a region with its prompt resolved and its run open, the region the writer's
first read meets, and each open place is coded under its written byte. `tools/forms_table.py make` writes the table from the held files (the
86 sums in their three forms, and the 256 held records cut after `= `); `tools/forms_table.py sum` adds a log up by form, by the operands'
lengths, by the digit's place counted from the value's last, and, for sums and differences of two operands, by whether a carry (a borrow)
entered the digit's column. A ruler on the host; the world is synthetic, so its forms and values are printed.

## Guesses, fixed before any read

Codes in bits a place, at a lap's mean, on the held records of the arithmetic world.

- **G-an0** (lap 69's mean, before any arithmetic): the value's digits code at 3.0 bits a place or more after each of the three forms on met
  lengths, and words and foil differ by less than 0.05 bits a place.
- **G-ar1** (lap 71's mean, one lap on the joined store): the line feed that ends a met answer codes under 2 bits (the answer's length read
  from its operands' lengths).
- **G-ar2** (lap 71): the units digit of a met two-operand sum codes above 3.0 bits (no lock of the last digits after one lap).
- **G-an1** (lap 71): on met rows the value after symbols codes at least 0.3 bits a place below the value after the foil.
- **G-an2** (lap 71): words stand between symbols and foil and nearer the foil: words − symbols > 0.7 × (foil − symbols), as no record writes
  `plus` or `equals` and the word problems rarely write a sum in that form.
- **G-an3** (lap 71): on the symbols form, far rows' digits code within 0.2 bits a place of met rows' digits, and far rows' line feed codes at
  least 1 bit above the met rows'.

## Reads

**Lap 69's mean, before any arithmetic** (`forms69.txt`, read on the host's eight threads in 5.8 s beside lap 70 on the card). Bits a place
over the value's places (digits and the line feed); of the 86 held records of two operands, 37 are at met lengths (226 places) and 49 at far
ones (588 places):

| form | met, all places | met, units digit | met, lead digit | met, line feed | far, all places |
|---|---|---|---|---|---|
| symbols `a + b = ` | 4.45 | 4.27 | 3.97 | 5.59 | 4.21 |
| words `a plus b equals ` | 6.97 | 7.26 | 7.11 | 5.96 | 6.62 |
| foil `a plux b eqvals ` | 6.47 | 6.66 | 6.41 | 5.63 | 6.62 |

All 256 held records cut after `= `: 4.62 bits a place on met lengths, 4.31 on far ones; their line feed 5.35 and 5.74.

- **G-an0: half held.** Every form's digits code at 3.0 bits or more (3.97 to 7.26). Words and foil do not agree within 0.05: on met rows the
  value after `plus … equals` codes 0.51 bits a place above the value after the foil, and on far rows they agree (6.62 and 6.62). Before any
  arithmetic, the field's own words lead away from a number more than an unknown word does; the symbols already lead 2 bits nearer it,
  from the code and the web's `=`.

## Gates

- Gate 1 (`bash tools/gate.sh`): passed.
