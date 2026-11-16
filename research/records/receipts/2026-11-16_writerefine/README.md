# The writer's refine passes read against their references (November 16)

The theory thread's guesses W1 to W4 of 16:37 UTC, on the writer of lap 69's end state (the four-lane line on the store of November 12):
`write-store` on 20 held problems (4 a slice, a prompt of 256 places, a run of 256) with REFINE 0, 4 and 16, each write read by
`read-writes` (added here: each written run and its reference coded after the problem's prompt, every place open alone among the run's
others, the one-place receiver, and every place open at once, the receiver of the writer's first read) and by `tools/write_words.py` (a
ruler: the share of a write's whitespace-separated strings of two or more octets met as strings in its slice's training prefix, and the
share of its commonest octet). The writes and the held texts are private and stay outside the tree; these files hold counts only.

Device: the card, lock held in the gap after lap 69. Writes 13.5 s, 59.4 s and 198.4 s (`write_times.txt`; projected 13, 65 and 220 s);
each read about 21 s (`read_writes.txt`).

## Readings

Bits a place (`read_writes.txt`; the file prints millionths of a bit). One-place code of the write, then of the reference:

| slice | write, 0 passes | 4 | 16 | reference |
|---|---|---|---|---|
| code | 2.48 | 2.09 | 1.37 | 0.62 |
| web | 2.81 | 2.71 | 2.68 | 1.00 |
| science | 2.97 | 2.87 | 2.47 | 1.80 |
| books | 2.49 | 1.89 | 1.97 | 1.61 |
| wikidata | 3.09 | 2.93 | 2.41 | 0.70 |

All open at once, the write codes 4.68 to 5.47 bits a place and the reference 4.80 to 5.23 at every count of passes: under that receiver the
field reads its own drafts about as it reads the references.

Words met in the slice's prefix (`write_words.txt`), 0 → 4 → 16 passes: books 0.580 → 0.650 → 0.618; code 0.442 → 0.408 → 0.519; science
0.340 → 0.386 → 0.443; web 0.419 → 0.532 → 0.567; wikidata 0.223 → 0.134 → 0.137. The commonest octet's share: code 0.119 → 0.219 → 0.252
(`/`, octet 47), the others within 0.04 of where they began (a space in four slices, `e` in wikidata at 16 passes).

## The guesses

- **W1, partly missed.** The guess: the write's one-place code falls from 0 to 4 to 16 passes in every slice; at 0 passes it stands 0.3 to
  1.0 nats a place above the reference's, and at 16 passes 0.1 to 0.5 nats under it. It fell in four slices and turned back in books from 4
  to 16 passes (1.89 to 1.97 bits). At 0 passes it stood 0.61 to 1.65 nats above (two slices inside the guess). At 16 passes it stood above
  the reference in every slice, 0.25 to 1.18 nats, never under.
- **W2, missed.** The guess: the share of words met in the prefix rises by 0.10 or more from 0 to 16 passes in at least four slices. It
  rose that far in two (web +0.15, science +0.10); code rose 0.08, books 0.04, and wikidata fell 0.09.
- **W3, missed.** The commonest octet's share rose 0.13 in code (to a quarter of the written octets, `/`), past the guess's bounds.
- **W4, held.** At 16 passes no write holds a sentence (read by eye; the texts stay private).

What the reads say about the refine law: rereading the draft as the field's own lowers its code under the one-place receiver everywhere
but books, and buys words in web and science. In code it buys repetition of one octet, not structure. These drafts were written on the
store of November 12 alone. The line has since joined the arithmetic world and the word problems (`../2026-11-16_arithworld/`), and the
writes are next read on held arithmetic and word problems, where the world's answer is the reference.
