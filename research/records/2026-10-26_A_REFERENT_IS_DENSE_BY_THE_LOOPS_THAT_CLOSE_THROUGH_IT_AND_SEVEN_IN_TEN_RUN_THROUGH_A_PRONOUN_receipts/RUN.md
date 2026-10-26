# Runs of the referent receipt

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `referent_mass.py` | A: the 6,726 training problems (render `b`), named problems, person names and their sheets, the opener's mass and loops per problem, the sheet against the next word; B: the held-out John problem and its reference answer; C: the 400 committed samples after the John question, by group; D: the carry of each word of the question | unmeasured before the first run, so planned at one to three minutes | 180 s (development runs), 60 s (final run, from the development runs' largest 1.9 s) | 1.61 s | 74,100 KiB |

`referent_mass.py`: exit 0, `all 19 checks hold`. Output `referent_mass.txt`. Script SHA-256
`d5b1f21115c368bda7793bc28056cc13c4b1b34c5c0ae6f425f2196eeb798a17`; output SHA-256
`00e270c196fbe26a96adccd72ff703dbb9ceef755ab67d8081d55f3a2d407c7e`. The elapsed milliseconds differ
between runs, and every other field is deterministic.

Exact arithmetic only: integers and `fractions.Fraction`. The decimals in the output are printed
readings beside fractions, formatted by integer division, and enter no check. No float is built.

Inputs:
- GSM8K's public training split (`train.jsonl`, 7,473 rows);
- the partition written by `tools/gsm8k/partition.py` (6,726 training and 747 development rows);
- the repository's committed sample files `2026-10-26_*_receipts/SAMPLES*.md`.

No private data. Run as `timeout 60 python3 -I` through `runpy`, the peak read by
`resource.getrusage` (`/usr/bin/time` is not installed here). Measured to projected wall: 1.61 s
against 60 s.

Development, before the final run:
- **The named count.** The first run checked 4,524 named problems per training row and failed: per
  row the rule counts 4,523. Design's 4,524 splits the text at blank lines, and one answer contains a
  blank line. The script now checks both counts and states why they differ.
- **The name rule.** It first kept an opening word only when it occurs capitalized after a lowercase
  word more often than lowercase. That dropped real names that never occur mid-sentence (Isabel,
  Abigail). The rule now drops a word only when its lowercase form occurs there at least as often.
- **Grouping.** The sample groups first pooled the banked and bankless samples of passes 4 to 7. They
  are now split by the sample's header.
- **Per-sample reads.** One sample's "he is means he is" loop dominated the pooled mention counts, so
  the table leads with per-sample counts.
- **Part E removed.** The first committed version (PR #498) had a fifth part, the held-out
  denominators for the acceptance of a build this record specified. That build is withdrawn (the
  record's §5), so the part and its check went with it: 20 checks became 19. Parts A to D are
  unchanged, and every number they print is the same as in the first version.
