# The race track runs the plain tower for hours on the card and writes after every lap

Refs #404 #76. Status: [design fixed before the run; agent-inferred, October 27]. The run's
results are added below as they arrive. Owners: `holonics::hnn::tower::realization` (the section's
pass, the held-out read and the advance through a realization), `holonics_cuda::hnn::tower`
(`TowerCard`), `tower_classes` in the `complete-language` example (training and release on a class
passage) and `holonics-cuda`'s `tower_pass` example (the card route). Receipts:
[`receipts/2026-10-27-race-track/`](receipts/2026-10-27-race-track/).

## Why

Brandon's direction of October 27, as the [GPU-first record](2026-10-27_THE_LEARNER_RUNS_ON_THE_CARD_AND_ITS_WORKLOAD_IS_NEVER_TRADED_FOR_TIME.md)
records it: the tower converges because it is plastic, so run it fast and for long on the 4080 and
watch how it spreads information and language through itself, never by vertical data scaling. The
runs before it learned on eight CPU threads, two levels of 64 modes, eight streams and three passes
of 3.5 MB. This run holds the law fixed and sizes the work to the card.

## The run, decided before it starts

**Device line.** Every lap's forwards, reverses, held-out read and writing run on the RTX 4080
SUPER under the main checkout's `.local/gpu.lock`, one lap a segment so the lock frees between
laps. Each section's moments, step, certificate and deposit stay the host's (the learner's one
law, `TowerLearner::section_realized`), on the 7900X with `RAYON_NUM_THREADS=12`; every receipt
states the card's and the host's time. No part of the run learns on the host alone.

**The learner.** The plain gated tower on both turn ladders (`train-two-ladder-tower-classes`):
rectifying contacts, not turned, not pumped, no pair or ring face, no rotor or strands, alphabet
257, width 64, 128 modes, 256 contacts, **four levels** (the most the card carries), sections of
128 classes, rate `2^(−7)`, **320 streams** (where the card filled on October 25). This is the
October 25 card law with two levels more; nothing is cut to fit time.

**The passage** (`compose_race_passage.py`). Every Markdown file under `docs/` and
`research/records/` in path order (1,839 files at the build's tree), then the GSM8K training
text: about 29.7 million classes, one an octet, the end letter after every file and after the first
blank line closing 4 KiB, the October 25 rule. The octet is the codec's grain, fixed before the
tower reads it, and all four levels tick at it, one step a class: this run does not let the tower
learn its own encoding. Levels that tick where the machine's own units close (a receiver's clock
counting its own flux across a section, coarser levels at the odometer's carry; the elementary
objects' §12) are [the next design](2026-10-27_THE_LEVELS_TICK_ON_THEIR_OWN_NEWS_SO_THE_TOWER_LEARNS_ITS_ENCODING_ON_ITS_OWN_AXIS.md), kept out of this run so that the race reads the plain tower's
plasticity alone and the two axes are never mixed in one measurement.
Held out: `README.md` and the records dated October 26 and 27 (about 500,000 classes, read as
region `words`), and the GSM8K development text (about 398,000, region `gsm8k`). The GSM8K
problems of the two texts are checked disjoint before the run.

**The writing.** After every lap, `release-tower-classes` on the card from that lap's learner:
three prompts (the first end-lettered span of `README.md`, of the first held-out record and of the
GSM8K development text), each twice, 1,024 classes each at agreement 1, the same release keys
every lap, so two laps' writings differ only by the learner. The release reads each prompt as one
stream, then draws all prompts together, one class each a launch.

**Before any lap**, fixed now:
- (a) the October 25 command at 24, 96 and 320 streams, built with the `certificate-check`
  feature (each decision the readings make is compared with the exact products and a disagreement
  stops the run), leaves `STATE.0` with the October 25 SHA-256s
  (`6470451f…`, `8ee11071…`, `7f71cea4…`) and dev bits 2.819, 3.416 and 4.660. The forward count
  now includes the held-out read's forwards, which ran on the host before.
- (b) `tower_pass parity` at the race's declaration on the race passage: 32 sections at 24 streams
  and 4 at 320, every face and covector entry equal. Four levels have not been checked on the card;
  if this fails the race does not start. The host reference (`HostPass`) keeps no cell between its
  calls and its reverse reads each stream's forward again (amended October 27, below), so the
  320-stream parity holds only the cells of the streams its threads are reading.
- (c) the card's release equals the host's (`RELEASES.classes` by SHA-256) from (a)'s 24-stream
  learner on the race prompts and keys, and the GPU suite `tests/tower_pass.rs` passes, its new
  advance test included. The host's release is that parity reference: `HOLONICS_HOST_EXCEPTION`
  names a manifest of kind `parity` whose command is the host run's and whose card log already
  holds the card release of the same command (`complete_language::host_exception`); the host route
  refuses any other run.

**Time.** A one-to-three-minute opening read of the first lap on the card gives the largest time
a 32-section window takes; a lap (about 726 sections) is projected from it with the held-out read
and the state write, and that projection's upper end is each lap's fixed deadline (`race.sh`).
A lap that passes its deadline stops and is reported incomplete, and `race.sh` stops the race after
any lap with a window past 1.12 times the opening read's largest, or with fewer than two windows
read. Laps continue for eight hours from launch; no lap starts after that, and no deadline is
raised.

**Reported each lap:** train and held-out bits a class by region, deposits over sections, the
pass's time with the card's and host's parts, and the six writings, whole. Bits are readings beside
the writing, never its success.

## The recorded failures this run could repeat

- *Bits read as progress*: each lap's writing is shown whole beside its bits.
- *A refusal answered with a larger limit*: the lap deadline comes from the opening read and is
  never raised; a slow lap stops and is reported.
- *Seen material graded as unseen*: the held-out files are named by rule before the run and the
  GSM8K split is checked disjoint.
- *Text run on its codec's grain as the exception*: this run does read text at its codec's grain,
  the octet, which is that failure's form; it is declared as the plain tower's measurement, no
  text-only part enters the route, and the repair is the learned grain above, its own design.
- *An uncertified deposition step*: (a) checks the certificate against its products on every call.
- *A located cause carried unrepaired into a new consumer*: four levels are checked by (b) before
  the race reads them.

## Before the laps (October 27, on the PC, at `4374a509`)

Every check below ran on the RTX 4080 SUPER under the card lock, the host reference on the 7900X.

- (a) passed. Each `STATE.0` is October 25's (`6470451f…`, `8ee11071…`, `7f71cea4…`), the dev
  bits 2.819, 3.416 and 4.660, and the certificate's assertion stopped no run. The card's forwards
  are 503, 139 and 56 against October 25's 493, 136 and 55: the held-out read now runs on the card.
  The unchecked build's 320-stream pass took 2,122 ms against October 25's 11,027 (card forward 956
  against 1,044 ms, reverse 504 against 592); the checked build's took 10,772 ms, so comparing every
  decision with the exact products costs about 8.6 s of that pass.
- (c) passed. The GPU suite, 4 of 4. The card's release equals the host's: `RELEASES.classes`
  `87b2f180…` and `RELEASES.tsv` `d28ac019…` in both, six prompts of 4,145 to 4,544 classes.
- The passage: 1,839 files, 33 of them held out, 29,744,156 training classes, 913,986 held-out
  (397,759 GSM8K, 516,227 prose). None of the 747 development problems has its question line in
  the training text.
- (b) at 24 streams passed: 32 sections, 98,304 faces, 10,588,192 covector entries and every
  learner equal, four levels; host reference 9,918 ms, card 3,115 ms; peak resident 1,673,124 KiB.
  At 320 streams it was not run: the host reference then held every stream's cells for its reverse,
  which projects to about 22.3 GB against 11.7 GB available. `HostPass` now keeps no cell between
  calls (the test `the_host_pass_reads_each_stream_again_for_its_reverse`); the 320-stream parity
  runs at the amended head before any lap.
- The opening read ran the whole first lap inside its 180 s: 726 sections in 119.0 s (card
  99.4 s, its forwards 61.3 s and reverses 38.0 s; the host's moments, step and certificate about
  19 s), 531 MB peak resident, 6,313 MiB on the card. Training 2.748 bits a class, held out 2.356
  (GSM8K 2.407, prose 2.317). The largest 32-section window w = 5,316 ms, the founding and reading
  before the first f = 940 ms, so a lap's deadline is ⌈1.12 · (23 · 5.316 + 0.940)⌉ + 120 = 258 s,
  a writing's ⌈4 · 3.1⌉ + 60 = 73 s, and the race's memory bound 8 GiB.
