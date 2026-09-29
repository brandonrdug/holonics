# Native generation: the moiré continues exactly, the copy is near, and text is illegible

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [measured] for the
receipts, read once each at the pinned commit `70a572e7` (the
[pins](2026-09-29_NATIVE_GENERATION_PINNED_BEFORE_ITS_RUNS.md)); [agent-inferred] for §4.

**What ran.** `hnn::prediction` (commit `64eac0eb`): a section of the receiving ring refined by
`K = 2` continuing words of one tick from the request's moment and a latent, read jointly at every
station from one anchor, released at width zero through `receiver::release`, and learned by the
section's covector pulled back through the words and deposited by the normal law inside the
refinement's diamond. Nothing is authored for a terrain: `R` opens at zero and `E` at the declared
sign sequence. The path reads no window, no landmark tree and no copy stage.

```sh
cargo run --release -p holonics --example hnn_prediction -- copy
cargo run --release -p holonics --example hnn_prediction -- moire
cargo run --release -p holonics --example hnn_prediction -- text .local/cuts/curated-u6-passage-cut.bin .local/cuts/u6-native-sections.txt
```

## 1. Acceptance 1, the internal checks: holds

On every refinement of the three runs, 2,818 in all:

| Run | Refinements | Balances closed | Pairings exact | Commits closed | Deposits | Unreached checks (loci) | Every unreached locus unchanged |
|---|---|---|---|---|---|---|---|
| copy | 1,536 | 1,536 | 1,536 | 1,536 | 96 | 96 (672) | 96 of 96 |
| moiré | 512 | 512 | 512 | 512 | 32 | 32 (224) | 32 of 32 |
| text | 770 | 770 | 770 | 770 | 50 | 50 (350) | 50 of 50 |

Every balance closes with its pump, dissipation and every chart and split residual stated, the ticks
chained across the words and the request's re-entry the only jump; across each deposit the
deposition work closes it. Every pairing is exact on the executed charts. The seven loci outside each
refinement's diamond (ring 1's element and resonator locus; ring 2's element, junction, standing and
resonator locus; the channel of the contact joining rings 1 and 2) kept their material and deposit
clocks. Every release's width was read: in training the copy's sections
released at width zero 1,494 times of 1,536, the moiré's 494 of 512 and the text's 308 of 770; the
rest were plural at a station's top grain cell and held.

## 2. Acceptance 2, known truth

- **The moiré continues exactly: passes.** Two gratings, joint period 6, least period 6,
  determining depth 2. After 512 windows every one of its 6 distinct windows is released at width
  zero and equals its continuation exactly, 48 of 48 stations. Its windows are finitely many, so
  this reads whether the field located one navigator's continuation, not transfer. The training
  sections coded `661 + 6/16 + ε` bits over 4,096 stations.
- **The copy is near: fails as pinned.** After 1,536 requests, 256 fresh requests of 8 symbols: all
  256 released at width zero, **234 of 256 equal to the request exactly**, 2,026 of 2,048 stations
  right. The pin asked for 256 of 256. The training sections coded `2833 + 0/16 + ε` bits over
  12,288 stations.

The echo and the continuation were located by the field's own refinement and deposition: nothing
copies, no grating routine reads the emission, and `R` and `E` began at zero and at the sign
sequence.

## 3. Acceptance 3, text: fails

After two passes over the passage's 385 choosing pairs, the 8 validation requests F0's rule selects
gave 7 sections of 32 bytes, each valid UTF-8, and one typed refusal (every member plural at some
station). The sections are strings of `e`, `o`, `r` and spaces, a few other letters among them; the
two requests that share one human part gave the same section. **They are illegible**, and the item
fails. The text is owner-only (`.local/cuts/u6-native-sections.txt`) and was shown in the
conversation whole, with nothing beside it. The members that released: at rest once, keyed 1 three
times, keyed 2 once, keyed 6 twice. The training sections coded `144724 + 10/16 + ε` bits over 24,640
stations, between `5 + 13/16` and `5 + 14/16` bits a station.

## 4. Time and memory

| Run | Milliseconds (projected) | Peak resident bytes |
|---|---|---|
| copy | 447,718 (about 456,000) | 401,580,032 |
| moiré | 142,464 (about 142,000) | 381,526,016 |
| text | 389,739 (about 386,000) | 819,576,832 |

No run reached its training stop (540,000 ms) or the 20,000,000,000-byte cap. The text run passed its
projection by 3,739 ms, within the ten-minute bound; its evidence is complete.

## 5. What stays open, by its measurement [agent-inferred]

- **Text.** The section's stations are a linear readout of one anchor that a linear refinement makes
  from the request's phase-binned moment, then a face per station. That is a log-linear chart of the
  request's bytes by phase: its most frequent bytes win at every station, and it codes the training
  responses at between `5 + 13/16` and `5 + 14/16` bits a station. The blocker, by its measurement:
  the native field's readout codes response bytes near the byte frequencies, so its sections are
  illegible. What must change is what the anchor carries of the request, which is the encoding's
  subject (`hnn::encoding`: text's recurring transformations must be located from the passage), and
  the refinement's reading of its own section, which this loop keeps linear.
- **The copy's last 22 sections.** 22 stations of 2,048 are wrong after 1,536 requests. The copy's
  readout is representable exactly (the 60 directions of 8 cells' offsets through 4 symbols
  separate in the ring's 64 coordinates); the normal law's steps shrink as the Grams grow, and the
  pinned training bound stopped before they were separated.
- **The normal law in a deep refinement.** At `K = 4` campaign 1's steps diverged on the moiré (the
  pins' development table): the covector reaching the source port sums every station and every word
  the moment re-enters, times the receiving map's gain, and the normal law moves the port by all of
  it. The lattice rule's unit-scale covector assumption fails there. A step that reads the
  downstream gain is owed before deeper refinements; this loop took `K = 2`.

## 6. Owed in #62

- `HNN/Prediction` on the concrete word: `jointSection` with the continuing word (`HNN/Word.fieldTick`
  continued across a word's boundary) as its step, and the continuing return as the exact adjoint of
  `F^[K]` (checked on every refinement in Rust on the executed charts; the concrete bridge is owed
  with the diamond's, "Step 4 (#73) owed: the diamond on the concrete tick").
- The normal law's stability in a refinement: a bound on the covector reaching an upstream locus
  through `K` words and `m` stations, and the step under which the carried deposition stays within the
  lattice rule's unit-scale assumption.
