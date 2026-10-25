# One listener hears GSM8K, MNIST and speech as sections of one passage

Refs #404 #406. Follows [the tens with the hand](2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md#the-tens-with-the-hand-the-key-located-at-the-units-the-ring-read-at-the-tens),
where the arithmetic line stops. Status: [measurement; agent-inferred, October 25], on the host
(4 cores). Owners: `tower_classes.rs` (train, read and release over a class passage) and
`tools/listener/{compose,render}.py` (the boundary charts); atlas `hnn.tower-class-passage`.

## The failure this step works on

From October 23 to October 25 every tower heard digit lines or text built around them, and every
reading asked about digits. Brandon's direction on October 25: the arithmetic had become the road,
and the general tracks (GSM8K, MNIST, LibriSpeech) are the work. Arithmetic stays one section of
what the machine hears. This step brings the three tracks back as sections of one listener.

## The claim fixed first

One gated tower hears one passage holding whole GSM8K problems, MNIST digits and LibriSpeech
speech in one alphabet. It is read on held-out material of each medium beside two foils: a tower
of the same declaration that heard only that medium's sections (the sibling), and conditional xz
on the same class files. The product step is what the listener writes from held-out prompts,
shown whole. Transfer would show as the listener coding a medium below its sibling. No claim of
usable output is made until the outputs are usable.

## The passage

A section is `source, END, target, END` over the classes `0..256`: the 256 octets and the end
letter 256, which no octet writes (the tower reads classes of a declared alphabet and nothing else,
so the alphabet is 257). The charts are `examples/listener/sections.rs`'s, written in
`tools/listener/compose.py`:

- text is its octets;
- an MNIST raster is its stroke, one octet a pixel `(turn << 4) | octave`, the turn in eighths
  relative to the heading and turn 8 a jump followed by a signed `(dr, dc)`; about 168 octets an
  image;
- PCM at 16 kHz is its half-cycles, the run length (255 escapes) then `(sign << 4) | peak octave`;
  about 4,300 octets a second.

The exact fibres (an intensity's remainder inside its octave, a sample's residual from its
half-cycle's peak) stay at the boundary: the tower hears the chart. MNIST's label `7` is the octet
`0x37`, the same class as GSM8K's `7`.

Sections: GSM8K question then answer; MNIST an image then its label, and every other training
image the label then the image; LibriSpeech an utterance then its transcript, and every other
training utterance the transcript then the utterance. The media are interleaved by the smallest
share of their progress, so every stream the tower cuts holds all three. Training: 1,000 GSM8K
problems, MNIST training images `0..2999`, 90 s of speech from the dev-clean speakers. Held out:
100 GSM8K development problems, MNIST training images `50000..50499` (the official test set stays
sealed), and 19.2 s from two speakers never heard. Counts and every file's SHA-256 are in the
receipts' `MANIFEST.json`.

| | Training classes | Held-out classes |
|---|---|---|
| GSM8K | 518,633 (1,000 sections) | 53,556 (100) |
| MNIST | 516,933 (3,000) | 84,205 (500) |
| Speech | 354,790 (22) | 82,275 (4) |
| One passage | 1,390,356 | 220,036 |

## The route

`train-gated-tower-classes` is the gated tower's `fit` over a class file (width 64, 64 modes, 256
contacts, two levels, 8 streams of 128-class sections, rate `2^(−7)`); its `TOWER_PASS` line names
the held-out regions by medium. `read-tower-classes` reads a held-out passage in parallel parts,
each from rest, and sums each class's code by its section's mark (answer, question, label, stroke,
cycle, transcript, end), with the label numerals' confusion. `release-tower-classes` writes from
prompts by agreeing draws until the end letter.

[agent-inferred] A prompt is entered as every section of the passage is: from rest through one end
letter, then its source. From rest alone, a numeral and its end letter are also the close of every
GSM8K answer, and the first release (one pass) drew GSM8K text for every numeral asked for.

## Measured

Held-out bits a class (whole medium, lower is better). Conditional xz and bzip2: the training file
compressed with and without the held-out file after it (`BASELINES.txt`).

| Held-out medium | Listener, 1 pass | Sibling, 1 pass | Listener, 4 passes | Sibling, 4 passes | xz | bzip2 |
|---|---|---|---|---|---|---|
| GSM8K | 2.884 | 2.795 | 2.689 | 2.572 | 2.147 | 2.238 |
| MNIST | 3.129 | 3.069 | 3.084 | 2.984 | 3.684 | 3.684 |
| Speech | 3.442 | 2.915 | 3.270 | 2.820 | 3.219 | 3.429 |

- **No transfer at equal width.** The listener codes every medium above its sibling. After four
  passes it pays 0.117 bits on GSM8K, 0.100 on MNIST and 0.450 on speech, where its sibling of
  the same declaration hears one medium with the same state.
- **The GSM8K sibling is the October 23 byte tower on classes.** That tower took 1,000 problems'
  held-out code to 2.531 bits a byte after seven passes; the sibling reaches 2.572 after four. The
  route the tower was joined to on October 23 (the passage tree's news and its node lock, trained on
  all 6,726 problems) reads any class sequence. Joined, GSM8K came to 1.574 bits a byte. It is not
  joined here.
- **The siblings code MNIST and speech below xz, GSM8K above it.** For context only, since the
  chart drops the fibre: the digit sibling's 503 bits an image (62.8 bytes) beside a lossless PNG's
  249.6 bytes, and the speech sibling's 12,106 bits a second beside the corpus FLAC's 146,882.
- **Labels at chance.** Reading each held-out image in its passage and naming its label by the
  face's largest class: the digit sibling names 46 of 500 right after one pass and 52 after four;
  the listener 21 and 38, and it names almost every image `4`. Chance is 50. The label costs the
  sibling 4.036 bits, above the 3.32 of a uniform numeral: after an image's end letter the face
  does not yet expect a numeral.
- **GSM8K writing takes the answer's shape.** After four passes the answers are lines with a
  bracketed step and a closing `####` line, and 3 of the 6 releases (3 prompts, 2 towers) end
  by themselves (none did after one pass). Every number is wrong, and the words are GSM8K's
  vocabulary without a subject.
- **The speech sibling changes medium at an utterance's end.** Given the first held-out utterance
  it writes an upper-case transcript-like line and ends; given the second it keeps writing
  half-cycles. Given a transcript it writes another transcript instead of speech. The
  listener writes a word problem.
- **Written digits.** Asked for a numeral, the digit sibling writes a numeral and stops; the
  listener writes a word problem. With the two directions alternating, `END numeral END` both
  closes an image's label and opens a request to draw one, and a release from rest cannot say
  which. The entering end letter repairs only the first ambiguity.

The outputs were shown whole in the conversation. They derive from public datasets and are not kept
here; `RELEASES.txt` keeps each release's length, its prompt's code and whether it ended.

## What the measurement locates

The three tracks need the same link: a target read from its source (an answer from its question,
a label from its image, a transcript from its utterance). The listener hears each medium's form,
and below xz on two of the three. The link is absent where it can be read most cleanly: the
label is 0.6% of the digits' classes, and the face at it is not better than a uniform numeral.

## The state at the label

Whether the state at the label still carries the image decides where the link breaks.
`read-tower-classes-at` reads the frozen tower over a passage as `read-tower-classes` does and
writes, at every cell where a label arrives after its image, the top face the readout reads (64
integers on `2^(−16)`) and every level's carried modes (2 × 64 complex). There are 1,500 such
training cells (every other image of `0..2999`) and the 500 held-out. `tools/listener/probe.py`
fits exact exterior probes on the training cells (no floats; nothing returns to the tower) and
names the held-out labels. The foil is the same probe on the stroke chart itself, drawn back to its
raster and pooled to 7 × 7. Held-out labels named, of 500 (chance 50, the commonest label 54):

| Read at the label | Digit sibling | Listener |
|---|---|---|
| The tower's own face (its largest class) | 52 | 38 |
| Top face, nearest class mean | 99 | 71 |
| Top face, each coordinate scaled by its within-label scatter | 103 | 72 |
| Top face, pooled covariance | 76 | 68 |
| Carried modes, nearest class mean / scaled | 103 / 111 | 97 / 92 |
| The modes' energies (blind to phase), nearest class mean / scaled | 102 / 108 | 105 / 103 |
| Foil: the stroke chart drawn back, nearest class mean / scaled | 377 / 383 | 377 / 383 |

- **The state keeps little of the picture.** At best the sibling's state names 111 held-out
  labels and the listener's 105, about twice chance, where the same probe names 383 from the chart
  both towers heard. The image's roughly 168 classes do not survive to its end letter.
- **The readout loses a little, the state most.** The sibling's top face shows almost what its
  state keeps (103 against 111); the listener's face shows less (72 against 105).
- So a readout founded at the label cannot name the digit: what it would read is not there. The
  next loop is a section's memory, on all three media at once, since an answer needs its question
  and a transcript its utterance in the same way. The existing route is a ring founded at section
  arrivals, whose state is the phase-carried moment of its drive (`hnn.ring-moment-keys`,
  `hnn.tower-ring-founding`), read at the end letter by this probe beside the chart's 383.

## The recorded failures this step could repeat

- **A task's routine standing in for learning.** The charts are boundary codecs and the renderer
  is an exterior reading; nothing computes a label, an answer or a transcript. The probe is
  fitted outside the tower and never handed to it: it measures what the state holds, and no
  label it names is counted as the machine's.
- **Text as the exception.** Text, image (a pen's strokes: a motor chart) and sound enter as the
  same object, sections of one class passage, and the route has no modality branch.
- **Seen material graded as unseen.** The held-out images are disjoint from the training range,
  the speakers disjoint, the GSM8K problems the partition's development rows.
- **Bits read as progress.** Bits are reported beside the outputs. Labels stay at chance while
  the stroke code falls.
- **A refusal answered with a larger limit.** The first launch's composed run stopped at its
  declared early stop and was not relaunched with a larger deadline. Its partition changed: it
  ran alone, on a projection from a new measurement.

## Receipts

`2026-10-25_ONE_LISTENER_HEARS_GSM8K_MNIST_AND_SPEECH_AS_SECTIONS_OF_ONE_PASSAGE_receipts/`:
`RUNS.txt` (every training run's passes and measure lines), `READS.txt` (held-out reads by mark,
label confusions), `RELEASES.txt` (each release's prompt length and code, its length and whether
it ended), `BASELINES.txt` (conditional xz and bzip2, PNG and FLAC context), `PROBE.txt` (the reads
at the label with their times and digests, and every probe's training and held-out counts),
`MANIFEST.json` (the composition's configuration, inputs and written files with their SHA-256).

Times (projection → measured):

- The first launch planned four towers together on 24 cores. The host has 4. The composed run
  stopped at its declared early stop: 32 sections in 15,857 ms projected its pass past 480 s. The
  siblings, projected at 68, 72 and 53 s, took 204.5, 205.5 and 160.8 s (ratios 3.0, 2.9, 3.0).
  The projection error is the core count.
- The composed tower alone, projected at 672 s from that contended rate, took 258.8 s (0.385).
- Three more passes one tower at a time: composed 786 → 775.3 s, GSM8K 279 → 278.9 s, MNIST
  293 → 291.0 s, speech 213 → 199.2 s. Peak resident set 163,252 KiB.
- Reads took 3.4 to 5.7 s each and releases at most 14.2 s.
- The reads at the label, projected from 0.068 ms a class on 4 threads (deadlines 35, 15, 95 and
  15 s), took 21.3, 3.7, 62.3 and 9.9 s for the top face, and 32.0, 5.2, 89.5 and 13.9 s with the
  modes (class by class). The passage's training read came to 89.5 of its 95 s (0.94).
