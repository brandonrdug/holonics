# The bank lowers every medium's held-out code and recalls no subject bound at the opening

**Withdrawn, October 26.** The binding bank this record builds or measures is a key/query/value
store: a fixed grid of slots written by the delta rule, opened as an induction copier and first
accepted on a lookup benchmark (MQAR). An audit made at Brandon's request found it, and commit
`0934a25ff` retired it ([the
retirement](2026-10-26_THE_STORES_AND_COPIERS_ARE_RETIRED_AND_THE_PLAIN_TOWER_CODES_THE_SAME_BITS_WITHOUT_THEM.md)).
The measurements below stand only as measurements of that machinery, never as progress of the
learner, and nothing here is a design to resume.

October 26. Refs #404, #405, #386. Items 5 and 6 of the binding bank's fixed acceptance
([spec record §3](2026-10-26_THE_BINDING_BANK_IS_A_STRAND_CLOCKED_BY_ITS_ANTECEDENT_AND_A_RELEASE_IS_TRACED_BY_ITS_ADDRESS.md#3-spec-1s-acceptance-fixed-before-the-build)),
read on the bank the
[first build record](2026-10-26_THE_BINDING_BANK_AT_THE_FIRST_LEVEL_RECALLS_THE_HELD_OUT_BINDINGS_AND_AT_THE_TOP_LEVEL_IT_RECALLS_NOTHING.md)
placed at the first level. Receipts:
[`…_receipts/`](2026-10-26_THE_BANK_LOWERS_EVERY_MEDIUMS_HELD_OUT_CODE_AND_RECALLS_NO_SUBJECT_BOUND_AT_THE_OPENING_receipts/RUN.md).

Computational object: the helical pair interaction, the bank's strand clocked by content. The reads
touch two of the winding guide's six objects, the helix (the bank's key turns) and faces and
placement (each byte's code at its receiver's face, sorted by the medium of the predicted byte). The
pair contacts, cell holonomy, tube and tower thread stay as the tower has them.

## 1. Item 5: prose

**What was read.** The pair tower of the mixed Holonics terrain at pass 7 (`hcont2`, the
[text record](2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md)'s
3.117 on held-out prose) received a bank at the first level (`join-tower-bank … level=0`, `O = 0`),
then one more pass over the training text. The bankless tower took the same pass from `hcont2` as
the foil. After training, `read-tower-held … unjoined` zeroes the bank's join `O` and reads the
held-out text again. The held-out read is the tower's own: the held-out text cut into 8 chunks of
6,004 bytes, each read from rest, every byte's code counted under the medium of the byte it predicts.

| learner | prose | Lean | Rust | digits | all |
|---|---|---|---|---|---|
| pass 7 (`hcont2`), the starting point | 3.117 | 2.431 | 2.172 | 2.324 | 2.511 |
| one more pass, bankless (the foil) | 3.083 | 2.402 | 2.117 | 2.351 | 2.488 |
| one more pass, banked | **3.042** | **2.341** | **2.079** | **2.312** | **2.444** |
| the banked pass with `O` zeroed | 3.085 | 2.409 | 2.132 | 2.346 | 2.493 |

Bits a byte; the exact codes on `2^(−20)` bits are in `HELD.txt` (prose: banked
38,311,483,436 / 12,009, the foil 38,820,416,306 / 12,009, zeroed 38,845,310,653 / 12,009). The
bank lowers every medium against the foil, by 0.041 on prose and 0.061 on Lean. Zeroing its join
returns each medium to within 0.015 of the foil's code: above it on prose, Lean and Rust, 0.005 below
it on the digits. **The second half of item 5 passes**: the read carries code, and removing it shows
that.

**The compressors given the training text.** `tools/listener/compressor_given_training.py` reads bz2
(level 9) and xz (preset 9, extreme) on the same held-out bytes. A piece's code is
`len(C(context + piece)) − len(C(context))`.

| read | context | pieces | bz2 prose | xz prose | bz2 Lean | xz Lean | bz2 Rust | xz Rust | bz2 digits | xz digits |
|---|---|---|---|---|---|---|---|---|---|---|
| `chunks\|all` | the whole training text | the tower's 8 chunks | 3.441 | 3.133 | 2.332 | 2.126 | 1.399 | 2.057 | 2.276 | 2.934 |
| `chunks\|own` | the medium's part | the tower's 8 chunks | **2.773** | **2.922** | 1.918 | 2.110 | 1.841 | 2.046 | 2.446 | 2.944 |
| `whole\|own` | the medium's part | one piece | 2.671 | 2.888 | 2.039 | 2.062 | 1.799 | 2.033 | 2.283 | 2.915 |

The training text runs prose, Lean, Rust, then the equations. bz2 sorts blocks of 900 kB, so given
the whole text it reaches a piece only through the last block, which holds the end of the Lean, the
Rust and the equations and no prose: its prose code rises to 3.441 and its Rust code falls to 1.399.
**The bar is declared here** [agent-inferred]: for each compressor, the lower of `chunks|all` and
`chunks|own`, both on the tower's own pieces and given no more than the tower was given. On prose
that is bz2's 2.773 and xz's 2.922.

**The first half of item 5 fails**: the banked tower codes held-out prose 0.269 bits a byte above
bz2 given the prose part of the training text, and 0.120 above xz. It is below both when they are
given the whole text. Against the same bar it is above bz2 on Lean (2.341 against 1.918) and Rust
(2.079 against 1.399), and above bz2 on the digits by 0.036 (2.312 against 2.276) while below xz there.

**A correction to the spec record.** Its §1 and §3.5 named "the 64 held-out prose pieces" and bz2
at 2.601. The tower's 3.117 was read at 8 chunks, in which prose falls in three pieces, and none of
the five readings above reproduces 2.601: the nearest is bz2 on the whole prose part read as one
piece, 2.671. The `n16|own` and `n64|own` lines in `COMPRESSORS.txt` show a compressor's conditional
code rising with the piece count alone (bz2 prose: 3.213 at 16 pieces, 4.852 at 64), so a reading that
does not state its pieces cannot be repeated. The spec record carries a dated note pointing here.

## 2. Item 6: the subject question (fails)

**What was read.** The original pass-3 units tower and its key streams are not on Brandon's PC, so
the units tower was rebuilt there with the units record's declaration and terrain: the committed
units, width 64, 64 modes, 256 contacts, 2 levels, 8 streams, sections of 128 units, rate `2^(−7)`,
the same training and held-out GSM8K text, and a fresh 1 MiB founding stream (so a different tower
under the same law). Its three passes read 1.963, 1.882 and 1.849 bits a byte held out, against 1.953,
1.876 and 1.839 for the original. It received a bank at the first level and one more pass; the
bankless tower took the same fourth pass as the foil. Each continued the held-out question about John
on eight fresh key streams, one draw and two agreeing draws, 400 bytes, opening from rest.

| fourth pass | held out, all | questions | answer prose | digits | markup | samples about John |
|---|---|---|---|---|---|---|
| bankless (foil) | 1.822 | 1.909 | 1.708 | 2.511 | 1.351 | 0 / 16 |
| banked | **1.607** | 1.818 | **1.343** | 2.294 | 1.209 | **0 / 16** |

The bank codes the held-out problems 11.8% below the foil and their answer prose 21.4% below. The bar
is 12 of 16 samples about John; none is. Every sample is in
[`SAMPLES_JOHN.md`](2026-10-26_THE_BANK_LOWERS_EVERY_MEDIUMS_HELD_OUT_CODE_AND_RECALLS_NO_SUBJECT_BOUND_AT_THE_OPENING_receipts/SAMPLES_JOHN.md),
whole, as released. Two observer reads, outside the machine:
- The bank carries one piece of the prompt: `shel` (from `at a shelter`) appears 38 times in three
  banked samples and never in the foil's.
- Six of the eight banked two-draw samples end looping on one phrase (`a sheld of watermine for…`,
  `a sheltural a sheltural…`, `her speed of her speed… speed speed`, `school cents in the school
  cents…`, `$500 + $500 +…`, `seconds seconds…`). No banked one-draw sample loops, and no foil sample.

**The blocker, by its measurement**: the banked tower recalls no subject bound at the passage's
opening (0 of 16 samples about John), and six of its eight two-draw releases loop on a phrase the bank
recalls.

**Why, as first read** [agent-inferred, from the law; §2.1 refutes it as the whole cause]. A key is
the face before the arrival. `John` is the prompt's first unit, so it is bound under the rest face.
In the training passage every question follows the separator after the previous answer (`#### n`
and a blank line), and the rest face is one no cell of the answer reproduces. The read returns what
followed the present face's last arrival: once the release writes `a sheld`, the next `a ` reads it
back, and the rewrite carries no news, so nothing damps the binding but the hold. It is an echo with
a round-trip gain near one, which two agreeing draws push over; one draw stays below.

### 2.1 On the original tower: the question framed, and the key that reads the arrival

The original pass-3 units tower is on the cloud host with its eight key streams, so the subject was
read there three ways, each after one more pass:
- **Framed.** The question preceded by the separator the training passage puts before every
  question (a blank line), so `John` is bound under the separator's face, as every subject in the
  training text is. The bankless pass-3 tower read the framed question as the framing's control.
- **The key reads the arrival.** The spec record's October 26 amendment (from the mathematics
  thread): `s(k_t) = 2^(−σ)(W_k a_t + W_k′ x^ℓ_t + b_k)`, `W_k′` opening at zero, so the bank opens
  bit-identically on the antecedent-only one. A key read from the antecedent alone gives every
  arrival under one face one key, the later overwriting the earlier, and cannot recall an arrival by
  its own content. Built in `hnn::tower::bank` with its covector; the covector check now reads
  eleven families and passes.

| learner (one pass after pass 3) | held out, all | questions | answer prose | digits | markup | prompt code, as written / framed | about John, as written | about John, framed | two-draw loops, as written / framed |
|---|---|---|---|---|---|---|---|---|---|
| bankless pass 3 (control) | 1.839 | 1.928 | 1.725 | 2.443 | 1.426 | — / 2.028 | 0 / 16 (units record) | 0 / 16 | — / 0 of 8 |
| bank, antecedent key | 1.604 | 1.811 | 1.348 | 2.243 | 1.217 | 2.185 / 1.940 | 0 / 16 | 0 / 16 | 3 / 2 of 8 |
| bank, key reads the arrival too | 1.604 | 1.816 | 1.346 | 2.253 | 1.200 | 2.456 / 2.172 | 1 / 16 | 0 / 16 | 1 / 1 of 8 |

Every sample is in
[`SAMPLES_FRAMING.md`](2026-10-26_THE_BANK_LOWERS_EVERY_MEDIUMS_HELD_OUT_CODE_AND_RECALLS_NO_SUBJECT_BOUND_AT_THE_OPENING_receipts/SAMPLES_FRAMING.md)
and every pass line in `PASSES_JOHN.txt`. The one sample about John is the amended bank's key stream
8, one draw, which opens `John takes Linume, Ley have 30 gallons, 9:00 * 3 = <<600*3=660>>720 feet`
and then drifts. Two other samples write `John` inside a new problem they opened after `####`. A loop
here is a sample whose last 150 bytes repeat with a period of at most 40 bytes over at least 60
bytes (an observer's read; no one-draw sample loops except one of the amended bank's).

**What this shows** [measured]:
- Binding `John` under the trained separator's face does not bring the subject back: 0 of 16 on
  the antecedent key, so the rest-face key is not the whole cause.
- The key that reads the arrival codes the held-out problems as the antecedent key does after one
  pass (1.604 both), loops less (2 two-draw loops in 16 against 5), and opens one sample on John.
  The subject's bar, 12 of 16, is not met by any learner.

**The heard text holds the copy** (an observer's read of the training text, outside the machine):
of the 4,647 training problems whose question opens on a name, 2,653 answers name it and 1,078 open
with it. So the relation the subject read asks for is in what the tower heard; one pass at rate
`2^(−7)` has not carried it into the bank's keys [agent-inferred]. The next loop trains the amended
bank further on Brandon's PC, where a banked pass takes about a fifth of the cloud host's time, and
reads John after every pass.

## 3. Time

Every run's projection, deadline, measured wall time and peak resident set are in `RUN.md`. The two
prose passes ran at 0.82 and 0.56 of their projections. On Brandon's PC, the first three-pass run
stopped itself at section 992 when a window ran past its bound; it was relaunched with that window's
time as its bound, not with a larger deadline. On the cloud host, the amended bank's first pass
stopped itself at section 64 (a mean of 815.6 ms a section against an 805.9 ms bound): its bound was
the antecedent-only bank's largest window, a measurement of another law. The amended law was then
timed on its own, beside the old one on the same 300 problems (the old one ran 7% slower than its
earlier read, the amended one 3% slower again), and relaunched on the largest window measured on the
amended law, 827.5 ms; it ran at 0.90 of that projection.

## 4. The recorded failures these choices could repeat

- **Bits read as progress.** Item 6's bar is behaviour (samples about John), and the 11.8% lower
  code stands beside its failure. Item 5's bits stand beside the compressors, under a bar declared
  before reading the tower against it.
- **Seen material graded as unseen.** The held-out Holonics text and the held-out GSM8K problems are
  the earlier records' held-out sets, fixed by SHA-256; no training text enters a held-out read.
- **An authored routine standing in for learning.** The compressors are exterior readings beside the
  tower, never a part of it; nothing in the bank names a subject, a separator or a phrase.
- **A refusal answered with a larger limit.** Each run that stopped itself was relaunched with a
  bound measured before the new launch, on the law being run, and its deadline from that projection;
  no running run's limit was raised.
- **Text run on its codec's grain as the exception.** The same bank and commands read the MQAR class
  terrain, the Holonics bytes and the GSM8K units.

## 5. What is owed

- Item 5's first half, held-out prose at or below bz2 given the prose part of the training text:
  0.269 bits a byte to close.
- Item 6, the subject question: 1 of 16 at best against a bar of 12; the amended bank trained
  further, read after every pass, and the release's echo through its own bindings.
- Item 3, the card form: the card now refuses a banked tower before a launch
  (`the_card_refuses_a_banked_tower`).
- Lean, carried in #410: `bank_recall_exact`, `bank_delta_overwrite`, `bank_chunk_eq_recurrent`.
