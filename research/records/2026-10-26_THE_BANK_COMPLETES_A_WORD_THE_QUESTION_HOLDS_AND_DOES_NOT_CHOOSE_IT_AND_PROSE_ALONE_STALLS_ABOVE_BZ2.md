# The bank completes a word the question holds and does not choose it, and prose alone stalls above bz2

**Withdrawn, October 26.** The binding bank this record builds or measures is a key/query/value
store: a fixed grid of slots written by the delta rule, opened as an induction copier and first
accepted on a lookup benchmark (MQAR). An audit made at Brandon's request found it, and commit
`0934a25ff` retired it ([the
retirement](2026-10-26_THE_STORES_AND_COPIERS_ARE_RETIRED_AND_THE_PLAIN_TOWER_CODES_THE_SAME_BITS_WITHOUT_THEM.md)).
The measurements below stand only as measurements of that machinery, never as progress of the
learner, and nothing here is a design to resume.

October 26. Refs #404, #405, #386. Items 5 and 6 of the binding bank's fixed acceptance
([spec record §3](2026-10-26_THE_BINDING_BANK_IS_A_STRAND_CLOCKED_BY_ITS_ANTECEDENT_AND_A_RELEASE_IS_TRACED_BY_ITS_ADDRESS.md#3-spec-1s-acceptance-fixed-before-the-build)),
continued from the
[bank record](2026-10-26_THE_BANK_LOWERS_EVERY_MEDIUMS_HELD_OUT_CODE_AND_RECALLS_NO_SUBJECT_BOUND_AT_THE_OPENING.md)
with the key that reads the arrival. Receipts:
[`…_receipts/`](2026-10-26_THE_BANK_COMPLETES_A_WORD_THE_QUESTION_HOLDS_AND_DOES_NOT_CHOOSE_IT_AND_PROSE_ALONE_STALLS_ABOVE_BZ2_receipts/RUN.md).

Computational object: the helical pair interaction, the bank's strand clocked by its antecedent and
its arrival. The reads touch two of the winding guide's six objects: the helix (the bank's key and
query turns) and faces and placement (each held-out cell's code at its receiver's face, sorted by the
word that holds it and by what the training text holds). The pair contacts, cell holonomy, tube and
tower thread stay as the tower has them.

## 1. Item 6: the subject question (fails)

### 1.1 Four more passes on Brandon's PC

The PC's pass-3 GSM8K units tower (`towerA`, the bank record's §2) received the amended bank
(`join-tower-bank … level=0`, `O = 0`, `W_k′ = 0`) and four passes, one run each; beside the last
three the bankless tower continued from its fourth pass as the foil. Each banked pass continued the
held-out question about John on eight key streams, one draw and two agreeing draws, 400 bytes, as
written and framed (after the blank line that precedes every training question): 32 samples a pass,
16 for each foil.

| pass | banked held out | questions | answer prose | digits | markup | banked training read | foil held out | prompt code, banked as written / framed | foil | samples answering about John |
|---|---|---|---|---|---|---|---|---|---|---|
| 4 | 1.610 | 1.820 | 1.350 | 2.299 | 1.186 | 1.629 | 1.822 | 2.224 / 1.936 | 2.388 | 0 / 32, foil 0 / 16 |
| 5 | **1.597** | 1.811 | **1.334** | 2.289 | **1.170** | 1.560 | 1.803 | 2.507 / 2.386 | 2.670 | 0 / 32, foil 0 / 16 |
| 6 | 1.599 | 1.809 | 1.348 | **2.228** | 1.181 | 1.542 | 1.785 | 2.767 / 2.225 | 2.557 | 0 / 32, foil 0 / 16 |
| 7 | 1.598 | **1.801** | 1.339 | 2.304 | 1.197 | 1.532 | 1.774 | 2.716 / 2.057 | 2.598 | 0 / 32, foil 0 / 16 |

Bits a byte. The foil's regions are in `SAMPLES_PC_PASSES.md` with every sample, whole, as released.
John appears in four of the 192 samples, never in the volunteering question: two framed banked
samples open a new problem after `####` on John (`John has already has already…`, `John eats 1/6 as
much…`), one writes him inside an answer line (`…John spends the ceen a year.`), and one foil sample
opens a new problem on him. No sample holds `volunteer` or 72; the prompt's noun appears once, in a
banked loop `For a shelter, a shelter…`.

**What the passes show** [measured]:
- The banked held-out read is flat from pass 5 (1.597, 1.599, 1.598) while its training read falls
  from 1.629 to 1.532, below the held-out read from pass 5 on.
- The foil keeps falling (1.822 to 1.774), so the bank's lead narrows from 0.212 to 0.176 bits a byte.
- The banked tower codes the held-out question itself worse after pass 4 (2.224 to 2.716 as written).
- More passes at this constitution do not bring the subject: 0 of 128 banked samples answer about
  John against a bar of 12 of 16. This is the
  [diffusion record](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md#1-is-more-passes-the-remaining-key)'s
  §1 read on this tower: passes that found nothing finish the bridge and leave the held-out read where
  it was.

### 1.2 Where the bank's code goes in an answer

`read-tower-held-cells` writes each held-out cell's code (`2eb383691`); `held_cells.py copy` sorts an
answer's cells (answer prose and answer numbers) by whether the problem's question holds the word
(`[A-Za-z]+` or a number), by the word's kind, and by the cell's place in the word. The state is the
cloud bank record's amended-key pass from the original pass-3 tower (1.604 held out), read as it is
and with the bank's join `O` zeroed (1.822).

| answer word | its first cell, banked | its first cell, `O` zeroed | its later cells, banked | its later cells, `O` zeroed | words |
|---|---|---|---|---|---|
| a capitalised word the question holds | 6.40 | 6.81 | **6.42** | **13.92** | 1,841 |
| another word the question holds | 5.56 | 6.70 | **3.58** | **7.31** | 11,764 |
| a number the question holds | 5.46 | 5.86 | **3.57** | **5.27** | 3,750 |
| a capitalised word it does not hold | 5.29 | 5.31 | 4.86 | 4.79 | 1,761 |
| another word it does not hold | 6.41 | 6.45 | 5.23 | 5.73 | 5,333 |
| a number it does not hold | 4.60 | 4.62 | 3.07 | 4.19 | 5,120 |

Bits a word (the later cells summed over the words that have them); bits a byte and cell counts are in
`HELD_CELLS.txt`.

**The bank completes a word the question holds and does not choose it** [measured]:
- Once a question's word has begun in the answer, the bank pays half or less for the rest of it: a
  capitalised word (in these problems almost always a name) 6.42 bits for its later cells against
  13.92 without the bank.
- At the same word's first cell the bank saves 0.41 bits of a name's 6.81, 1.14 of another word's 6.70,
  0.40 of a number's 5.86.
- A name the question holds costs more at its first cell (6.40) than a name it does not hold (5.29):
  at the place where the answer names its subject, the tower does not expect the question's name.
- On words the question does not hold the bank saves almost nothing at the first cell (0.02 to 0.04
  bits); at their later cells numbers gain 1.12 bits, other words 0.50, names nothing.

**Why** [agent-inferred, from the bank's law]. The amended key `s(k_t) = 2^(−σ)(W_k a_t + W_k′ x^ℓ_t
+ b_k)` reads the arrival, so the first unit of a word the question bound becomes the address of the
rest of its binding: recall by content, which the bank does exactly (MQAR, 15,999 of 16,000). Choosing
the subject is recall by role: at the answer's opening nothing the query reads carries the name, and
the query must land on the key the name was bound under without it. This is the diffusion record's §1
statement, "a key read from content cannot serve a role query". Its decisive read, the share of the
4,647 training problems whose bank read at the answer's opening puts its largest weight on the binding
written at the question's name, needs the bank's read weights, which no command prints yet. The copy
read is its shadow in code, and it falls on the dormant branch: the first-cell saving on a question's
name is 0.41 bits, and the passes of §1.1 did not raise the subject.

**Where the role falls in the units** [measured on the committed GSM8K units; the consequence
agent-inferred]. Seven of the 1,062 founded units hold a newline: `.\n`, `\n\n`, `?\n`, `s\n`, `s.\n`,
`e?\n`, `s?\n`. Every training question opens after the unit `\n\n`, and its answer opens after the
question's last unit, `?\n` or one of its kin. The name is bound under the antecedent `\n\n` and the
answer's query reads `?\n`, two different units. On either key law the two land on one key turn only
if `W_k` and `W_q` carry those faces together, and the descent moves them there only if the read at
`?\n` already returns some of the name. It returns what last followed a `?\n` in the bank's hold: in
training the previous problem's answer opening, from rest nothing. That is the dormant step: the role "the first word of the passage's
line" is a face of the passage's clock (the line it is on and its place there), and no key reads it.

## 2. Item 5: prose (fails, by 0.061 bits a byte)

### 2.1 Where the byte tower's prose code goes

On the bank record's bankless pass 8 of the Holonics pair tower (3.083 on held-out prose),
`held_cells.py place` sorts each prose byte by the longest run holding it that the training text also
holds, and by its place in a word the training text holds (heard) or not:

| heard run holding the byte | 0–3 | 4–7 | 8–11 | 12–15 | 16–23 | 24 or more |
|---|---|---|---|---|---|---|
| bits a byte | 8.286 | 4.526 | 2.888 | 2.096 | 1.886 | 2.867 |
| bytes | 199 | 2,829 | 4,882 | 2,777 | 1,163 | 159 |

| byte | heard word, first letter | heard word, later letter | unheard word, first letter | unheard word, later letter | not a letter |
|---|---|---|---|---|---|
| bits a byte | 4.700 | 2.322 | 6.412 | 4.217 | 3.074 |

**The tower has not deposited the vocabulary it heard** [measured; `held_cells.py prefix`, an
observer's reference]. A heard word's later letter costs the tower 2.322 bits. Read from the heard
words' prefix counts alone, with no context beyond the word's own beginning, the same letters cost
1.427. By the letter's place in its word:

| letter | 2nd | 3rd | 4th | 5th | 6th | 7th and later |
|---|---|---|---|---|---|---|
| the tower | 2.857 | 2.720 | 2.281 | 1.715 | 1.694 | 1.550 |
| the prefix counts alone | 2.618 | 1.990 | 0.938 | 0.431 | 0.452 | 0.202 |

From the fourth letter on, the tower spells a heard word at two to eight times what its own heard
vocabulary leaves undetermined. A compressor that copies the heard text's long runs pays almost nothing
there [agent-inferred: bz2's code is not read by place].

### 2.2 The units tower on the Holonics text

The units law (`hnn::units`) founded 1,015 units on the Holonics training text: it reads in 815,454
units instead of 1,789,116 bytes, at an order-one code of 2.959 bits a byte against 4.059. Three passes
of the units tower with the bank record's declaration coded the held-out text at 2.587, 2.500 and 2.436
bits a byte, prose at 3.172, 3.094 and **3.041** (Lean 2.343, Rust 2.101, digits 2.259): below the
byte tower's eighth pass (3.083) and level with its banked pass (3.042), in three passes.

Units carry a heard word, with the non-letters after it, in 3.07 cells instead of 6.36 bytes, and its
bytes cost about the same (2.874
bits a byte against 2.902; unheard words 4.117 against 4.274). The units shorten the walk through a
heard word; they do not make it cheaper per byte.

### 2.3 Prose alone, bankless and banked

From the units tower's pass 3, prose-only passes over the training text's prose part (its first
524,316 bytes): bankless (`a`) from pass 3, banked (`b`) from pass 3 with the bank joined.

| run | held-out prose | Lean | Rust | digits | training read | prose with `O` zeroed |
|---|---|---|---|---|---|---|
| units pass 3, the start | 3.041 | 2.343 | 2.101 | 2.259 | — | — |
| `a1`, `a2`, `a3` | 2.879, 2.880, 2.881 | 2.438, 2.509, 2.577 | 2.208, 2.318, 2.409 | 2.961, 3.265, 3.877 | 2.191, 2.099, 2.054 | — |
| `b1`, `b2`, `b3` | 2.867, 2.849, **2.834** | 2.426, 2.474, 2.515 | 2.199, 2.291, 2.353 | 2.940, 3.349, 4.014 | 2.207, 2.090, 2.040 | `b3` 2.876 |
| `b4` … `b7` | 2.838, 2.837, 2.844, 2.838 | 2.555, 2.596, 2.652, 2.687 | 2.438, 2.513, 2.575, 2.662 | 4.397, 4.801, 5.818, 5.753 | 2.006, 1.976, 1.953, 1.932 | `b7` 2.886 |

**What prose alone shows** [measured]:
- **The first half of item 5 still fails**: the best held-out prose is 2.834 bits a byte, 0.061 above
  bz2 given the prose part of the training text (2.773, the bank record's declared bar).
- One bankless prose pass takes held-out prose from 3.041 to 2.879, and two more hold it there. The
  banked passes reach 2.834 at the third and hold it for four more, while the training read keeps
  falling (2.207 to 1.932): the passes fit what was heard and leave the held-out read where it was.
- **The second half holds again**: zeroing the bank's join raises held-out prose by 0.042 (`b3`) and
  0.048 (`b7`), back to the bankless passes' 2.88.
- Every other medium rises with every prose pass: the digits from 2.259 to 5.753, Lean from 2.343 to
  2.687, Rust from 2.101 to 2.662.

**Where the prose passes and the bank lowered the code** (`HELD_CELLS.txt`, `place` and `spans` on
the units cells): heard words 2.874 (pass 3), 2.712 (`a3`), 2.679 (`b3`), 2.708 (`b3`, `O` zeroed);
unheard words 4.117, 3.971, 3.834, 3.961. The bank's saving is largest where the training text helps
least: bytes whose longest heard run is 0–3 bytes cost 7.243 banked against 7.671 with `O` zeroed, and
unheard three-letter words 4.970 against 6.028. That is the bank's own law on held-out text: a word
bound at its first appearance in a chunk is recalled at its next [agent-inferred from the bank's law;
the read sorts cells, it does not trace the recall].

**The prose-only terrain is a diagnosis, not item 5's route** [agent-inferred, from the lesson on
text run as the exception]. It shows how far held-out prose goes when every contact serves prose,
and the tower pays for it in every other medium. Item 5 is owed on a tower that holds every medium.

### 2.4 Capacity, one timing read

Over the first 180,000 bytes of the prose part from scratch, a tower with 1,024 contacts read
held-out prose at 3.917 bits a byte after one pass, against 3.527 for 256 contacts, its certificate
halving its step 18 times against 8. A larger tower starts slower; whether its capacity closes the
0.061 needs several passes, and is owed.

## 3. Time

Every run's projection, deadline, measured wall time and peak resident set are in `RUN.md`. No run
stopped. On the PC the banked passes ran at 0.80 to 0.89 of their projections and the foils at 0.91 to
1.00; on the cloud host the passes ran at 0.76 to 0.97. Two departures, neither a raised limit: one
timing read's deadline (60 s) sat above its projection (35 s), and the first six prose passes were
projected on 258 sections where the prose part took 222.

## 4. The recorded failures these choices could repeat

- **Bits read as progress.** Item 6's bar is behaviour, and the bank's lower code stands beside 0 of
  128. The copy read says where the code goes, not that the subject is closer. The prose passes' 2.834
  stands beside the media it cost.
- **Text run on its codec's grain as the exception.** The prose-only passes raise every other medium
  and are recorded as a diagnosis; nothing in the bank or the tower names a medium, a word, a question
  or a role.
- **An authored routine standing in for learning.** The prefix counts and the compressors are an
  observer's references beside the tower, never a part of it. A role key, when built, is located by the
  bank's own deposition, never by a parser that marks a subject.
- **Seen material graded as unseen.** The held-out sets are the earlier records', fixed by SHA-256;
  "heard" means the training text holds the word or run, read from the training text alone.
- **A refusal answered with a larger limit.** No run was relaunched; each later projection used the
  largest window measured before its launch.

## 5. What is owed

- **Item 6, the subject question.** The diffusion record's weight-share read as a command (per
  training problem whose question opens on a name, whether the bank's read at the answer's opening
  puts its largest weight on the name's binding), run on the last banked state and every later pass.
  On the dormant branch the copy read shows, the step needs a founding, a key face that is the product
  of two faces (the passage's clock and the content), or a landmark, the role arriving as received
  material; the next loop builds the read and the founding together.
- **Item 5, prose ≤ bz2 on a tower holding every medium**: the banked byte tower is 0.269 above, the
  units tower's pass 3 0.268, prose alone 0.061. The vocabulary the tower heard is not deposited
  (§2.1).
- **Capacity**: several passes at 1,024 contacts.
- **Item 3, the card form**: the card still refuses a banked tower before a launch.
- **Lean, carried in #410**: `bank_recall_exact`, `bank_delta_overwrite`, `bank_chunk_eq_recurrent`.
