# The bank's read at the answer's opening never reaches the name the question opened on, so the role step is dormant

October 26. Refs #404, #405, #386. The bank's address trace, spec 2's trace (b)
([spec record §4.2](2026-10-26_THE_BINDING_BANK_IS_A_STRAND_CLOCKED_BY_ITS_ANTECEDENT_AND_A_RELEASE_IS_TRACED_BY_ITS_ADDRESS.md#42-the-trace-law-agent-inferred)),
built and used for the read that decides the subject question
([diffusion record §1](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md#1-is-more-passes-the-remaining-key)):
after each pass, the share of named problems whose read at the answer's opening puts its largest
weight on the binding written at the question's name. Receipts:
[`…_receipts/`](2026-10-26_THE_BANKS_READ_AT_THE_ANSWERS_OPENING_NEVER_REACHES_THE_NAME_THE_QUESTION_OPENED_ON_SO_THE_ROLE_STEP_IS_DORMANT_receipts/RUN.md).

Computational object: the helical pair interaction, the bank's strand clocked by content. The read
touches two of the winding guide's six objects: the helix (the key's turn and the hold's decay
`ρ^L` along the strand) and faces and placement (where the read at one cell is placed among the
cells that wrote). The pair contacts, cell holonomy, tube and tower thread stay as the tower has
them.

## 1. The trace, built

[definition; agent-inferred] Unrolling the bank's write `S_t = ρ(S_(t−1) + w_t φ(s(k_t))ᴴ)`, with
`w_t = g_t e_t` the news cell `t` wrote, the read at cell `t` is a sum over the cells that wrote:

```text
v̂_t = Σ_(τ≤t) a(τ, t) w_τ,    a(τ, t) = ρ^(t−τ+1) · 2^(−m) Σ_n conj(φ_n(s(k_τ))) φ_n(s(q_t))
```

The address `a(τ, t)` is the hold's decay times the box's Dirichlet kernel at the turn difference
`s(q_t) − s(k_τ)`. It is one where the query's turn falls on the key's, and it falls off away from
it, so `|a(τ, t)|` says which earlier cell's binding the present read reaches.

- **Owners.** `hnn::tower::bank::BankTrace` and `Tower::read_bank_trace`; the command
  `complete-language read-tower-bank-trace`; the observer `tools/listener/bank_trace.py`; atlas row
  `hnn.binding-bank-address`.
- **Outside the machine.** An observer keeps the trace beside a frozen reading. The machine never
  keeps or consults it: it is no tape and no index, and the bank reads `S` alone.
- **What it keeps.** `ρ^L` is carried on `2^(−62)` and read on the address's `2^(−30)`. It releases
  to zero from `L = reach + 1` on, so every earlier cell's address is zero at that grain, and the
  trace keeps the last `reach` cells.
- **The consumer equation, checked** [measured, `the_bank_trace_returns_the_read`]: on a small
  banked tower over a 37-cell passage, `Σ_τ a(τ, t) w_τ`, released to the face's `2^(−16)`, is
  within one step of the bank's read on every cell and channel. The read reaches above `2^8` and
  the present cell's own term above 2, so the check is not met by small numbers. The reach is
  exact, and the passage is shorter than the reach.
- **Owed to #410:** `bank_read_is_addressed_sum`, the unrolled recurrence with the address as the
  decay times the Dirichlet kernel, beside the spec record's `bank_recall_exact`.

## 2. The read, as the diffusion record fixed it

- **A named problem** is one whose question opens on a word (a run of letters) that is capitalised,
  where the heard text holds that word capitalised more often than in lower case. That is the heard
  text's own reading of a proper name, with no list of names. It gives 4,524 named training
  problems and 421 named held-out problems. The answer opens with the name in 1,074 and 97 of
  them.
- **The request** is the read at the answer's first byte, with the trace's window opened at the
  problem's first byte, so the window holds every cell of the question. The name's cell is the
  class holding that first byte.
- **Where the read's largest address `|a|²` falls**, of five places: the name's cell at the
  question's opening; a cell holding a later occurrence of the name in the question; the read's own
  cell; another cell of the question; an earlier problem.
- **Beside it:**
  - whether the largest share `|a|² ‖w‖²` falls on the name;
  - the opening name's rank among the window's addresses (a cell with no address ranks last),
    beside the chance a uniform rank would give;
  - where inside the question the largest address falls, by quarter of the way from the name to
    the read.

The decisive share is the first place. A later occurrence of the name is reported beside it,
because its binding also writes the name.

## 3. What it measured

[measured] Brandon's PC read the bank of the four-pass record
([receipts](2026-10-26_THE_BANK_COMPLETES_A_WORD_THE_QUESTION_HOLDS_AND_DOES_NOT_CHOOSE_IT_AND_PROSE_ALONE_STALLS_ABOVE_BZ2_receipts/RUN.md)):
its join of the pass-3 GSM8K units tower, then the four amended-bank passes after it. Each read is
the frozen state over the whole text, cut into the held-out read's 8 chunks, each read from rest.

| read | text | join | pass 1 | pass 2 | pass 3 | pass 4 |
|---|---|---|---|---|---|---|
| **largest address on the opening name** | training (4,524) | **0** | **0** | **0** | **0** | **0** |
| | held-out (421) | **0** | **0** | **0** | **0** | **0** |
| the opening name first among the question's cells | training | 1 | 0 | 0 | 0 | 0 |
| | held-out | 0 | 0 | 0 | 0 | 0 |
| the opening name's mean rank, of 83.5 cells | training | 41.92 | 52.54 | 61.98 | 74.88 | 45.98 |
| | held-out | 42.35 | 54.82 | 62.41 | 72.97 | 47.41 |
| largest address on a later occurrence of the name | training | 6 | 79 | 105 | 133 | 147 |
| | held-out | 0 | 7 | 17 | 19 | 10 |
| largest share on the name | training | 1 | 77 | 100 | 154 | 167 |
| | held-out | 0 | 7 | 18 | 21 | 14 |
| largest address on another cell of the question | training | 408 | 2,770 | 3,544 | 2,659 | 3,374 |
| | held-out | 46 | 249 | 324 | 244 | 322 |
| largest address on the read's own cell | training | 0 | 48 | 72 | 170 | 42 |
| | held-out | 0 | 4 | 4 | 21 | 2 |
| largest address on an earlier problem | training | 4,110 | 1,627 | 803 | 1,562 | 961 |
| | held-out | 375 | 161 | 76 | 137 | 87 |
| `ρ` on `2^(−30)` | | 1,073,217,792 | 1,065,535,173 | 1,064,567,945 | 1,063,944,589 | 1,063,687,173 |
| reach, in cells | | 44,017 | 2,800 | 2,504 | 2,344 | 2,283 |

A uniform rank would put the opening name first in about 1 read in 72 (0.0139 to 0.0140 in every
read). Where the answer opens with the name, a later occurrence takes the largest address in
2, 31, 39, 54 and 46 of the 1,074 training problems, and in 0, 2, 4, 5 and 4 of the 97 held-out.

[measured, the cloud host] The bank record's own cloud join and its one pass read the held-out text
the same way:
- at the join, the opening name holds the largest address 0 times and a later occurrence 5 times;
- after one pass, 0 and 14 times.

Inside the question, the largest address lands by quarter of the way from the name to the read:

| state | text | quarter 1 | 2 | 3 | 4 | inside the question |
|---|---|---|---|---|---|---|
| PC join | training | 54 | 73 | 116 | 171 | 414 of 4,524 |
| PC pass 1 | training | 419 | 573 | 869 | 1,036 | 2,897 |
| PC pass 2 | training | 432 | 568 | 1,082 | 1,639 | 3,721 |
| PC pass 3 | training | 265 | 475 | 779 | 1,443 | 2,962 |
| PC pass 4 | training | 365 | 693 | 1,040 | 1,465 | 3,563 |
| PC join | held-out | 6 | 4 | 19 | 17 | 46 of 421 |
| PC pass 1 | held-out | 35 | 63 | 72 | 90 | 260 |
| PC pass 2 | held-out | 43 | 50 | 99 | 153 | 345 |
| PC pass 3 | held-out | 28 | 46 | 67 | 143 | 284 |
| PC pass 4 | held-out | 35 | 71 | 93 | 135 | 334 |
| cloud join | held-out | 29 | 30 | 24 | 41 | 124 of 421 |
| cloud, one pass | held-out | 40 | 57 | 85 | 128 | 310 |

The share reads are in [`SHARES.txt`](2026-10-26_THE_BANKS_READ_AT_THE_ANSWERS_OPENING_NEVER_REACHES_THE_NAME_THE_QUESTION_OPENED_ON_SO_THE_ROLE_STEP_IS_DORMANT_receipts/SHARES.txt).

## 4. What it decides

**The share the diffusion record named is zero at every pass and does not rise, so the role step is
dormant** [measured]. In 5 × 4,524 training reads and 5 × 421 held-out reads, the bank's read at the
answer's opening never puts its largest address on the binding written at the question's opening
name. By the diffusion record's §1, more passes at this constitution will not bring John. The step
needs a founding (a key face that is the product of the two faces, the one where the name was bound
and the one where the answer asks for it) or a landmark (the role arriving as received material).

**Counting later occurrences of the name does not change that** [measured]. They take the largest
address in at most 3.3% of the training reads. The rise slows pass by pass (73, 26, 28 and 14 more
reads), and on held-out it falls at pass 4. This is the four-pass record's recall by content: the
read reaches a word the question repeats, not the role the opening holds.

**What the passes learn instead is a shorter strand** [measured; the reading of it agent-inferred].
- The hold `ρ` falls from `1 − 2^(−11)` at the join to `1 − 0.0094` at pass 4, and the reach from
  44,017 cells to 2,283.
- Over a question's 83 cells, the decay alone is about 0.96 at the join and 0.45 at pass 4.
- The read's largest address moves out of earlier problems (91% of training reads at the join) into
  the question (79% at pass 4). Inside the question it leans to the end at every state: on the
  training text the last quarter holds 36–49% of those reads and the first quarter 9–14%.
- The opening name is the question's oldest cell, so a shorter strand weighs it least, and its rank
  sinks to 73–75 of 83.5 by pass 3. Pass 4 brings it back to the middle; this read does not say why.

The descent found the step it had, recency and content, and no step toward the role exists for it
to descend. That is the dormant branch, measured.

**The next loop's subject** is the blocker as measured: the bank's read at the answer's opening
lands on the question's opening name in 0 of 4,524 training problems at each of five passes. The
founding is located by the machine's own pool under the exact charge (diffusion record §3,
`contact.pool-founding`), never by a newline routine or a list of names, and it is accepted by this
same read.

## 5. Departures and corrections

- **The named problems are 4,524, not 4,647.** The diffusion record's 4,647 came from a definition
  it did not record. This record's definition is §2's, and the observer states it.
- **The cloud's training read stopped at its 215 s deadline** with seven of eight chunks read and
  nothing written. It was not relaunched with a larger deadline. The command now writes each chunk
  as it finishes (`97dbb00d4`), and the whole read ran on the PC under its own measured projection.
- **The cloud's held-out read at the join departed from the early-stop rule.** Its first chunks ran
  0.741–0.783 ms a cell against the 0.628 ms projected, because the join's reach of 44,017 makes
  each request scan more kept cells. It finished inside its 30 s deadline at 29.5 s. Its result
  stands as measured, and the PC projected requests separately because of it.
- **The opening name is first among the question's cells once.** The PC worker reported that it
  never ranks first. The share read shows one training read at the join where it is first among the
  question's cells, while a cell of an earlier problem holds the larger address. It never holds the
  largest address.
- **The PC and cloud series start from different joins**, each of its own host's pass-3 tower. Both
  read zero on the opening name.

## 6. The recorded failures these choices could repeat

- **Bits read as progress.** The decisive read is a share of addresses, never a code.
- **Seen material graded as unseen.** Training and held-out are read and reported apart; the
  held-out text was never trained on.
- **A refusal answered with a larger limit.** The stopped run was not relaunched with a larger
  deadline: what it keeps changed, and the next run's projection was measured.
- **An authored routine standing in for learning.** The trace and the name test are the observer's,
  and nothing here enters the machine. The name test reads the heard text's own capitalisation and
  holds no list of names.
- **A located cause carried unrepaired into a new consumer.** No further pass runs on this
  constitution for the subject question until the founding is built and this read accepts it.
- **Text as the exception.** The trace law is on the bank's cells, keys and decay, so it holds for
  any medium's bank. The named-problem test is only the observer's chart of this text.
