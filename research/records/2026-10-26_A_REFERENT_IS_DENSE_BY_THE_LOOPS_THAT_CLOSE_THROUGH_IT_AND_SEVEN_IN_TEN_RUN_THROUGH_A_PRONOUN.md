# A referent is dense by the loops that close through it, and seven in ten run through a pronoun

October 26. Refs #404, #405, #386, #410. **Grade.** Each claim carries one of these grades:
- [owned]: an existing owner states it.
- [measured]: read on this record's receipt or on a design record.
- [proved-derived]: proved here in a line.
- [agent-inferred]: a join made here, owed its construction.
- [interpretation]: a reading of a result in the objects.

The exact receipt is `referent_mass.py` in
[`…_receipts/`](2026-10-26_A_REFERENT_IS_DENSE_BY_THE_LOOPS_THAT_CLOSE_THROUGH_IT_AND_SEVEN_IN_TEN_RUN_THROUGH_A_PRONOUN_receipts/RUN.md).

**The lens.** Brandon, October 26, on the John audit (the audit thread's document, outside this
repository). The audit spoke of the tower's size. He reads the question as one of mass and
vorticity, as in a space-time fabric:
- the model may not register how dense the actors in a dialogue are, because they are not dense with
  connections in the way it learns;
- "he volunteers" is close, since it keeps the referent male, but the samples also turn to "she";
- "John" is four letters, so the model may have no reason to hold it as one dense, consistent object.

He pointed to Lai, Bao, Quinn and Gilpin, *Fractal basins trap latent reasoning* (arXiv:2609.04963),
as close in concept (§4).

**His correction, the same day.** This record's first version (PR #498) specified a build. The bank
was to be keyed by the problem's first unit, so that "He" would read back "volunteers". Its write was
to be gated by the mass already written at a key. He rejected both:
- they read the passage as facts provided about a thing, filed under the person they are about,
  which is privileged;
- "volunteers" is an abstract term that would need much association before it means anything
  relative to an independent actor;
- the actor John is already an abstraction one can hardly hope to relate to gendered pronouns;
- that the gender split is visible at all is a surprise, and it fits an entropy lens: most languages
  mark masculine and feminine.

The build is withdrawn (§5). The law below is restated without facts and without a privileged
subject.

**Computational object.** The helical pair interaction. Here it is the pair contact between a
passage's present arrival and a region it has crossed before: a return closes a loop through the
region, and a crossing that does not return opens a new region. Of the six general objects of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md), the record touches:
- the helix: the clock's reset, carried along the strand;
- cell holonomy: the loops that close through a region, and the turn the passage accumulates going
  round them.

The pair, faces and placement, the tube and the tower thread stay as the tower has them.

## 0. The law in seven statements

1. **A referent is a region the passage keeps returning to** [proved-derived, §3.1]. Nothing is
   given to it and nothing is filed under it. Take the passage's mentions in order as a path and
   identify the `k` returns to one region. That adds `k − 1` independent cycles, so
   `β₁ = Σ_r (k_r − 1)`. Each cycle is a loop from one crossing along the passage back through the
   region.
2. **Its density is the loops that close through it, and its mass is its identified returns**
   [owned `spectro.reading-mass`; agent-inferred as applied]. Each identified return adds one unit
   along the region's direction, so `M = M₀ + k`. A later crossing moves the region by the share
   `1/(M + 1)` and is bent toward it by `M/(M + 1)`, as mass bends a path. A crossing that is not
   identified as a return has no mass, moves the whole way, and opens a new region.
3. **Mass is winding** [agent-inferred join of `spectro.reading-mass` and `spectro.basin-shape`]. A
   region opened by one crossing and returned to `k − 1` times has mass `1 + (k − 1)`: its opening
   plus one unit for each loop. The vorticity of the region is the circulation of those returns.
4. **Size and bits are blind to it** [owned `spectro.hidden-basins`; measured, §1].
   - "John" is cheap because it is the training text's most frequent opening name (210 of 4,523).
   - "he" occurs in 2,250 of 6,726 training problems.
   - Neither cost shows that, inside one problem, the passage returns to John more than to anything
     else.
   - In the training text, 70.0% of the loops through the problem's opening name close through a
     pronoun (16,547 of 23,628).
   - In the held-out John problem, the region has mass 4, and all three loops close through "he".
5. **What recurs across problems is the sheet, and it is found first** [measured, §1;
   interpretation; owned: the parametron's Ising lock of half-turn sheets].
   - The type "John" spans 210 problems and the passage does something different in each: 100
     distinct next words over 325 mentions.
   - What recurs is the sheet: he 181, she 2, both 6, none 21. Over every name with a sheet, 3,379
     single-sheet problems agree with their name's sheet and 44 do not.
   - The sheet is a half-turn lock. A return that agrees closes a loop; one that disagrees opens a
     new region.
   - [interpretation, the entropy lens] One sharp, strongly skewed split that recurs in nearly every
     problem with a person is the cheapest structure a code learner can locate. That is why it is
     visible at all: the samples hold the he-sheet in 348 of 436 pronouns.
   - Retention keeps across problems what recurs (the sheet), never what one problem's passage did
     there.
6. **The founded clocks bring the answer's opening back to the region, and the loops stop there**
   [measured, §2].
   - The founded clocks raise "the answer's first mention returns to John" from 11 of 34 (bankless
     foils, passes 4 to 7) to 9 of 10, 12 of 14 and 9 of 12 (the founded blank-line clock, the
     second lap, the third lap).
   - Later returns do not keep closing. Every mention returns to John in 100 of the 248 samples with
     a mention, 148 of 400 samples open another region, and a she-sheet pronoun appears in 72.
   - [agent-inferred] The region stays light: one return at the opening, then the passage drifts to
     the nearest cheap region, some man in a word problem.
7. **The reference: closed loops move a problem from leaf to core** [agent-inferred join with
   arXiv:2609.04963, §4].
   - With no identified returns, the passage's graph is a tree. Loop closure is linear on it and has
     no slow modes: fluent at each line, with nothing closing across lines, which is what the samples
     are.
   - Closed loops are where the paper finds transient chaos: trapping near nearly-correct
     solutions, and positive Lyapunov exponents only on the core variables.
   - The samples' trap is such a near-correct solution: the right sheet in a passage that no longer
     returns to its region.

## 1. What the terrain says

[measured, receipt part A] The training text is the audit's render `b` (SHA-256 prefix
`050b94f367625ad2`), 6,726 problems.

**Named problems.** Design's rule (`tools/listener/bank_trace.py`, `named`) counts 4,524 over
blank-line chunks. Per training row the same rule counts 4,523: one answer contains a blank line, and
its second half makes design's extra chunk.

**Person names.** A name is an opening word whose capital the sentence start does not explain: after
a lowercase word, its lowercase form never occurs, or occurs less often than the capital. This drops
17 opening words, among them "If" (75), "How" (8), "Since" (4) and "Amber" (6). It leaves 1,534 names,
of which 1,259 have a sheet. The sheets are he/him/his/himself and she/her/hers/herself. A name's
sheet is that of most of its single-sheet problems.

**Coreference rule.** A mention is a name or a sheeted pronoun:
- a name returns to itself;
- a pronoun returns to the most recent region of its sheet;
- with no such region, a pronoun opens an unnamed one.

This is the observer's rule for counting returns. It lives only in the receipt and never in the
machine, which must locate its own returns.

| Read | Value |
|---|---|
| Problems opened by a sheeted name | 4,087 |
| Mentions returning to the opener (mass), summed | 27,715 (mean 6.781 a problem) |
| Loops `k − 1`, identified through pronouns | 23,628 |
| Loops by the name's letters alone | 7,081 |
| Share of loops through a pronoun | 16,547/23,628 (0.700) |
| Answer returns to the opener: by name / by pronoun only / neither | 2,398 / 971 / 718 |
| Answers with a mention, every mention on the opener | 2,779 of 3,520 |
| Answers with a mention, first mention on the opener | 3,129 of 3,520 (0.889) |
| John: problems opened / mentioning him anywhere | 210 / 249 |
| John's problems: he only / she only / both / none | 181 / 2 / 6 / 21 |
| Single-sheet problems agreeing / against their name's sheet | 3,379 / 44 |
| (name, next word) pairs: distinct / mentions / once | 7,693 / 11,895 / 5,590 |
| After John: distinct next words / mentions | 100 / 325 ("has" 42, "buys" 31, "s" 29, "is" 18) |
| Training problems with "volunt-" / opened by a name | 7 / 6 (Brenda, Hadley, James, Janet, Mr, Nick) |

**The held-out problem** [measured, part B]. It is row 207, held out. In the question, "John" and "he"
both return to John; in the reference answer, "He" and "he" both return to John. The region's mass is
4 with 3 loops, and none of the loops is closed by the letters J-o-h-n.

## 2. What the samples say

[measured, part C] There are 400 committed samples, each a 400-byte release after the held-out John
question, from 7 sample files of October 26. A sample's answer is its text up to the first blank
line, which is where the blank line's clock resets. A sample starts with John (sheet he) as the only
region; the question leaves exactly that.

| Group (samples) | With a mention | First mention on John | Every mention on John | Opens another | Any she |
|---|---|---|---|---|---|
| Reference answer (1) | 1 | 1 | 1 | 0 | 0 |
| Bankless foils, passes 4–7, as written (64) | 34 | 11 | 8 | 26 | 10 |
| Banked, passes 4–7, as written (64) | 39 | 16 | 11 | 28 | 14 |
| Banked, passes 4–7, framed (64) | 45 | 29 | 17 | 28 | 13 |
| Bankless pass-3 tower, framing control (16) | 11 | 2 | 2 | 9 | 4 |
| Pool's blank-line clock, framed (16) | 10 | 9 | 9 | 1 | 1 |
| Its twin, framed (16) | 9 | 6 | 5 | 4 | 3 |
| Clock after "any" (16) | 9 | 7 | 7 | 2 | 1 |
| Second lap (16) | 14 | 12 | 8 | 6 | 4 |
| Third lap (16) | 12 | 9 | 9 | 3 | 3 |
| All 400 | 248 | 145 | 100 | 148 | 72 |

The table lists the groups that bear on the clocks; every group's row is in the receipt's output.
- **Pooled mentions.** 346 of 581 mentions return to John.
- **Region changes.** There are 232 changes over the 581 mentions.
- **Named regions opened.** The samples open 54 distinct named persons: Michael 21, Tom 9, Mr 8,
  Mark 6, Saturday 6, and others.
- **John by name.** 13 answers name John, and 19 samples name him anywhere.
- **The loop.** One founded-clock sample loops "he is means he is …" and holds 30 of that group's 55
  mentions. That is why the table reads samples, not pooled mentions.

**Words of the question in the samples** [measured, part D], read beside the rest and not as an
expectation:

| Word | Training problems containing it | Answers containing it | Samples containing it anywhere |
|---|---|---|---|
| volunt- | 7 | 0 | 0 |
| shelter | 13 | 0 | 1 |
| month | 293 | 14 | 23 |
| year | 325 | 23 | 37 |
| hours | 641 | 124 | 165 |
| he | 2,250 | 160 | 241 |

[interpretation] The question's frequent words recur in the samples at rates near their training
frequency, and its rare words do not recur at all. "volunt-" occurs in 7 training problems and is
abstract. Nothing in the passage's loops yet couples it to John's region, and nothing should be
expected to.

## 3. The derivation

### 3.1 The loops of a region

[proved-derived] Let the passage's mentions in order be the vertices `1..N` of a path, with `N − 1`
edges and one component. Identifying the `k` vertices that return to one region gives `N − k + 1`
vertices and the same `N − 1` edges. Adjacent mentions become a loop edge, which still counts. The
cycle rank is then `β₁ = E − V + C = (N − 1) − (N − k + 1) + 1 = k − 1`. Identifying each region's
returns in turn adds its own `k_r − 1`, so `β₁ = Σ_r (k_r − 1)`.

Each independent cycle runs from one crossing along the passage to the next return and closes
through the region: a loop. [interpretation] The holonomy of a loop is the turn the passage
accumulates going round it. A return that does not agree, such as "she" or a new name, does not
close the loop: it opens a new region instead. The circulation round a region's loops is the
vorticity Brandon names. By the helicity reading (`fluid.helicity-linking`), loops that close
through one region are linked to each other through it.

### 3.2 Mass and its pull

[owned `spectro.reading-mass`]
- The law: `1/h′ = 1/h + 1`, and `vᵀw′ − vᵀw = (m/(M + m))(y − vᵀw)` with `m = 1`, `M = 1/h`.
- After `k` identified returns from an opening of mass 1, `M = k` and the next return's share is
  `1/(k + 1)`.
- [proved-derived] The region is the running mean of its returns: `w_k = w_(k−1) + (y_k − w_(k−1))/k`
  sums to `w_k = (1/k) Σ_(j≤k) y_j`.
- [interpretation] A dense region bends the next crossing toward itself by `M/(M + 1)`. This is the
  fabric's curvature: a heavy region bends a later path onto itself, and it stores nothing to do so.
- A crossing that is not identified lies outside the span: share 1, no mass, a new region. In the
  samples that is 189 regions opened over 400 samples and 232 changes over 581 mentions.

### 3.3 Why the name's size misleads, and why bits do

[owned `spectro.hidden-basins`; measured, §1] The code length is the magnitude face, and it is blind
to the all-pass basins.
- "John" codes cheaply as the most frequent opening name, and "he" codes cheaply everywhere.
- Neither cost says which region a mention returns to.
- By its letters alone, John's region in the held-out problem has no loop. Through "he" it has three.
- A learner that identifies returns by letters sees 7,081 of the training text's 23,628 loops.

So Brandon is right that size misleads. The exact correction is that John is dense as a type, the
most frequent name in the terrain, while the density that matters is the loops inside one passage,
most of them closed by pronouns.

### 3.4 What recurs, against the retention law

[owned: the retention law, CLAUDE.md; interpretation]
- **Across problems.** Retention is the quotient sufficient for the admitted future. Across problems
  the future the type "John" admits is the sheet (181 to 2), and nothing that any one passage did
  around its John (100 next words over 325 mentions). The sheet is kept as a lock.
- **Within a problem.** The loops of one passage live between two resets of the blank line's clock.
  Keeping them past the reset would carry one passage's region into another.
- **The entropy lens.** The sheet is found first because it is the cheapest recurring split: one
  half-turn, skewed 181 to 2 for John, repeated in nearly every problem with a person.

## 4. The reference: fractal basins and transient chaos

[measured outside; cited] Lai, Bao, Quinn and Gilpin (arXiv:2609.04963, September 2026) treat a looped
reasoning model and a problem instance as a deterministic map on the latent state, with the solution
as a fixed point. They vary the initial latent state on random two-dimensional slices and label each
point by its convergence time.
- **Fractal basins.** Basins become fractal as tasks get harder. They read this with the basin
  entropy, the boundary entropy, and the uncertainty exponent `α` (`f(ε) ∼ ε^α`, boundary dimension
  `2 − α`). They see it on Sudoku-Extreme, mazes, Countdown and ARC-AGI-1, across four architectures.
- **Saddles decode to near-correct attempts.** Slow trajectories pass near saddles that decode to
  nearly-correct solutions: dead ends in mazes, grids with a repeated digit in Sudoku.
- **The fast Lyapunov indicator** follows the frequency at which a trace changes its decoded answer.
- **The training bifurcation.** Training a looped transformer on `Ax = b` over `F₃` (`M = N = 8`),
  near 150k steps the wrong fixed points lose stability and become saddles. Solving appears with
  transient chaos at the same time.
- **Core variables only.** Positive finite-time Lyapunov exponents appear only on the core variables,
  those that need multistep elimination. The leaf variables, which constraint propagation resolves,
  have none.
- **Slim fractals.** Where dissipation makes the saddle set decay, they read slim fractals
  (doubly transient chaos).

[agent-inferred] The joins:
- **Initial state and key.** Their initial latent state is our key, the navigators' initial
  configuration. The samples per state are a one-dimensional slice over key streams. Their answer
  changes per iteration are our region changes per mention, 232 of 581.
- **The near-correct trap.** The samples sit near a near-correct solution: the right sheet (348 of
  436 pronouns he) and the right genre (a man in a word problem), in a passage that no longer
  returns to its region (54 other named persons). The "he is means he is" loop is the same trap
  closed into a cycle.
- **Leaf and core.** On a tree, loop closure resolves every key in linear time and nothing is slow
  ([diffusion record](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md),
  statement 6). The core, where cycles exist, holds the slow modes. Identified returns are what give
  a problem's graph cycles (§3.1). A learner that identifies none stays a leaf solver: fluent at each
  line, with nothing closing across lines.
- **Escape directions.** Their escape directions at a saddle (unstable Jacobian eigenvalues) are the
  positive inertia of `S − θI` in the lap stopping rule (`contact.lap-stop-inertia`): the directions
  still owed a landmark or a founding.
- **Dissipation.** Their dissipation is our hold `ρ` and the clock's reset, which let the regions of
  a finished passage decay.
- **The difference.** They probe float latents from sampled random states with observer statistics.
  Here carriers are exact, key streams are declared, and the read is a count.

## 5. The build first specified here, withdrawn

[agent-inferred, withdrawn the same day] PR #498 specified two changes to the binding bank:
- the reset clock's held arrival in the key and query, so that each binding would be filed under the
  problem's first unit and "He" would read back "volunteers";
- a write gated by the mass already written at a key.

Both read the passage as facts provided about a subject, filed under the person they concern. That
is a store with a privileged subject, the picture the retention law refuses, and Brandon rejected
it. Neither is built. A region's density has to come from loops the machine closes itself, never
from a subject named for it.

## 6. A correction to the diffusion record

[measured, the audit] The
[diffusion record](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md)
§1 said the subject question asks the answer to reach "the name the question opened on".
- **For John that is wrong.** His reference answer opens "He volunteers" and never names him.
- **Which answers it fits.** The read it proposed (the bank's largest weight on the name's binding at
  the answer's opening) fits answers that name the opener: 2,398 of the 4,087 here.
- **What John's answer does.** It returns to the region by its sheet.
- The audit also showed that John is not a usable loop gate: every baseline is 0 of 16. This record
  keeps John only as a reading beside.

## 7. Where it enters

- **Design (Athena).** No build. The sample read runs unchanged on new samples, as a reading beside
  the output: `python3 -I referent_mass.py TRAIN_JSONL PARTITION_JSON research/records`.
- **Lean, owed to #410:**
  - the cycle rank of a path with `k` vertices identified, `β₁ = k − 1`, and its sum over regions;
  - the iterated reading mass, `1/h_k = 1/h₀ + k`, and the running mean it gives.

## 8. The recorded failures these choices could repeat

- **A store with a privileged subject** (this record's first version). Filing what a passage says
  under a named subject is an archive of facts, never retention. Refused in §5.
- **An authored routine standing in for learning.** The receipt's name rule, pronoun lists and
  coreference rule are observer instruments. They stay in the receipt and never enter the machine.
- **Seen material graded as unseen.** The samples are read only after the held-out question.
- **Bits read as progress.** The reads are counts of returns, with bits nowhere.
- **A located cause carried unrepaired.** §6 repairs the diffusion record's John claim before
  anything consumes it.
- **Text as the exception.** A region and its returns are stated on crossings of a passage, so the
  law holds for text, image, acoustic and motor input alike.

## Receipts

`referent_mass.py` reads the training text and the committed samples with exact integers and
`fractions.Fraction`. Decimals are printed only as readings beside fractions.
- Parts: A, the terrain; B, the held-out problem; C, the samples; D, the question's words.
- Result: `all 19 checks hold`.
- Projection, deadline, wall time and peak resident set are in
  [`RUN.md`](2026-10-26_A_REFERENT_IS_DENSE_BY_THE_LOOPS_THAT_CLOSE_THROUGH_IT_AND_SEVEN_IN_TEN_RUN_THROUGH_A_PRONOUN_receipts/RUN.md).
