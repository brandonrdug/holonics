# A referent is dense by its identified readings, seven in ten of its laps run through a pronoun, and the held handle must key the bank

October 26. Refs #404, #405, #386, #410. **Grade.** Each claim carries one of these grades:
- [owned]: an existing owner states it.
- [measured]: read on this record's receipt or on a design record.
- [proved-derived]: proved here in a line.
- [agent-inferred]: a join made here, owed its construction.
- [interpretation]: a reading of a result in the objects.

The exact receipt is `referent_mass.py` in
[`…_receipts/`](2026-10-26_A_REFERENT_IS_DENSE_BY_ITS_IDENTIFIED_READINGS_SEVEN_IN_TEN_OF_ITS_LAPS_RUN_THROUGH_A_PRONOUN_AND_THE_HELD_HANDLE_MUST_KEY_THE_BANK_receipts/RUN.md).

**The lens.** Brandon, October 26, on the John audit (the audit thread's document, outside this
repository). The audit spoke of the tower's size. He reads the question as one of mass and
vorticity, as in a space-time fabric:
- the model may not register how dense the actors in a dialogue are, because they are not dense with
  connections in the way it learns;
- "he volunteers" is close, since it keeps the referent male, but the samples also turn to "she";
- "John" is four letters, so the model may have no reason to hold it as one dense, consistent object.

He pointed to Lai, Bao, Quinn and Gilpin, *Fractal basins trap latent reasoning* (arXiv:2609.04963),
as close in concept (§4).

**Computational object.** The helical pair interaction. Here it is the pair contact between a
mention and the referent the passage holds; its slip is a mention that does not close a lap on that
referent. Of the six general objects of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md), the record touches:
- the helix: the reset clock's handle, carried along the strand;
- the pair: the referent ⊗ role key;
- faces and placement: the key's phases on the harmonic box;
- cell holonomy: the referent's laps and what they transport.

The tube is the problem, the clocked span between two blank lines. The tower thread stays as the
tower has it.

## 0. The law in nine statements

1. **A referent is a class carried round the cycle of its mentions** [proved-derived, §3.1]. Take the
   passage's mentions in order as a path and identify the `k` mentions of one referent. That adds
   `k − 1` independent cycles, so `β₁ = Σ_r (k_r − 1)`. Each cycle is a lap from one mention through
   the passage back to the referent. Its holonomy is what the referent carries; for John the laps
   carry 2 a month to 24 a year to 72 hours.
2. **Its mass is its identified readings** [owned `spectro.reading-mass`; agent-inferred as applied].
   Each identified reading adds one unit along the referent's direction, so `M = M₀ + k`. The next
   reading moves it by the share `1/(M + 1)`, and the referent pulls that reading by `M/(M + 1)`.
   An unidentified mention lies outside the referent's span, has share 1 and moves the whole way: it
   founds a new referent.
3. **Mass is winding** [agent-inferred join of `spectro.reading-mass` and `spectro.basin-shape`]. A
   referent founded by one reading and identified `k − 1` more times has mass `1 + (k − 1)`: its
   founding plus one unit for each lap. The count of laps is a winding, and the rest mass is that
   count.
4. **Size and bits are blind to it** [owned `spectro.hidden-basins`; measured, §1].
   - "John" is cheap because it is the training text's most frequent opening name (210 of 4,523).
   - "he" occurs in 2,250 of 6,726 training problems.
   - Neither cost shows that, inside one problem, the referent is the passage's heaviest object.
   - In the training text, 70.0% of the referent's laps pass through a pronoun (16,547 of 23,628).
   - In the held-out John problem, the referent has mass 4, and all three laps pass through "he".
5. **The type carries a lock; the token carries the relations** [measured, §1; agent-inferred].
   - The type "John" spans 210 problems, each a different person: 100 distinct next words over 325
     mentions.
   - What the type keeps across problems is the sheet: he 181, she 2, both 6, none 21.
   - The relations belong to the token. They are founded at the problem's first mention, carried by
     mass and released at the blank line.
   - Retention keeps across tokens only what recurs (the sheet). Keeping a token's relations at the
     type would be recitation.
6. **The sheet is a half-turn lock** [interpretation; owned: the parametron's Ising lock of
   half-turn sheets].
   - An agreeing pronoun closes a lap on the referent; a disagreeing one founds a new referent.
   - In the terrain the lock is pinned: 3,379 single-sheet problems agree with their name's sheet and
     44 do not.
   - In the samples it slips: a she-sheet pronoun appears in 72 of 400, and the he-sheet holds 348 of
     436 pronouns.
7. **The held handle already reaches the sheet, and nothing carries the relation** [measured, §2].
   - The founded clocks raise "the answer's first mention resolves to John" from 11 of 34 (bankless
     foils, passes 4 to 7) to 9 of 10, 12 of 14 and 9 of 12 (the founded blank-line clock, the
     second lap, the third lap).
   - Across all 400 samples, "volunt-" appears 0 times and "shelter" once, never in an answer.
   - The bank binds an arrival to the face it came into. "volunteers" was bound after "John " and is
     asked after "He ", which is another face. The one thing those two places share in this problem
     is the referent, and the reset clock already holds it.
8. **The founding: the held handle keys the bank, and the write is gated by mass** [agent-inferred;
   spec in §5].
   - The key and the query add the held handle's face. Since `φ(s₁ + s₂) = φ(s₁) ⊙ φ(s₂)`, every
     binding becomes a product, referent ⊗ role.
   - The write's share is the barycentric `m/(M + m)`, with `M` the bank's own count at that key.
   - The count is released at the clock's reset.
   - Each change opens at zero, so the founded tower reads bit-identically to its twin until the
     covector moves it.
9. **Reference: a referent moves the problem from leaf to core** [agent-inferred join with
   arXiv:2609.04963, §4].
   - With no identified mentions, the passage's graph is a tree. Loop closure is linear on it and has
     no slow modes: locally fluent, globally loose, which is what the samples are.
   - Identifying mentions makes cycles. That is where the paper finds transient chaos: trapping near
     nearly-correct solutions, and positive Lyapunov exponents only on the core variables.
   - The samples' trap is such a near-correct solution: the right sheet and the right genre on the
     wrong token.

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
- a name resolves to itself;
- a pronoun resolves to the most recent referent of its sheet;
- with no such referent, a pronoun founds an unnamed one.

This is an observer rule. It lives only in the receipt and never in the machine.

| Read | Value |
|---|---|
| Problems opened by a sheeted name | 4,087 |
| Mentions resolved to the opener (mass), summed | 27,715 (mean 6.781 a problem) |
| Laps `k − 1`, identified through pronouns | 23,628 |
| Laps by the name's letters alone | 7,081 |
| Share of laps through a pronoun | 16,547/23,628 (0.700) |
| Answer re-mentions the opener: by name / by pronoun only / neither | 2,398 / 971 / 718 |
| Answers with a mention, every mention on the opener | 2,779 of 3,520 |
| Answers with a mention, first mention on the opener | 3,129 of 3,520 (0.889) |
| John: problems opened / mentioning him anywhere | 210 / 249 |
| John's problems: he only / she only / both / none | 181 / 2 / 6 / 21 |
| Single-sheet problems agreeing / against their name's sheet | 3,379 / 44 |
| (name, next word) pairs: distinct / mentions / once | 7,693 / 11,895 / 5,590 |
| After John: distinct next words / mentions | 100 / 325 ("has" 42, "buys" 31, "s" 29, "is" 18) |
| Training problems with "volunt-" / opened by a name | 7 / 6 (Brenda, Hadley, James, Janet, Mr, Nick) |

**The held-out problem** [measured, part B]. It is row 207, held out. In the question, "John" and "he"
both resolve to John; in the reference answer, "He" and "he" both resolve to John. The referent's mass
is 4 with 3 laps, and none of the laps is closed by the letters J-o-h-n.

## 2. What the samples say

[measured, part C] There are 400 committed samples, each a 400-byte release after the held-out John
question, from 7 sample files of October 26. A sample's answer is its text up to the first blank
line, which is where the blank line's clock resets. A sample starts with John (sheet he) as the only
referent; the question leaves exactly that.

| Group (samples) | With a mention | First mention on John | Every mention on John | Founds another | Any she |
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
- **Pooled mentions.** 346 of 581 mentions resolve to John.
- **Referent changes.** There are 232 changes over the 581 mentions.
- **Named persons founded.** The samples found 54 distinct named persons: Michael 21, Tom 9, Mr 8,
  Mark 6, Saturday 6, and others.
- **John by name.** 13 answers name John, and 19 samples name him anywhere.
- **The loop.** One founded-clock sample loops "he is means he is …" and holds 30 of that group's 55
  mentions. That is why the table reads samples, not pooled mentions.

**Carry of the question's words** [measured, part D]:

| Word | Training problems containing it | Answers carrying it | Samples carrying it anywhere |
|---|---|---|---|
| volunt- | 7 | 0 | 0 |
| shelter | 13 | 0 | 1 |
| month | 293 | 14 | 23 |
| year | 325 | 23 | 37 |
| hours | 641 | 124 | 165 |
| he | 2,250 | 160 | 241 |

The reference answer carries "volunteers" twice, with "year", "hours" and "he". [agent-inferred] The
samples carry the question's frequent words at rates near their training frequency and its rare words
not at all. The relation reaches the answer only where the training text already makes it likely, so
it is not bound to the referent.

## 3. The derivation

### 3.1 The laps of a referent

[proved-derived] Let the passage's mentions in order be the vertices `1..N` of a path, with `N − 1`
edges and one component. Identifying the `k` vertices of one referent gives `N − k + 1` vertices and
the same `N − 1` edges. Adjacent mentions become a loop edge, which still counts. The cycle rank is
then `β₁ = E − V + C = (N − 1) − (N − k + 1) + 1 = k − 1`. Identifying each referent's mentions in turn
adds its own `k_r − 1`, so `β₁ = Σ_r (k_r − 1)`.

Each independent cycle runs from one mention along the passage to the next mention of the same
referent and closes through the referent: a lap.

[interpretation] Along a lap the passage transports what the referent holds:
- John's first lap carries "twice a month for 3 hours" to the question "per year";
- the second carries it to "2·12 = 24 times a year";
- the third carries it to "24·3 = 72 hours".

The lap closes when the transported relation agrees at the return. A lap whose return disagrees,
such as "she" or a new name, does not close; it founds a new referent and leaves the relation behind.
The circulation round the referent's laps is the vorticity Brandon names: what the referent turns as
the passage goes round it. The helicity reading (`fluid.helicity-linking`) adds that relations linked
through one referent are linked to each other: "volunteers", "shelter", "twice a month" and "3 hours"
are linked through John.

### 3.2 Mass and its pull

[owned `spectro.reading-mass`]
- The law: `1/h′ = 1/h + 1`, and `vᵀw′ − vᵀw = (m/(M + m))(y − vᵀw)` with `m = 1`, `M = 1/h`.
- After `k` identified readings from a founding of mass 1, `M = k` and the next reading's share is
  `1/(k + 1)`.
- [proved-derived] The referent is the running mean of its readings: `w_k = w_(k−1) + (y_k − w_(k−1))/k`
  sums to `w_k = (1/k) Σ_(j≤k) y_j`.
- [interpretation] A dense referent pulls the next mention toward itself by `M/(M + 1)`. This is the
  fabric's curvature: a heavy referent bends a later mention onto itself.
- An unidentified mention lies outside the span: share 1, no mass, a new referent. In the samples
  that is 189 founded referents over 400 samples and 232 changes over 581 mentions.

### 3.3 Why the name's size misleads, and why bits do

[owned `spectro.hidden-basins`; measured, §1] The code length is the magnitude face, and it is blind
to the all-pass basins.
- "John" codes cheaply as the most frequent opening name, and "he" codes cheaply everywhere.
- Neither cost says which referent a mention closes a lap on.
- By its letters alone, John's referent in the held-out problem has no lap. Through "he" it has three.
- A learner that keys by letters sees 7,081 of the training text's 23,628 laps.

So Brandon is right that size misleads. The exact correction is that John is dense as a type, the
densest name in the terrain, and that the density that matters is the token's mass inside the
problem, most of it carried by pronouns.

### 3.4 Type and token, against the retention law

[owned: the retention law, CLAUDE.md; agent-inferred]
- **The type: the sheet.** Retention is the quotient sufficient for the admitted future. Across
  problems the future the type "John" admits is the sheet (181 to 2) and nothing of any one John's
  relations (100 next words over 325 mentions). The type keeps the sheet as a lock and never a
  relation.
- **The token: the relations.** The token lives between two resets of the blank line's clock. It is
  founded at the problem's first mention, gains mass at each identified reading, and its count is
  released at the reset. The binding it wrote stays only as the prior the hold `ρ` decays.

### 3.5 What the bank cannot do now

[owned `hnn.binding-bank-recall`, `hnn.binding-bank-delta-write`; measured, §2; agent-inferred]
- **Content keys only.** The bank's key reads the antecedent face and the arrival's face. A binding
  made in the question under "John " is read in the answer only where the answer's face matches it.
  "He " is not that face, so the read diffuses, and a key reached by diffusion is read only to its
  square root ([diffusion record](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md),
  statement 7).
- **The clock holds the referent and binds nothing.** The reset clock holds the problem's handle,
  copied at the output (`held_t`, `hnn::tower::clock`). It reaches the sheet at the opening, which is
  §2's rise from 11 of 34 to 9 of 10.
- **Nothing joins the two.** A copy at the output can bring back the handle's letters. John's answer
  needs "He volunteers", not "John", so the copy carries the wrong face of the referent for this
  answer and binds no relation.

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
  changes per iteration are our referent changes per mention, 232 of 581.
- **The near-correct trap.** The samples sit near a near-correct solution: the right sheet (348 of
  436 pronouns he), the right genre (a man doing a GSM8K action), the wrong token (no "volunt-", 54
  other named persons). The "he is means he is" loop is the same trap closed into a cycle.
- **Leaf and core.** On a tree, loop closure resolves every key in linear time and nothing is slow
  (diffusion record, statement 6). The core, where cycles exist, holds the slow modes. Identified
  mentions are what give a problem's graph cycles (§3.1). A learner that identifies no mention stays
  a leaf solver: fluent at each line, with nothing to close across lines.
- **The prediction for the founding.** Founding the referent moves the problem into the core. Their
  bifurcation says what to expect: the type-level fixed point (some man) should become a saddle that
  slows the passage before the token's relation is carried. So a first pass of the founding may pay
  in time near that saddle before it gains.
- **Escape directions.** Their escape directions at a saddle (unstable Jacobian eigenvalues) are the
  positive inertia of `S − θI` in the lap stopping rule (`contact.lap-stop-inertia`): the directions
  still owed a landmark or a founding.
- **Dissipation.** Their dissipation is our hold `ρ` and the count's release at the reset, which
  decay the stale referents.
- **The difference.** They probe float latents from sampled random states with observer statistics.
  Here carriers are exact, key streams are declared, and the read is a count.

## 5. The spec for design

**What it builds** [agent-inferred]. One founding on the binding bank (`hnn::tower::bank`), using the
blank line's reset clock (`hnn::tower::clock`, the class the pool founded), in the bank's own
notation:

```text
handle      h_t      = E(held_t)                     the held class's first-level face; zero before the first reset
key turn    s(k_t)   = 2^(−σ) (W_k a_t + W_k′ x^ℓ_t + W_h h_t + b_k)
query turn  s(q_t)   = 2^(−σ) (W_q [r̂_t, x^ℓ_t] + W_h′ h_t + b_q)
            φ(s(k_t)) = φ(2^(−σ)(W_k a_t + W_k′ x^ℓ_t + b_k)) ⊙ φ(2^(−σ) W_h h_t)       referent ⊗ role
count       C_t      = ρ (C_(t−1) + g_t φ(s(k_t))ᴴ)                                     one complex row, value 1
mass        M_t      = 1 + μ · Re(2^(−m) C_(t−1) φ(s(k_t)))                             what was written at this key
gate        g_t      = m_t / (M_t + m_t),   m_t = 2^(W_g x^ℓ_t + b_g)
release     C ← 0 at the clock's reset                                                   S keeps the binding as the prior
```

**Each choice, with its reason:**
- **`W_h`, `W_h′` and `μ` open at zero**, each part released to its grain before it is added, as
  `W_k′` is. At `M = 1`, `m/(1 + m) = 1/(1 + 2^(−(W_g x + b_g)))`: the founded bank opens on the
  present gate exactly, and reads bit-identically to its twin.
- **The product.** `φ_n(s₁ + s₂) = φ_n(s₁) φ_n(s₂)`, so the handle turns every binding the problem
  writes by its own phase.
  - A read under the same handle undoes the turn.
  - A read under another handle sees the binding turned by the difference of the two handles' phases.
    The bank already reads that through its box kernel `K` (`hnn.binding-bank-address`).
  - The role part (`W_k`, `W_k′`) is then free to bind "the subject's action" once per referent,
    instead of once per face.
- **The mass gate** is `spectro.reading-mass`'s share. The `k`-th write at a key moves the binding by
  `1/(k + 1)` when `m = 1`: a running mean, not an overwrite.
  - A dense referent resists a stray later write.
  - The delta rule's news `e_t` still writes only what the bank did not already say.
- **The release** ends the token at the blank line. The relation leaves no mass in the next problem,
  so the next John starts light (§3.4).
- **The covectors.** `∂g/∂y = ln 2 · g(1 − g)` with `m = 2^y`, as now, and
  `∂g/∂μ = −g(1 − g) R_t / M_t` with `R_t = Re(2^(−m) C_(t−1) φ(s(k_t)))`. The handle's covector
  reaches `W_h` and `W_h′` through the key and query phases exactly as `W_k′`'s does.
- **Every medium.** The handle is the arrival a clock holds after its reset class; nothing in the law
  names a language. In an image, acoustic or motor passage it is the first arrival after the clock's
  class, and a "pronoun" is any later arrival the bank identifies with it.

**Acceptance, fixed before the build:**
1. **Opening.** With `W_h = W_h′ = 0` and `μ = 0`, the held-out cells read byte-identical to the
   twin's.
2. **Certificate.** The founded pass codes the training text below its twin by more than the charge.
3. **The relation is carried** (decisive, held out). Take the held-out answer words that occur in
   their own question: 18,790 of 26,709 answer words in 747 problems (receipt part E). For John these
   are "He volunteers a year he volunteers for hours". For each such word, read whether its first unit
   takes the largest mass, in the founded pass and in the twin.
   - It passes when the words the founded pass gains (twin misses, founded takes) outnumber the words
     it loses (twin takes, founded misses).
   - The two counts are reported with the code on those cells beside them.
4. **The carry is the token's, not the type's** (the recitation foil). Re-read the held-out named
   problems with the opening name replaced at every occurrence by one name the training text never
   contains, declared before the run. Item 3's gained count must still exceed its lost count. A gain
   that needs the training name's history is recitation, not binding.
5. **John, read beside and shown whole** (never the bar). Take the 16 framed samples (8 key streams,
   one draw and two agreeing draws), read by this receipt's sample rules: first mention on John, every
   mention on John, any she, another referent founded, "volunt-" carried. Against them:
   - the third lap: 9 of 12, 9 of 12, 3, 3 and 0;
   - the reference answer: 1, 1, 0, 0 and carried.

**What it does not do.** It does not touch arithmetic. The markup's arithmetic (the tower right 13 of
250 in the audit) and the units that weld digits to operators are a separate blocker, under the
digit-word law (record `50bc405`).

## 6. A correction to the diffusion record

[measured, the audit] The
[diffusion record](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md)
§1 said the subject question asks the answer to reach "the name the question opened on".
- **For John that is wrong.** His reference answer opens "He volunteers" and never names him.
- **Which answers it fits.** The read it proposed (the bank's largest weight on the name's binding at
  the answer's opening) fits answers that name the opener: 2,398 of the 4,087 here.
- **What John's question asks.** It asks for the referent's sheet and its relation, which this
  record's §5 item 3 reads.
- The audit also showed that John is not a usable loop gate: every baseline is 0 of 16. This record
  keeps John only as a reading beside.

## 7. Where it enters

- **Design (Athena).** Build §5 on the blank line's clock, with its acceptance as fixed. The receipt's
  sample read runs unchanged on new samples:
  `python3 -I referent_mass.py TRAIN_JSONL PARTITION_JSON research/records`.
- **Lean, owed to #410:**
  - the cycle rank of a path with `k` vertices identified, `β₁ = k − 1`, and its sum over referents;
  - the iterated reading mass, `1/h_k = 1/h₀ + k`, and the running mean it gives;
  - the mass gate at `M = 1` equal to the logistic gate, `2^y/(1 + 2^y) = 1/(1 + 2^(−y))`;
  - the product key, `φ_n(s₁ + s₂) = φ_n(s₁) φ_n(s₂)`.

## 8. The recorded failures these choices could repeat

- **An authored routine standing in for learning.**
  - The handle is the pool-founded clock's held class, never a name list.
  - The receipt's name rule and pronoun lists are observer instruments. They stay in the receipt.
- **Recitation counted as generation.** Item 4's foil refuses a carry that needs the name's training
  history.
- **Seen material graded as unseen.** Items 3 and 4 read held-out problems only.
- **Bits read as progress.** The decisive item is a count of carried words, with bits beside it.
- **A located cause carried unrepaired.** §6 repairs the diffusion record's John claim before
  anything consumes it.
- **Text as the exception.** The handle is a clock's held arrival in any medium (§5).
- **Arrays and windows.** The token is a span between two resets of a clock, never a window.

## Receipts

`referent_mass.py` reads the training text and the committed samples with exact integers and
`fractions.Fraction`. Decimals are printed only as readings beside fractions.
- Parts: A, the terrain; B, the held-out problem; C, the samples; D, the carry; E, the spec's
  denominators.
- Result: `all 20 checks hold`.
- Projection, deadline, wall time and peak resident set are in
  [`RUN.md`](2026-10-26_A_REFERENT_IS_DENSE_BY_ITS_IDENTIFIED_READINGS_SEVEN_IN_TEN_OF_ITS_LAPS_RUN_THROUGH_A_PRONOUN_AND_THE_HELD_HANDLE_MUST_KEY_THE_BANK_receipts/RUN.md).
