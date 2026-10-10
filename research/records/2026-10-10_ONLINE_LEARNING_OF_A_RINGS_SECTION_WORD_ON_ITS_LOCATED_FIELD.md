# Online learning of a ring's section word on its located field

Refs #386 #73 #148. October 10. Renamed after Codex's source review of `6d13dd9c`: this record is the
**online-learning consumer** (refine, compare, deposit or discard, ingest, the receiver's code
scored). It calls no `ExecutionPort::release` and decodes no released cell or sample, so it makes no
retained-release claim. The original findings and receipts are kept as they were measured. Follows the
[bank record](2026-10-10_A_BANK_OF_RINGS_SOUNDS_ITS_EMISSION_ON_A_BOUNDED_LATTICE.md) §28–§29, where a
ring's section word enters the field declared on its located helix and is ingested whole.

## 1. The question (acceptance fixed before code)

[definition; agent-inferred, October 10] §28 established entry: the clean F1 section word (ring
`t = 1`, window `(120, 120)`, cycle `τ = 7` with support `{+1, −2}`) is founded, admitted and
ingested whole on its frames. Entry alone teaches nothing. The receiver's face is
`f_j = k(a_j)/L_R + R · P_R^(τ_R) v_R(e_j)`, the sum of:
- the landmark tree's face at the receiver's own suffix address;
- the wave's part through the receiving map `R`.

Both open at their declared priors (`R_0 = 0`) and move only by deposition from a compared target
(`hnn::receiving`, "R opens at zero and learns from the first deposit"). The question is whether the
field, through its own learning loop, comes to continue the ring's cycle: whether what it retains
predicts the next cell before that cell is read.

**The loop.** It is the receiving fixture's own sequence (`hnn::tests::receiving`,
`r_opens_at_zero_and_learns_from_the_first_deposit`), on the reference port:
1. Feed the word's first `τ` cells, ingested whole across the aeons.
2. Then, for each later cell `n`:
   - `refine` the moment at the admitted receiving phases (aperture 1), which publishes the face
     for cell `n` from the moment and the constitution alone;
   - `compare` it against cell `n`, encoded through the same chart;
   - `deposit`;
   - feed cell `n`.
3. **The twin** is the same field and feed, with the compare and the deposit withheld: its face
   stays at the declared priors and the moment's own counts.

**The frames.** The two carrying frames whose receiving cells equal the support, `[7, 2]` and
`[9, 2]`, are read with `field_on(helix.periods())` and the receiver declared there. On these frames
the alphabet is the cycle's own two classes.

**The readings**, exact:
- for every cell `n ≥ τ`, the actual cell's code-length enclosure at the refined face,
  `−log₂ p̂(cell n)` at the receiver's grain (`Face::code_length`), for the learner and the twin;
- the class of least code, reported with the advance it denotes (`+1` or `−2`).

Each cell is coded before its own deposit (prequential), so no cell is graded after the field has
read it.

**Acceptance.**
- **C1, the field learns the word.** On cells `60 … 119`, the second half, the learner's summed
  code-length enclosure lies strictly below the twin's: `upper(Σ learner) < lower(Σ twin)`. The
  per-cell series is reported, not only the sums.
- **C2, the field continues the cycle.** On the last two cycles (cells `106 … 119`), the class of
  least code at the learner's face is the actual cell at every cell. A tie, or a wrong class, is
  reported by cell.
- **C3, scope.** This is the online prequential code of one periodic word, the field continuing a
  cycle located in it. It is not the generation of new audio, it grades no unseen material
  beyond the word's own later cells, and it claims no learning across words.

**Recorded failures this design could repeat, and the guard against each.**
- *Seen material graded as unseen*: prequential order, each cell coded before it is deposited.
- *Bits read as progress*: the per-cell series and the least-code class with its denotation are
  reported, not a single number.
- *An authored routine standing in for learning*: only the field's own `ingest`, `refine`,
  `compare` and `deposit` act.
- *Recitation counted as generation*: C3. The continuation of a repeated cycle is claimed as that
  and nothing more.

**The read.** A development read on the first 30 cells of one frame gives the time per cell, and
the whole word's projection follows from it.

## 2. The first read failed on my adapter: I read the wrong face (the correction below is itself corrected in §4)

[measured] Developer read, frame `[7, 2]` only, 6886603002 ns. The test panicked at C1 after the
first frame.
- Learner and twin each coded cells `60 … 119` at exactly 60 bits: every cell at `[1, 1]` bit, the
  face uniform. C2 continued 0 of 14 cells.
- The learner's face moved on cells `8 … 24` (it favoured `+1`, coding `+1` cells below 1 bit), then
  returned to uniform from cell 25 on, for good. No aeon closed before cell 27.

Two causes were located from the deposit's own reading:
1. **The receiving map falls to zero.** `R` moves by every deposit, but its entries stay below the
   receiver's grain. The deposit at commit 18 (cell 24) releases them to zero (`DepositReading`'s
   `released` list: the below-grain release, atlas `hnn.below-grain-released`). With `R = 0` the
   combined face carries only the tree's grain logits.
2. **My reading was the wrong face.** `refine` publishes the combined face `q_C`. The receiver's code
   of a cell is its **population** over the landmark tree's face `q_T` and `q_C`, the two-family
   mixture `w_T q_T + w_C q_C` stepped cell by cell, which the receiving law scores at `compare`
   (`receiving_population`, ruling A, THE_REBUILD U1). The tree, which receives the deposited
   targets, never entered my reading.

[definition; agent-inferred] **The reading is corrected to the owner's law, before the next run.**
- Both the learner and the twin `compare` each cell against its target, and the code read is the
  compare's (`HolonRatio::code_length`, the population's), still before that cell's deposit.
- The learner then deposits; the twin discards the staged deposit (`ExecutionPort::discard`).
- C2's "greatest mass" is read through the code: on this two-class alphabet the actual class has
  mass above ½ exactly when its code is below 1 bit. C2 becomes: on cells `106 … 119` the learner's
  code enclosure has `upper < 1` at every cell.
- C1 is unchanged.

## 3. Measured: the field learns the word's composition, not its position (its C1 numbers are the combined face's; §4)

[measured] ([receipt](receipts/2026-10-10-online-learning/R1_FIRST_READS.v1.json); developer
reads.) Both frames, with the corrected reading. `acoustic_encoding` passes 10 of 10, wall
33272140661 ns.

- **C1 met on `[7, 2]` and on `[9, 2]`.** On cells `60 … 119` the learner's summed code is the
  enclosure `[2786561512655894101540777339391, 2786561512655894101770945273637] / 2^96` bits,
  strictly below the twin's exactly 60 bits. (`2^96 = 79228162514264337593543950336`, and the upper
  endpoint is below `35 + 1/5` times it.) The twin codes every cell at exactly one bit.
- **C2 NOT met: 12 of 14 on each frame.** The cycle is six `+1` advances and one `−2`, with the
  `−2` at cells `≡ 5 (mod 7)`.
  - On cells `106 … 119` the learner codes every `+1` cell below one bit.
  - Its two `−2` cells, 110 and 117, are each coded in
    `[200072836609431665706777441537, 200072836609431665710751374245] / 2^96` bits, between `5/2`
    and `13/5`.
  - The field predicts the cycle's majority, not its turn.
- **The two frames read identically.** With `R` at zero, only the receiving ring's tree acts, and
  the hidden ring changes nothing.

**Reading.** From what it retains and deposits, the field learns the section word's composition:
`+1` is six times as likely as `−2`, which takes the code from one bit per cell to below `35 + 1/5`
over sixty cells. It does not continue the cycle's position.

**The measured blocker, named by its measurements.**
- **The phase part dies below the grain.** The receiver's face carries the helix phase through
  `R · P_R^(τ_R) v_R`. That is the part that knows where in the cycle the word is, since the located
  navigator's lift is the cycle's position. Every deposit moves `R`, but its entries stay below the
  receiver's grain (`L_R = 16`), and at commit 18 they are released to zero for good.
- **The tree reads two cells back** (the receiver's declared depth `D = 2`, copied from the
  encoding tests' helper). Six `+1`s followed by a `−2` share their last two cells with most `+1`
  positions.
- **The depth is not the fix.** Raising `D` to the cycle's length would be a context window tuned to
  this task, which the no-catered-machinery law refuses. The position must come through the
  navigator's phase, so the next loop's subject is why `R`'s deposits stay below its grain on this
  field.

The C2 assertion records the measurement (`continued < 2τ`); it does not claim the acceptance.

## 4. Corrections from the source review of `6d13dd9c`, and the reading repeated

[measured] Codex's read-only review gave GO to the mechanics:
- each cell's refine precedes its compare, and the deposit or discard precedes its ingest;
- learner and twin are independent residents;
- aperture 1 puts no target into its own address;
- only `deposit` publishes the population, the tree and the material.

It found a **blocker in my source-to-record claim**, and I confirm it:
- §2's "correction" read `HolonRatio::code_length`, the **combined face's** code `q_C`, tree grain
  logits included. It did not read the population.
- The population's code is the compare's receipt, `ReceiptDetail::Compare { code_length, .. }`.
- So §2's "population" and §3's C1 numbers are the **combined face's**. That is a narrower scope than
  I stated, and they stand only under that name.

**The reading, repeated with all three codes side by side** ([receipt](receipts/2026-10-10-online-learning/R1_THREE_CODES.v1.json)). Developer read, both frames,
33181231084 ns. Each value below is the upper sum over cells `60 … 119` in units of `2^(−96)` bits;
the lower ends and the per-cell series are in the receipt.

| Frame | Population (`ReceiptDetail::Compare`) | Landmark tree's face alone | Combined face |
|---|---|---|---|
| `[7, 2]` | `2782450455824146995580402192893` | `2781621769690068407681731676749` | `2786561512655894101770945273637` |
| `[9, 2]` | `2782553182213765847538783259461` | `2781621769690068407681731676749` | `2786561512655894101770945273637` |

The twin codes exactly 60 bits under every face.

- **C1 met on the receiver's population code**, on both frames: strictly below the twin's 60.
- **The learning is carried by the landmark tree.** Its face alone is the lowest of the three.

**C2 is the majority baseline.** 12 of 14 is exactly what always betting `+1` scores: the cycle has
six `+1`s and one `−2`. The learner has not exceeded the cycle's composition.

**The receiving map's path, corrected.** §2 and §3 said `R` was "released to zero below its grain".
That was my reading of the `released` list, and it is withdrawn. The deposits at commits 16–20 show:
- the first deposits built `R` up to entries `±1/64` and `±1/128` (the map lattice `2^(−7)`, from
  the receiving width 4; the face grain `1/16` is a different grain);
- each later certified step moved entries one lattice unit, `1/128`, toward zero, until all were
  zero at commit 18;
- after that, every step's moves stay below one unit. The `released` lists are each step's sub-unit
  tails, which leave the carried entry unchanged (atlas `hnn.below-grain-released`).

So the descent itself removed `R`. On these cells, the map's reached feature did not lower the
combined code. "Zero for good" holds only on the measured prefix.

**Further scope, from the review.**
- The location, chart and `τ` are founded from the whole clean word before the loop. The causal
  prediction is conditional on that already-located chart; it is not blind discovery from the
  first seven cells.
- The source and the receiver are the same last ring. The receiving read rotates that ring's anchor
  only, so the longer ring's phase must reach it through contact and carry dynamics. Nothing here
  shows that it separates cycle positions.
- The copied contact declarations (`Y = 2`, `β = 2`, quarter-turns) may attenuate the hidden ring's
  influence.
- The population `2^24` sets precision, not the normalization.
- The test asserts C1, and `continued < 2τ` as measured; it does not enforce 12 of 14, both
  frames, or C2.

**The next observation on the phase path** (named by its measurement): the receiving map's
reached feature, per cell. That is the vector `R` multiplies in `R · P_R^(τ_R) v_R`. The questions
are whether it separates the cycle's seven positions at all, and why the certified steps descend
`R` to zero. The applied step, the carry, the tail and any prior move are read at commit 18.
Its acceptance will be fixed here before code. No depth increase, no authored cycle routine, and no
borrowed contact-only law for `R`.

## 5. O1: does the receiving map's reached feature separate the cycle's positions? (acceptance fixed before code)

[definition; agent-inferred, October 10, 14:15 UTC] The receiving map `R` acts on the reached
feature `f = P_R^(τ_R) v_R(e)`: the receiving ring's propagated state at the anchor. R's gradient at
a compare is `g fᵀ` (`Pullback::receiving`), where `g` is the logit covector
(`HolonRatio::covector`). For any `i` with `g_i ≠ 0`, `f = (g fᵀ)_(i,·) / g_i`, read exactly with no
new owner. The cycle's position is `n mod 7`; its `−2` sits at `n ≡ 5 (mod 7)`.

**The readings**, per cell `n ≥ τ`, for both the learner and the twin:
- `f_n` exactly;
- its equality classes over the cells;
- whether `f_n` repeats with the cycle (`f_n = f_(n+7)`) on the word's second half;
- the number of distinct values among the seven positions.

**The commit-18 decomposition.** The whole `DepositReading` at the commits that zero `R` is dumped,
read side by side with `R` before and after:
- the applied step and its moves;
- the carried entries and the sub-unit tails (the `released` list, `Map` and `Gram`);
- any `vanished` locus.

**Acceptance (a reading, not a learning claim).**
- **O1a.** For the twin, whose `R` and source material stay declared, the classes of `f` are
  reported, and the question is settled exactly: does `f` take a value at the `−2` positions that
  it takes at no `+1` position? A **yes** means a linear `R` can in principle single out the
  position; a **no** means this field's receiving read does not carry the cycle's position, and the
  blocker is the receiving read, not `R`'s steps.
- **O1b.** The same for the learner, where the source port `E` moves under deposits.
- **O1c.** At the commits that zero `R`, every entry's applied move is accounted to its step and
  its tail, and any prior move is named.

No depth, receiver or contact declaration is changed in this read.

### 5, measured (O1, 14:10 UTC)

[measured] ([receipt](receipts/2026-10-10-online-learning/O1_REACHED_FEATURE.v1.json); developer read,
34395027142 ns, both frames.)

**O1a and O1b: the feature carries the position only at a fine scale.**
- `f` has the form `(a, −a, b, −b)`. Over the last cycle `a` takes only `1/4`, `205/512` and
  `241/512`, rising and falling with the cycle, and the `−2` cell sits where `a` peaks.
- **On `[7, 2]`:**
  - 10 of the 16 `−2` cells share their feature exactly with some `+1` cell (twin), and 7 of 16
    for the learner. Exact equality alone refutes separation there: a linear `R` gives those cells
    the same logits.
  - In the last cycle, the `−2` cell 117 has `(a, b) = (241/512, 175/512)`, and its `+1` neighbour
    116 has `(241/512, 349/1024)`: equal `a`, and `b` differing by `1/1024`.
- **On `[9, 2]`:** no `−2` feature equals any `+1` feature, for either run.
- On neither frame does `f` repeat with the cycle on the second half; it drifts. The last cycle's
  seven positions show 7 distinct values (6 for the learner on `[9, 2]`).

**Reading.** Where the receiving read carries the cycle's position at all, it carries it at the
scale of `2^(−10)` in `f`. The receiving map steps on its lattice `2^(−7)`, and the face reads at
grain `1/16`. To lift a `2^(−10)` feature difference to one face-grain unit of logit, `R` would need
entries of order `2^6 = 64`.

**O1c: `R` is zeroed by its prior's moves, not by the descent.**
- At commit 17 the receiving map's chart reads `PriorMove { from: 7, to: 8 }`, and at commit 18
  `PriorMove { from: 8, to: 9 }`.
- Each move rescales the carried `W + r` by its new prior scale. That carries `R`'s entries
  (`±1/128` before commit 18) below the `2^(−7)` lattice, to zero.
- The certified steps' own moves stay below one unit throughout.
- §4's "the descent itself removed `R`" is withdrawn: the prior moves removed it.

**What O2 reads next** (choice (a) of the plan): the receiving map's prior-move law
(`NormalLaw::moved_prior`, `LocatedPrior`), and why its exponent rises at every commit here; then,
whether the learned `R` survives a move when its information sits below the new unit (`W` against
`r`). No declaration is changed until that law is read.

## 6. O2: the prior's verdict, and the receiver on the ring whose clock carries the cycle (acceptance fixed before code)

[definition] **The prior-move law, read** (`NormalLaw::moved_prior`; the
[prior carry's design](2026-10-04_THE_RECEIVING_PRIOR_IS_CARRIED_BESIDE_ITS_GRAM_AND_MOVES_TO_THE_CODES_CELL.md)).
- The receiving prior is a scale `2^k`. Its carried pair is the prequential code's alignment
  `a = A₀ + A₁ ln 2` and curvature `V = S ln 2`.
- After each deposit, the prior moves to its located member `k′`, the code's own cell, with
  `x = 2^(k − k′)`. The map's value becomes `W′ + r′ = x (W + r)`, its remainder carried. The Gram
  becomes `H′ = H + (2^(k′) − 2^k) I`.
- So `k` rising `7 → 8 → 9` at commits 17–18 is **the field's own prequential code judging that the
  receiving map's predictions from this feature cost more than they save**. Each move halves `R`,
  and on its `2^(−7)` lattice the halves carry to zero.
- This agrees with O1: the position reaches the receiving read only at `2^(−10)`, and on `[7, 2]` not
  at all.

[definition; agent-inferred, 14:20 UTC] **Why the receiving read misses the position, from the
helix.**
- The read is `f = P_R^(τ_R) v_R(e)`: the receiving ring's wave state, rotated by **its own** clock
  phase `τ_R`. In `field_on` the receiving ring is the last ring, of period `d_1 = 2`, so its phase
  carries one bit of the lift.
- The located helix's lift is `ℓ = τ_0 + d_0 τ_1`. The cycle's position, period 7, lives in the
  hidden ring's phase `τ_0` (period 7 on `[7, 2]`), the circle the carry turns. The receiving read
  sees it only through the contact dynamics, which O1 measured at `2^(−10)`.
- **Choice (derived, not tuned).** The receiver is declared on ring 0, the ring whose clock carries
  the located cycle. Its read's rotation `P_0^(τ_0)` then turns by the hidden ring's own phase.
  - This reads the located navigator's clock, a key the machine located itself. It is not a
    context window or a depth chosen to fit `τ`, and no authored routine enters.
  - The source ring, the chart, the contacts and the population are unchanged. Only the receiver's
    ring moves, from the helix's last ring to its first.

**Acceptance**, the same loop and readings as §1 and §4, on both frames, with the population code
from the compare's receipt:
- **C1′.** On cells `60 … 119` the learner's summed population code is strictly below its twin's.
- **C2′.** On cells `106 … 119` the learner's population code is below one bit at every cell. This
  exceeds the majority baseline, so the `−2` cells must also code below one bit. Reported by cell.
- **The receiving map's prior.** Its moves and `R`'s entries are reported at every commit, so the
  prior's verdict on this feature is read too.
- If the owners refuse a receiver on ring 0 (rank, observability, or the source's distance), the
  refusal is reported typed. It is not answered by another declaration in this read.

### 6, measured (O2, 14:14 UTC)

[measured] ([receipt](receipts/2026-10-10-online-learning/O2_RECEIVER_RING.v1.json); developer read,
55354059177 ns, both frames, both receivers.)

**With the receiver on ring 0:**
- **C1′ met on both frames.** The learner's population sum over cells `60 … 119` lies below the
  twin's 60 bits:
  - `[7, 2]`: upper `2783593195024518864581230590385 / 2^96`;
  - `[9, 2]`: upper `695959393141807318847851560653 / 2^94`.
- **C2′ NOT met: 12 of 14 on each frame**, still the majority baseline.
- **The tree's sum is unchanged**, identical to the last-ring receiver's
  (`2781621769690068407681731676749 / 2^96`). The tree reads the receiver's own suffix of cells,
  whatever ring the receiver sits on.
- **The reached feature now separates by exact equality** on both frames: no `−2` value occurs at a
  `+1` cell. But it has 14 coordinates (`[7, 2]`) or 18 (`[9, 2]`), entries at scales from `2^(−13)`
  to `2^(−7)`, with no cycle structure: it does not repeat with the cycle.
- **The receiving prior's verdict is sharper.** Its exponent rises by one at every commit from commit
  6 (`0 → 1 → … → 39` and on), halving `R` each time. On the last ring it had wandered
  (`… 5 → 6 → 3 → … → 9`). The field's own prequential code judges a readout of this feature
  costlier than none.

**Reading.**
- The receiving read is the ring's **wave state**, rotated by its clock phase. On neither ring does
  that wave state present the located cycle's position as a stable feature: it drifts, and its
  separation is accidental (exact inequality of noise-scale entries), not structural.
- The position is in the located lift's **clock digits** (`τ_0`, with the carry), which the wave read
  does not take as such.
- Moving the receiver's ring does not get past the majority. The blocker is the read's object, not
  its ring: the receiver addresses by received cells (the tree) and by wave state (the map), and
  neither is the navigator's clock.

**The next lawful route** (O3, read before any design): the receiving owners already address by
the clock. `hnn::tests::receiving` reads "the bundle letters … from the clock before the cell they
predict" (`the_bundle_letters_are_read_from_the_clock_before_the_cell_they_predict`, the
`FeatureFamily` of a campaign field). A receiver addressed by the located lift's clock, its carry-outs
and re-keyings, is the machine's own navigator read. It is neither a deeper context nor an authored
cycle routine. Its owner and declaration are read next, and an acceptance follows only from what it
actually offers.

## 7. O3: the receiver addressed by the located navigator's clock (design; acceptance fixed before code)

[definition] **What the owners offer.**
- The receiving tree's address is a register of typed bundles: each earlier tick's cell, plus the
  letters of a declared `FeatureFamily`. A `Feature::Phase { ring, grain }` letter is ring `g`'s phase
  class `λ_g mod d_g` at its grain, read from the retained clock before the cell it predicts. Its
  causality is Lean `Compression/Landmark/Context/Address.bundle_causal`.
- The reference port addresses every receiver by `letter_family(field)`, which returns
  `FeatureFamily::cells()` for every field: campaign 2's choice. On its development cells no
  clock-only or contact family coded below the constant control by its description charge.
- The clock letters are therefore built, causal and tested (`clock_letters`, `LetterReader`, the
  bundle tests), but no field can declare them.

[definition; agent-inferred, 14:25 UTC] **The change.**
- The letter family becomes the **field's declaration**. `Field::with_letter_family`, checked against
  the field's rings and grains, is read by `letter_family(field)`. The default stays
  `FeatureFamily::cells()`, so every existing field, test and receipt is unchanged.
- For the section word's field, the declared family adds `Feature::Phase { ring: 0, grain: d_0 }`:
  the hidden ring's phase class, the located helix's circle, which carries the cycle's position (§6).
- The choice is derived from the located helix, not fitted to the target:
  - it is the navigator's own clock digit, a key the machine located itself;
  - the tree's depth stays 2;
  - the letters' description charge is paid in the code exactly as the owner charges it.

**Acceptance**, the §1/§4 loop with the population code from the compare's receipt, on both frames,
receiver on the last ring, letters `cells ∪ {Phase(0, d_0)}`:
- **C1″.** On cells `60 … 119` the learner's summed population code is strictly below its twin's.
- **C2″.** On cells `106 … 119` the learner's population code is below one bit at every cell,
  beyond the majority baseline, so the `−2` cells too. Reported by cell.
- **C3″.** On both frames, the cell-only family's run (§4) beside it on the same cells: the code with
  the clock letter is strictly below the code without it, the letters' charge included. A clock letter
  that does not pay its charge is reported as such.
- **Owner checks.** The receiving tests and gate 1 pass with the default family. The new declaration
  refuses a phase letter on a ring the field does not have, and a grain that does not divide that
  ring's period.

**The lessons named.** A context window chosen for the task is refused, and the depth is unchanged.
The letter is the located navigator's clock, a machine key, and the frame `[9, 2]` (hidden period 9,
not `τ`) checks that the result is not authored to `τ = 7`.

### 7, measured (O3, 14:20 UTC): the clock letter carries the position

[measured] ([receipt](receipts/2026-10-10-online-learning/O3_CLOCK_LETTER.v1.json); developer reads.)

**A located cause, repaired at its owner.**
- The first clocked read was **refused by the port**: "the address register's clock against the
  lift point: expected 2, found 0".
- The register stepped its clock by the identity route's lock fit. A located passage's lift steps by
  the chart's own digits `a_g(c)`. The clock letters had only ever run on identity-encoded passages.
- `LetterReader` now steps ring `g` by the occurrence's located digit plus the carry
  (`tick_at`, `ActiveAddress::receive_at`, read by the reference ingest and by `clock_letters`), as
  the lift point does. The identity route is unchanged.
- A located register refuses, typed, to read known targets without their digits. That covers
  apertures above one on the located route, which are owed.
- The receiving tests pass 36 of 36, and the owner test of the declared family passes.

**The readings, both frames, receiver on the last ring, letters `cells ∪ {Phase(0, d_0)}`, depth 2:**
- **C1″ met.** On cells `60 … 119` the clocked learner's population code is, in exact enclosures
  strictly between `7/2` and `15/4` bits on each frame:
  - `[7, 2]`: `[148288478835922874514586366821 / 2^95, 296576957671845762176133800329 / 2^96]`;
  - `[9, 2]`: `[4633977272769413591120739187 / 2^90, 18535909091077655255947001381 / 2^92]`.

  The twin takes 60 bits.
- **C2″ met: 14 of 14 on each frame.** The `−2` cells code below one bit too. On `[7, 2]`, cells 110
  and 117 code at `[3866749768074556856415102649, 3866749768074557126833546071] / 2^96` and
  `[3636624065099927902837193747 / 2^96, 909156016274982047381353683 / 2^94]`. Both are below
  `1/16` bit.
- **C3″ met.** On each frame the clocked learner's upper bound lies below the cell-only learner's
  lower bound (about 35 bits), with the letter's description charge included.
- **`[9, 2]` passes as `[7, 2]` does**, though its hidden period, 9, is not the cycle's 7. The phase
  class reads the located lift, not a period authored to `τ`.
- Gate 1 passes. `acoustic_encoding` passes 10 of 10.

**Reading.**
- Addressed by the located navigator's own clock digit, the receiver's tree learns the ring's
  section word in its **position**, not only its composition. Over the second half it codes the
  word in under `15/4` bits for sixty cells, and the rare `−2` cell is predicted at under `1/16` bit.
- The position was never in the receiver's received cells or its wave state. It was in the clock the
  machine located, and reading that clock is what the change adds.

**Scope.** The online code of one clean periodic word, with its chart founded from the whole word
before the loop (§4). It is not the departed word, not the recording, not generation, and not a
release. The cell-only default and every other field are unchanged.
