# The field continues a ring's section word from what it retains

Refs #386 #73 #148. October 10. Follows the
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

## 2. The first read failed on my adapter: I read the wrong face

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

## 3. Measured: the field learns the word's composition, not its position

[measured] ([receipt](receipts/2026-10-10-retained-release/R1_FIELD_CONTINUES.v1.json); developer
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
