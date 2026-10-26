# The clock gains only where its arrival recurs, so its join becomes a copy at the output, and its acceptance is fixed before the build

October 26. Refs #404, #405, #386. The read the
[pool record](2026-10-26_THE_POOL_CHOOSES_THE_BLANK_LINES_CLOCK_AND_ITS_PASS_CODES_ABOVE_ITS_TWIN_SO_NOTHING_IS_FOUNDED.md)
§5 named as next, the law it changes, and the acceptance of the changed law, fixed before it is
built. Grades: [measured] for what the observer printed, [definition] for the law, [agent-inferred]
for each reading and choice. Receipt:
[`HELD.txt`](2026-10-26_THE_CLOCK_GAINS_ONLY_WHERE_ITS_ARRIVAL_RECURS_SO_ITS_JOIN_BECOMES_A_COPY_AT_THE_OUTPUT_AND_ITS_ACCEPTANCE_IS_FIXED_BEFORE_THE_BUILD_receipts/HELD.txt).

Computational object: the helical pair interaction, here the pair contact between the cell's next
arrival and the arrival a clock holds, whose slip is `[u_(t+1) ≠ held_t]`. It touches two of the
winding guide's six objects: the helix (the clock's reset carried along the strand) and faces and
placement (the held class's face read at the output). The pair contacts of the levels, cell
holonomy, tube and tower thread stay as the tower has them.

## 1. Where the founded pass's held-out bits went

[measured] The observer's `held` mode read the held-out cells of the founded pass (`clockB8`) against
its twin's (`twin8`), parted by where each cell stands from the blank line's last reset. The founded
pass codes the 151,676 cells 12,813.3 bits above its twin.

| part | cells | twin, bits a cell | founded, bits a cell | difference, bits | a cell |
|---|---|---|---|---|---|
| before any reset | 231 | 4.047 | 4.101 | +12.6 | +0.055 |
| the held arrival itself | 746 | 5.261 | 5.331 | +52.6 | +0.071 |
| **repeats the held arrival** | 1,168 | 6.966 | 6.550 | **−486.9** | **−0.417** |
| elsewhere, 1–8 cells after the reset | 5,964 | 5.709 | 5.916 | +1,236.0 | +0.207 |
| elsewhere, 9–32 | 17,804 | 5.409 | 5.564 | +2,776.6 | +0.156 |
| elsewhere, 33–128 | 68,505 | 4.198 | 4.291 | +6,407.9 | +0.094 |
| elsewhere, past 128 | 57,258 | 3.555 | 3.605 | +2,814.5 | +0.049 |

- The clock gains on the cells that repeat the arrival it holds, and only there: 0.417 bits a cell,
  and the repeated arrival is the largest mass in 54 of those cells against the twin's 43.
- Those cells are 0.77% of the passage. Every other part pays, and the parts sum to the whole
  difference.
- The cost a cell is largest just after the reset and falls with distance from it: 3.6%, 2.9%, 2.2%
  and 1.4% of the twin's code in the four parts after the reset.

## 2. Why the first level's join pays everywhere

[agent-inferred]
- The join `O_A E(held_t)` adds a `d`-vector at every cell, and which vector depends on the held
  class. Over the held classes it is a table of rank at most `d`, a whole direction of the level's
  output for each class. Its use was at the repeats; its cost fell on every cell.
- The pool record measured that most of every clock's drop is the covector's slow part, which any
  face constant between resets carries with the frozen passage's hindsight (§5 there: the rest's
  clock alone carries 1,612 parts a million), and that the cost lies in `O`'s own steps. A table
  over the held classes is a face that can carry that slow part, and the normalized step fits each
  section's share of it.
- The decay with distance is measured, and its cause is not read here.

## 3. The law: the held arrival is copied at the output

[definition] A reset clock's join moves from the first level's output to the readout. It reads the
face the readout reads, `x_t` (the top face, on `2^(−16)`), and adds to the held class's logit
alone:

```text
z_t[held_t] += ⟨r_A, x_t⟩ + b_A          r_A: d entries on 2^(−24), b_A on 2^(−16), both opening at zero
G_(r_A) = Σ_t δz_t[held_t] x_t,   G_(b_A) = Σ_t δz_t[held_t],   δx_t += δz_t[held_t] r_A
```

`δz_t = p̂_t − q_t` is the readout's covector at the cell. Nothing else of the clock changes: it
resets when `A` arrives, holds the arrival that follows, and keeps only that class.

- **What it is.** The copy is the face table's `x`-alone block (`contact.face-table-blocks`: copy,
  agreement and rhyme are `x` alone). It is the pair contact between the next arrival and the held
  one, whose lock is the cancellation of the slip `[u_(t+1) ≠ held_t]`. The passage node lock reads
  the same lock at an offset its tree locates (`hnn.passage-node-lock`); here the clock's reset
  locates it. Its weight `⟨r_A, x_t⟩ + b_A` is read from the readout's own face, so whether the held
  arrival recurs at this cell is what the tower's state says.
- **Why it cannot carry the slow part.** At each cell its covector is one coordinate of `δz`, the
  held class's, and one row `r_A` serves every held class. A mean covector for each held class has
  no direction to land in. The first level's join had `d²` entries and one direction for each class.
- **Nothing returns through the encoding.** The held class is the passage's, and the copy reads the
  top face, not the held class's encoding.
- **Retention, medium, opening.** The clock's state is still the held class alone. The law names a
  class and the readout, so it is the same over every codec's units. With `r_A = 0` and `b_A = 0` a
  clocked tower reads every passage bit-identically to its twin.
- **How it learns.** By the tower's own certified step, as every family does, with its moments
  opened on its passage (`TowerLearner::open_moments`, `hnn.tower-founded-moments`).
- **What retires.** The first level's join `O_A`, its return through the encoding, and the reading
  of the join covectors at a level that only its pool used.

## 4. The pool at the copy's port

[agent-inferred: `contact.pool-founding`'s reading at the copy's port] The drop of each class's clock
is read at the readout's covector over the training passage, frozen:

```text
x̄_t = (x_t, 1)
M_A = Σ_(t held) δz_t[held^A_t] x̄_t        C_A = Σ_(t held) x̄_t x̄_tᵀ        drop_A = M_Aᵀ C_A⁺ M_A
```

- The drop is the square of the steepest first-order descent the copy can give per unit of the power
  it adds to its logit, as the first level's drop was at its join. It does not depend on the scale of
  `x̄`.
- `δz` is the readout's covector, so the pool needs no reverse scan: one forward read of each
  stream in the training pass's partition, from the four-pass bank state `bankA7`.
- Exact. `M_A` sums one product of `δz` with `x̄` a cell for each clock holding a class there:
  `1,319 × 65` integer products a cell. `C_A` is the passage's Gram less, in each stream, the Gram of
  the cells before `A`'s first reset there, read from the stream's running Gram at that reset. The
  pseudo-inverse is read by fraction-free elimination, and each drop is a ratio of exact integers.
- The pool is every class's clock and the rest's, `1,318 + 1 = 1,319`. The founded class is the top
  drop, whatever class it is. The rest's clock and the shares down the ranking are read beside.

## 5. The acceptance, fixed before the build

1. **The opening.** A clocked tower reads every passage bit-identically to its twin (a test), and
   the founded state's held-out cells are byte-identical to the twin's opening cells
   (`8163fb5d…b954`).
2. **The covector.** The copy's two families pass the tower's covector check (a test).
3. **The choice is the machine's.** The founded class is the top drop over the whole pool, read on
   `bankA7` over the training text. The top sixteen drops, the rest's clock and the spread are
   recorded.
4. **The certificate.** One prequential pass from the founded state codes the training text below
   the twin's pass `twin8` (5,636,231,354,399 on `2^(−20)` bits) by more than the choice's
   description, `log₂ 1,319 < 11` bits: below 5,636,219,820,063.
5. **The role, held out.** On the 97 held-out named problems whose answer opens with the name, the
   founded state's face at the answer's opening gives the answer's first unit the largest mass in
   at least 49, and in more than the twin's 1.
6. **John.** At least 12 of the 16 framed samples about John.
7. **Read beside, never the bar.** The held-out code, whole and by region, and the observer's
   `held` read by part.

If item 4 fails, nothing is founded, and the next loop's subject is where the copy's pass pays,
read by the same observer.

## 6. The recorded failures these choices could repeat

- **An authored routine standing in for learning (a copier).** The copy is the pair contact's lock,
  one block of the face table, and it opens at zero. Which arrival it holds is the pool's choice
  over every class, and where it fires is a weight read from the tower's state and learned from the
  passage. No rule names the name, the answer or its opening.
- **A located cause carried unrepaired.** The cause §1–§2 locate (a per-class face added at every
  cell) is repaired by the form of the join, not by a smaller rate, a hold or another pass.
- **An uncertified deposition step.** The founding is charged by its pass against the twin.
- **Bits read as progress.** Items 5 and 6 are behaviour; the code is read beside them.
- **Text as the exception.** The copy names a class and the readout.
- **A design thought in arrays and windows.** The clock's state is one class; nothing is kept by
  offset.
- **Seen material graded as unseen.** Items 5 and 6 are held out.

## 7. Where it enters

- Owner: `hnn::tower::clock` (`ClockDeclaration`, `Tower::join_clock`, the reset and the copy in
  the tower's forward, its reverse, `ClockPool`), the text line `clock <class> …`.
- Command: `found-tower-clock` without its level.
- Atlas: `hnn.tower-reset-clock` takes the copy's law; `contact.pool-founding` keeps the clock pool
  as a consumer.
- Lean, owed to #410: the reset clock's drop box changes to the copy's port,
  `drop_A = max_r {(Σ_t δz_t[held_t] ⟨r, x̄_t⟩)² : Σ_t ⟨r, x̄_t⟩² ≤ 1}`. Its context-table ceiling
  clause retires with the first level's join.
