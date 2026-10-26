# The role key is a reset clock the pool founds, and its acceptance is fixed before the build

**Withdrawn, October 26.** The reset clock this record builds or measures is a copy pointer: it
holds the unit that arrived after a chosen class and raises that unit's logit at the output. An
audit made at Brandon's request found it, and commit `0934a25ff` retired it ([the
retirement](2026-10-26_THE_STORES_AND_COPIERS_ARE_RETIRED_AND_THE_PLAIN_TOWER_CODES_THE_SAME_BITS_WITHOUT_THEM.md)).
The measurements below stand only as measurements of that machinery, never as progress of the
learner, and nothing here is a design to resume.

Refs #404 #405 #386. Design record, October 26. Grades: [definition] for the object's law,
[agent-inferred] for each choice (its reason beside it), [measured] for the observer's pre-read.

The decisive read ([record](2026-10-26_THE_BANKS_READ_AT_THE_ANSWERS_OPENING_NEVER_REACHES_THE_NAME_THE_QUESTION_OPENED_ON_SO_THE_ROLE_STEP_IS_DORMANT.md))
found the role step dormant: after four passes the bank's read at a named answer's opening never
lands on the name the question opened on, and its hold shortened from a reach of 44,017 cells to
2,283. The diffusion record says why more passes do not reach it: a key that the passage reaches
only by diffusion is read to its square root, and a slow mode is founded, not waited for
([diffusion](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md)
§§1–3, `contact.pool-founding`). This record fixes the object that is founded, the pool it is
founded from, the charge, and the acceptance, before any of it is built or read.

## 1. The object: a reset clock and the arrival it holds

[definition] A **reset clock of class `A`** is a navigator's clock with one tick: it resets when `A`
arrives and holds the arrival that follows. Its resident face is that arrival's encoding, joined to
a level's output through a map that opens at zero:

```text
held_t     = u_t           when u_(t−1) = A        (the rest counts as a class: A = rest is the passage's first arrival)
           = held_(t−1)    otherwise;               nothing is held before the first reset
join       x^(ℓ+1)_t += O_A E(held_t)               O_A: d × d, opening at zero
covectors  G_(O_A)  = Σ_t δx_t E(held_t)ᵀ
           G_(E(u)) += Σ_(t: held_t = u) O_Aᵀ δx_t    (the paired adjoint through the encoding that produced the face)
```

`δx_t` is the covector of level `ℓ`'s output at cell `t`, the one the bank's reverse already reads.

- **Retention.** The clock's state is the held class alone. Nothing else of the passage is kept: it
  is the future-sufficient quotient of what the clock reads, no tape and no window.
- **Every medium.** A class is a codec's unit, so a reset clock is the same object over text, image,
  acoustic and motor units. [agent-inferred: the law names a class and an encoding, nothing of text]
- **The opening.** `O_A` opens at zero, so a founded tower reads every passage bit-identically to its
  twin, and the covector `Σ δx E(held)ᵀ` moves it from the first deposit.
- **Where it joins.** At the bank's level, `ℓ = 0`, after the bank. [agent-inferred: the role read
  asks the first level's join, where the bank reads `x⁰ = E(u)`, and the bank record measured the
  first level's face as the one a held arrival keeps its identity in]

## 2. The pool and its drop

[agent-inferred, from `contact.pool-founding`] The pool is generated symmetrically by the machine's
own navigators: one reset clock for every class and one for the rest, `|P| = 1,318 + 1 = 1,319` on
the GSM8K units. No class is named by the designer.

Each clock's drop is read at the join's covector over the training passage, frozen:

```text
c_A(t) = E(held_t)            M_A = Σ_t δx_t c_A(t)ᵀ        C_A = Σ_t c_A(t) c_A(t)ᵀ
drop_A = tr(M_A C_A⁺ M_Aᵀ)
```

[agent-inferred] Why this drop at a covector: the first-order change of the code when `O c` is
added is `Σ_t ⟨δx_t, O c_t⟩`, and its largest value over every `O` with `Σ_t ‖O c_t‖² ≤ 1` is
`√drop_A`. The drop is the square of the steepest descent the clock's face can give per unit of
the power it adds, so it does not depend on the scale of `E`. The present faces' own maps are at
their stationary point after the pass, so the covector carries no part they can absorb, and the
drop is the clock's novel part to first order.

- **Exact.** `M_A` and `C_A` are integer sums. `c_A` is constant between resets of `A`, so `M_A`
  is formed from prefix sums of `δx` at the reset cells: every cell starts one segment of one
  class, and the whole pool costs one pass and `O(N d²)`. The pseudo-inverse is read by
  fraction-free elimination, and each drop is a ratio of exact integers.
- **The ceiling.** `c_A` is a function of the held class, so the context table bounds the drop:
  `drop_A ≤ Σ_u ‖D_u‖²/n_u`, `D_u = Σ_(t: held_t = u) δx_t`, `n_u` the cells held at `u`, with
  equality when the held classes' encodings are independent ([owned] `contact.context-table-ceiling`).
  Both are read.

## 3. The charge and the certificate

[owned, `contact.pool-founding`; the reread's form agent-inferred] The top-ranked clock is founded
when a prequential pass over the training passage from the same state, with it joined, codes below
the same pass of its unfounded twin by more than the choice's description, `log₂ 1,319 < 11` bits.
The founded material is paid inside the prequential bits: each section is coded before its deposit.
If the top clock does not pay, nothing is founded, and the remaining tension is reported as the
diffusion record's §3 count.

## 4. The acceptance, fixed before the build

1. **The opening.** A founded tower reads every passage bit-identically to its twin (a test).
2. **The covector.** The clock's two families pass the tower's covector check (a test).
3. **The choice is the machine's.** The founded class is the top drop over the whole pool, read on
   the four-pass bank state (`bankA7`) over the training text. The top sixteen drops and ceilings
   are recorded. Whatever class it is, it is the one founded.
4. **The certificate** of §3 passes.
5. **The role, held out.** On the 97 held-out named problems whose answer opens with the name, the
   founded tower's face at the answer's opening gives the answer's first unit the largest mass in
   at least 49, and in more problems than the twin after the same pass.
6. **John.** At least 12 of 16 samples about John (the bank's item 6), on the framed prompt: the
   question preceded by the blank line the heard text puts before every question. The prompt as
   written, opening from rest, is reported beside it. [agent-inferred: a clock reads the class
   that resets it, and a passage opening from rest meets the rest's clock, not the separator's]
7. **Read beside, never the bar.** The held-out code, whole and by medium.

## 5. The observer's pre-read, outside the machine

[measured, on the training text with the committed units; an observer's tally, never a machine
input] Of the 1,074 named training answers that open with the name, the clock of the blank line
(`\n\n`) holds the answer's first unit at its opening in 1,072. The next clocks hold it in 159
(`does `) and 148 (`did `). The blank line precedes 4,522 of the 4,524 named questions. So the pool
holds a member that carries the role. Whether the drop ranks it first is the machine's read (item 3).

## 6. Where it enters

- Owner: `hnn::tower::clock` (`ClockDeclaration`, `Tower::join_clock`, the forward and reverse
  at the clock's level, the text line `clock <level> <class> …`), and the frozen reading of the
  join's covector `Tower::read_join_covectors`. The pool's drop is read in the same owner.
- Command: `found-tower-clock` beside the bank's commands in `solenoidal_alpha`.
- Atlas: a row for the reset clock, its consumer the tower's join; `contact.pool-founding` gains
  the clock pool as a consumer.
- Lean, owed to #410: the drop equals the context-table ceiling when the held encodings are
  independent, and never exceeds it.

## 7. The recorded failures these choices could repeat

- **An authored routine standing in for learning.** The pool is every class's clock; the drop picks
  the class; no name list, newline routine or parser enters. The observer's pre-read is not an input.
- **Text as the exception.** The clock names a class and an encoding only.
- **A located cause carried unrepaired.** The dormant step is not given more passes or a larger
  hold: the slow mode the diffusion law names is founded.
- **An uncertified deposition step.** The founding is charged by a prequential pass against its twin.
- **Bits read as progress.** Items 5 and 6 are behaviour; the code is read beside them.
- **Seen material graded as unseen.** Item 5 is held out, and the John prompt is a held-out question.
- **Arrays and windows.** The clock's state is one class; nothing is kept by offset.
