# The guarded witness: gate A's procedure with the executed release's descent as a commit guard (pinned before its run)

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for the law change and the rules; [measured] only in the receipt.

## 1. The law change

`hnn::executed::executed_move` adopts a successor only when, beside every earlier guard (including
the fixed mask's `C_mask(Θ′)⁺ < C(Θ)⁻`), the composition its own release executes is strictly lower
too: `C_own(Θ′)⁺ < C(Θ)⁻` by disjoint enclosures. A step refused only by this guard is typed
`TrialRefusal::OwnNotBelow`, and the ladder halves as before, at most `LADDER_DEPTH = 8` trials.

- **Why** ([the native direction](2026-10-01_THE_NATIVE_DIRECTION_MEASURED_THE_STEP_DESCENDS_THE_EXECUTED_RELEASE_WITHIN_ITS_CELL_AND_GATE_A_ADOPTED_SIXTEEN_TIMES_BEYOND_IT.md)).
  The mask's first order holds within the trajectory cell, about `1/32` of the unit step at the
  opening. Gate A's first move was adopted at `1/2`, where the executed release rose from
  `[500197/4096, …)` to `[517184/4096, …)` and locked class 3 at the far end.
- **The mathematics.** Within the cell the guard repeats the mask's. Past it, the move leaves the
  cell only while the executed comparison descends. On a fixed batch, the executed composition then
  falls strictly at every adopted move (`HNN/ExecutedComparison.disjoint_enclosures_decrease` on the
  own composition; nothing new is owed).
- **Symmetric across every arm**, as the 1b pin requires. Evaluation does not use the move, so the
  baseline replay must still match. The move's tests pass with the guard (25, including an
  assertion that every adopted move's own composition is strictly lower).

## 2. The run

- **Procedure.** Gate A's witness procedure, unchanged except for the guard:
  `hnn_prediction -- executed witness order2 2026093061 8 8 6974736 <out>/best.state <out>`. It
  starts from the founded opening, uses the lock face at the decisions, takes the same 8 development
  requests every epoch, and writes every constitution read as its complete continuing state
  (`c<k>.state`), so a later loop can continue from any of them exactly.
- **8 moves**, half gate A's 16. The question is the direction the guarded descent takes, which gate
  A's own trajectory showed from move 1 (class 3 at constitution 1). Each constitution's continuing
  state is written, so a continuation from `c8.state` is a resumption, not a rerun.
- **Every move prints** gate A's line, plus each trial's step, carried modulus, mask composition,
  own composition and refusal kind, and the incumbent's `γ_ρ`.

## 3. The outcome rules, fixed before the run

Comparisons are with gate A's 16 constitutions: solved at most 7, right at most 24, no whole
section, `γ_ρ < 0` at constitutions 0 to 2.

- **(G1) the guarded descent takes the route.** Some constitution reads `γ_ρ > 0`, and stations
  right above 24 or a whole section. The step law was gate A's blocker. The next loop continues from
  the written states toward gate A's matched budget, then the gate-B controls.
- **(G2) it descends without the route.** The executed `L` falls strictly at every adopted move,
  which the guard enforces, but `γ_ρ` stays negative and stations right stay at most 24. The covector
  at the decisions, nearly orthogonal to the descending route at the opening, leads elsewhere even
  under executed descent. The next subject is the composition's covector: which decision terms carry
  it.
- **(G3) the guard refuses a move.** No step in the ladder passes both guards. The executed descent
  along the native direction ends within 8 halvings of the start, and the refusal and its trials are
  reported.

## 4. Time, threads and the stopping rule

- **Measured units** (gate A's receipt, 24 threads): a move with one trial took 109,917 to 157,625
  ms, and a move with two trials 177,828 to 211,948 ms. A trial therefore costs at most
  `211,948 − 109,917 = 102,031` ms. A move with all 8 trials is projected at most
  `157,625 + 7 · 102,031 = 871,842` ms.
- **Projection.** 8 moves and the last read (at most 45,592 ms): `7,020,328` ms. The witness's own
  deadline is `6,974,736` ms, checked before each move, and the outer guard is `timeout 7021`.
- **Expected.** If the ladder adopts at its third trial, as the direction read suggests for move 0
  (`1/2` refused on the own release, `1/8` below), a move costs about 361,687 ms, and the run about
  49 minutes. The bound above is the deadline, not the expectation.
- **Threads.** `RAYON_NUM_THREADS=19`, beside nothing else.
- **Early stop.** The launcher stops the run when a move passes 871,842 ms since the last
  constitution line, reported incomplete.
- **The failures this could repeat**:
  - 5, an uncertified step: every guard stays a commit guard, and one more is added;
  - 7: the executed descent is the guard's consequence, not progress;
  - 9: fixed deadlines;
  - 1: nothing authored reaches the machine.
