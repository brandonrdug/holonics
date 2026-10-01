# The order as a term of the comparison (pinned before its run)

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [definition;
agent-inferred] for the law; [measured] for §1 and in the receipt.

## 1. What the release's first order looks like at c6

[The decision margins](2026-10-01_THE_DECISION_MARGINS_THROUGH_THE_ACCEPTED_MOVE.md) found that a
wrong first lock leaves the comparison reading the open section, while the release decides every
later station in contexts no term reads. The release picks its first lock by its own law: every
unlocked station whose top candidate flips and locks is eligible, its gap is the top's `lower` less
the largest other `upper`, and the stations of the largest gap lock (`bank_release`, `LockOrder::Gap`).
At the guarded witness's c6, before and after the accepted move (receipts here):

- every station is eligible in every request;
- 7 of 8 requests have an eligible station whose top is its target (request 1 has none);
- the first lock goes to the largest gap: the far station 7 in 6 of 8 requests, with a wrong top
  in 4 of them. Where the first lock is wrong (6 of 8), the wrong station's gap dwarfs the right
  stations'. Request 2 reads `60261/4096` against at most `2193/1024` for a right one; request 7
  reads `7777/1024` against `5309/8192`.

The far end's dominance of the order is the segment probe's mechanism: at the founded transport the
request's weight at the far station is large. So the order is where `ρ` acts on the decisions, and
it is the one decision no term of the comparison reads.

## 2. The order term

[definition; agent-inferred] The first lock is itself a lock: the stations compete, and the
largest gap wins. Read as a normalized receiver over the stations, its comparison is the log ratio
of the whole to the right part, the lock face's own form one level up.
- At each request's decision refinement `r*`, take the eligible stations `E` with their release
  gaps `g_s` (exact rationals: the quantity the release compares).
- Let `R ⊆ E` be those whose top is their target, and `r = argmax_R g`. With `S = {r} ∪ (E ∖ R)`
  (the other right stations do not compete against `r`):

```text
ℓ_o = log(Σ_S g / g_r) = log(1 + Σ_(E∖R) g_x / g_r),     solved  ⇔  g_r > Σ_(E∖R) g_x   (⇒ the first lock is right)
```

- The solved test is one exact rational comparison, and it implies the release locks a right
  station first. Its excess is `(ℓ_o − ln 2)_+`, as for every lock face.
- Its covector on the gaps is the lock face's: `∂ℓ_o/∂g_x = (θ_x − [x = r])/g_x`, with
  `θ_x = g_x/Σ_S g`. On the readings it is `dg = a_top du_top − a_runner du_runner`, carried by the
  top's and the runner's leading members' covectors, which the proposal already holds for every
  station at `r*`.
- A request with `R` empty (no right top anywhere) has no order term: its stations' own lock faces
  must make a right top first.

**The declared comparison.** `Composition::LockOrder`: the lock face's terms plus one order term per
request, under the same guards, readings and metrics. The order term's first-order bound encloses
`a_top`, `a_runner` and the members' pairings as the lock face's does. The witness's form adds the
order receiver's normalized Jacobian over `S`, with no resting sheet.

**Lessons it could repeat.** 1 (an authored routine): the order is the release's own gap rule, its
targets the declared targets; no order is authored. 7 (a count as progress): the outcome reads
decisions. 5 (an uncertified step): every guard stays.

## 3. The run

`executed move-once order2 2026093061 8 <out> c6=<c6.state> order-dec witness`: the arm
`order-dec` (`Composition::LockOrder` at the decisions) under the witness's metric, one move from the
same restored c6. The lock face's own witness move from c6 is the control, already measured: adopted,
stations right 13, first locks right 3 of 8.

**Outcome rules:**
- **(O1) the first locks come right.** The move is adopted and more requests lock a right station
  first than c6's 2 of 8, with stations right above 15. The order term reaches the decisions.
- **(O2) adopted without more right first locks.** Report the order terms' values before and after
  and the gap ratios. The term moved in its smooth face but not past its solved level.
- **(O3) refused.** Report the refusal kinds. A refusal here, against the lock face's adoption from
  the same state, is the order term's own obstruction.

## 4. Time

The unit is the witness's move from c6 under the lock face, 249,390 ms with 3 trials. Its bound,
with up to 8 trials, is the coordinate move's 440,346 ms plus the plane's 78,889 ms, 519,235 ms. The
order term adds no release read: its terms reuse the readings at `r*`. Projection 519,235 ms,
`timeout 520`, per-line bound 519,235 ms, 19 threads.
