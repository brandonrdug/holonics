# The cost is carried by the rule, and the gauge cannot afford itself

**Date:** 2026-08-08
**Truth status:** `established-bounded` for the measurement and for the falsification of the declared
cost law. `open` for the obligation in §5, which has a named remedy and no implementation.
**Evidence:** `computational-witness`. Measured by this session with a purpose-built probe against
`smith_normal_form` directly, release build, one machine, one sitting — not taken from a report.
Independently hit by two sub-agents on different material before this session measured it.
**Provenance.** Surfaced by the sub-agent investigating the grown circuit's lineage torsion, which
could not read width 3 in-tree and said so rather than quietly reporting width 2. Independently hit
by the sub-agent building the matroid Chow ring, on an `11×11` matrix. **Both reports are search
returns, not authority**; the figures below are this session's own.
**Band:** 2026-08-08 · A DECLARED COST LAW FALSIFIED BY ITS OWN MATERIAL / 390,000× SPREAD AT FIXED
DIMENSION BETWEEN RULES THE UNIQUENESS THEOREM FORCES TO AGREE / THE PIVOT COUNT IS NOT WHERE THE
BLOWUP LIVES / 29 DRIVER SITES MOVED / THE GAUGE STILL CANNOT AFFORD ITSELF

---

## 1. The declared law, and the measurement that falsifies it

`crates/holonic-engine/examples/grown_circuit_schedules.rs` declared:

> *"A cost law, measured and declared: the Smith reduction is cubic in the cell count and its
> intermediate entries grow, so a reading is taken where it is affordable."*

Measured today on the grade-two boundary map of a grown Brent–Kung adder at width 3, `[143 × 101]`,
release build, through the public `smith_normal_form`:

```text
  SmallestMagnitude      1 ms   rank 101   factors > 1  [2, 2, 2, 2]
  LargestMagnitude       8 ms   rank 101   factors > 1  [2, 2, 2, 2]
  FirstNonzero           did not complete in 390 s
```

**A spread of at least 390,000× at fixed dimension**, between three rules that the uniqueness of the
Smith normal form over a PID forces to return the same factors — and which returned the same factors
wherever two of them completed.

So *"cubic in the cell count"* is not a bound. It omits the variable that dominates. A cost law that
does not name the pivot rule is not a cost law, and this one was carried in a banner the example
prints on every run.

The mechanism is classical: intermediate expression swell in the Euclidean descent. The structure of
the reducer is not wrong for the *answer* — an independent Python implementation with the same
smallest-magnitude discipline does the same matrix in 0.04 s — and `SmallestMagnitude` is the
standard mitigation.

## 2. The pivot count is not where the blowup lives, and this matters

The obvious exact work measure is already returned: `PivotSchedule.selections`. It does **not**
explain the wall.

```text
  brent-kung w2  ∂₂ [78×52]   extent 52     brent-kung w3  ∂₂ [143×101]  extent 101
    SmallestMagnitude   52  (1.0×)            SmallestMagnitude  101  (1.0×)    1 ms
    LargestMagnitude    80  (1.5×)            LargestMagnitude   153  (1.5×)    9 ms
    FirstNonzero        78  (1.5×)            FirstNonzero        —           >390 s
```

`SmallestMagnitude` takes exactly `extent` selections — **no divisibility repair at all** — against
`1.5 × extent` for the other two. But that ratio is the same at both widths and for two rules three
orders of magnitude apart in cost. The dominating quantity is the **bit-length of the intermediate
entries**, and nothing in this tree counts it.

**That is the honest state of this cost law: the figures above are a clock reading.** Per `CLAUDE.md`
§8 they carry their frame and may measure; they may not select. The exact work vector that *would*
select — the one `cuda_aperture` was corrected to demand — does not exist for this reducer yet.

## 3. Where it came from in the source

`rebase_invariants::reduce` clones its matrix at entry. The divisibility repair does not continue in
place: it folds one row into the pivot row, then calls `reduce_from` and **returns**, restarting a
full reduction on a fresh copy of the trailing block — on coefficients that have already grown. Each
repair is a restart, and `FirstNonzero` picks pivots that maximise how often that happens.

## 4. What changed

- **The measurement is now on the owner.** `smith_normal_form`'s doc carries the three figures, the
  date, the mechanism, the recommendation, and — explicitly — the statement that the pivot count does
  *not* explain it and that the falsifier this law still lacks is entry-magnitude instrumentation.
- **The false declaration is corrected in place** rather than deleted, and the example now prints
  what it used to claim and why that was wrong.
- **Twenty-nine single-rule driver sites moved from `FirstNonzero` to `SmallestMagnitude`.** Every
  library occurrence but one lives inside a `#[cfg(test)]` module on small fixtures where all three
  rules are 0 ms; those were deliberately left, because a hundred-site sweep of test code is a change
  that should be made on purpose and not incidentally to a cost finding. The returned invariants do
  not move — that is what `invariants_agree` checks and the workspace is green at **1440 passed, 0
  failed**.

## 5. What did NOT change, and it is the finding with the longest tail

**`PivotRule::ALL` still contains `FirstNonzero`, and it is first in the list.**

That is deliberate and it is also the obligation. The gauge exists to show that the invariants do not
depend on the rule, and dropping the pathological rule would weaken exactly the thing it proves.
`CLAUDE.md` §8 convicts this same constant for the opposite defect — on the five plate fixtures all
three rules produced **identical traces**, a gauge whose group acted trivially. On grown material the
group acts non-trivially. It acts non-trivially on **cost**.

So the Brent–Kung width-3 reading remains unaffordable *through the gauge* while its invariants sit
one millisecond away *through a single rule*. `H₁ = Z¹⁵ ⊕ (Z/2)⁴` at that width was obtained
off-tree and confirmed here by direct reduction; the in-tree reading list still stops at width 2, and
now says why.

**This is §8's independent-implementation bullet pointing at a gauge**, and the remedy is §8's own
words with one addition:

> A gauge must exhibit its distinguishing word, **and state the cost of each of its schedules.**
> `invariants_agree` compares returns and never costs. A schedule that cannot be afforded on the
> declared material has not been run, and a gauge that reports agreement between two rules it could
> afford and one it could not has reported an agreement it did not obtain.

Two routes, and they are not exclusive:

1. **Instrument the entry magnitude** — total bit-length of intermediate entries, per rule, exact and
   machine-independent. That turns the clock reading in §1 into a work vector, and only then can a
   caller *lawfully* select a rule rather than a wall-clock sample selecting for them.
2. **Repair the reducer** — continue the divisibility repair in place instead of restarting, and take
   the standard remedy for expression swell (modular / Kannan–Bachem entry reduction). Bounded work
   against a classical algorithm, and it would make the gauge affordable rather than merely cheaper.

## 6. Two agents found this independently, on different material

The torsion investigation hit it on a `143×101` grown boundary map. The matroid Chow construction hit
it on an `11×11` Lefschetz matrix under a supermodular class — `SmallestMagnitude` in 396 µs,
`FirstNonzero` not returning in eight minutes — and recorded it in `integral_smith_factors`'s doc
before this session had seen either report.

**Neither was looking for it.** Both were consuming `rebase_invariants` for something else and were
stopped by it. That is worth recording as evidence about the defect's reach: it is not a property of
grown circuits or of matroids, it is a property of the reducer, and it will stop the next consumer
too.
