# The deed is not a test; the founded return is standing

**Date:** 2026-08-07
**Truth status:** `established-bounded`
**Evidence:** direct source inspection, `CTestCostData.txt` from a complete run, build-graph
measurement
**Provenance:** Brandon, direct instruction, three times across two days — the third stating the
correction plainly: *"you keep getting hung up on optimizing these tests when preserving them at all
is likely the real issue… whatever use-case they have is likely more efficiently achieved
computationally, but you are keeping them primitive in these 'tests'… I do not know what you are
misunderstanding about my frustration, and why you are acting like I'm asking for a 'speed-up', this
is just straight up wasted time and compute."*

---

## The three things wearing one name

`ctest` held 126 entries. They were not one kind of thing.

| | serial cost | what it is |
|---|---|---|
| **Foundings** | ~2,180 s | the machine running, and replays and seals of the machine running |
| **Guards** | ~73 s | source-tree audits, invariant falsifiers, compile contracts, host contracts |

Ninety entries were candidates to move. Twenty-seven of them turned out to deposit nothing at all —
they take material and return only an exit status — and were re-registered as tests by the same
rule that moved the others. **The taxonomy is drawn by what an entry does, not by what it was
called.** ctest ends with 63 entries; the graph ends with 249 founded returns.

A **deed** mounts a rest, contacts cards, computes on the card, and rests its return as a file. That
is production. A **guard** takes material and returns only a verdict. That is a test. The
distinction is not stylistic: a founding *deposits*, and a thing that deposits belongs to a
dependency graph, because the question of whether it needs to run is answered by whether its inputs
moved.

## The measurement

From `CTestCostData.txt` over a complete run, sorted:

```
r35.trace_rebase_discovery_device_deed   527.6 s     the deed
r35.source_access_audit                  301.4 s     the same deed, under a probe
r35.determinism                          263.5 s     the same deed, byte-compared
r33.determinism                           61.1 s
r33.source_access_audit                   60.8 s
r33.characteristic_discovery_device_deed  29.6 s     ← the original costs half of one replay
```

Across the whole suite, **about 1,320 of roughly 2,250 serial seconds were byte-for-byte
re-executions of a computation that had finished seconds earlier in the same invocation.** The
trace-rebase chain alone is 77% of the suite and over half of that is repetition.

`add_test` fires unconditionally. Nothing keyed a re-run to a change. ninja knows what moved; ctest
was never asked.

## The conviction, by the project's own tests

The three contamination tests are Brandon's (2026-08-06) and they convict the apparatus.

*It consumes current without transforming the shape of passing information.* `r34.determinism`
re-executes a 300-second deed to produce bytes it then proves identical to bytes already on disk. Its
output carries, by construction, zero information not already present. That is `while True: pass`
with a card attached.

*It is frozen against relation.* Every founding re-derived on every invocation means the chain is a
re-derivation chain, not a standing. Nothing accumulates; nothing is pivoted off.

*It simulates the mechanism it names.* Determinism is a property of *(executable, inputs)*. Once
established it cannot become false unless one of those moves. On every subsequent run where neither
moved, the entry has the form of a verification and the content of a tautology — which is §8's own
rule: **a receipt that could not have come out otherwise carries no evidence.**

## What the lineage already was

The deed chain was always a file-dependency graph. It is written out longhand in every argument
list:

```
r34's arguments: … "${R33_FINAL_REST}" "${R34_INTERMEDIATE_REST}" "${R34_POSITIVE}" …
                    ^ mounted                ^ founded              ^ contacted
```

Nothing ever told the build graph. The correction reads the lineage off the argument list with no
second declaration that could drift: **an artifact path is a return of the first founding that names
it and a mount for every founding after.** `cmake/HolonicStanding.cmake` does exactly this, and the
resulting graph for one rest is:

```
artifacts/R34_TRACE_FIBER_LIFTING.rest
  ← r34_trace_fiber_discovery_device_deed
  ← artifacts/R33_CHARACTERISTIC_TRANSPORT_HANDOFF.rest
  ← apparatus/cards/R34_{POSITIVE,SIGNED,RECHARTED}_TRIPLES.card
  ← formal/elementary-holonics/{lean-toolchain,lake-manifest.json}
```

**249 founded returns are now in the build graph and 62 guards remain in ctest.**

Measured 2026-08-07 on a settled tree, with ctest's own exit status read rather than a pipeline's:

```
ninja holonics_standing     0.031 s      nothing moved, so nothing ran
ctest                       58.39 s      100% tests passed, 0 tests failed out of 62
```

The routine gate is **under a minute**. It was twenty-four, and the difference is not throughput —
nothing was made faster. Work that had already been done simply stopped being done again.

## What licenses the caching

This is the part worth keeping. The replay steps established that each deed is a pure function of
its declared inputs; the source-access audits established that it opens nothing outside them. Those
two facts are precisely **the certificate that the declared input closure is a complete cache key.**

So the replays were never waste in themselves — they were the thing that made caching sound. They
were waste only because their result was thrown away and re-established from zero on every
invocation instead of being spent once to license a standing.

That is the same sentence as the ontology: **the rest is standing, re-derivation is current.**
Spending current to reproduce standing that already exists is the definition of waste here.

## What the unread gate was hiding

The first founding pass in dependency order surfaced a real regression that had shipped two commits
earlier under a gate reported as `126/126` from `ctest … | tail`, whose exit status is `tail`'s.

The commit corrected `returned_difference_applied` to read `accepted && commit landed`. In the
rederivation handler the foil is a return that is *supposed* to be refused, so its correct reading
is `!rejected && commit landed`. But the passage's stage advance was gated on the same field:

```cpp
stage_ = rejected && morphology.returned_difference_applied ? foil_returned : none;
```

After the correction that is `rejected && !rejected` — **unsatisfiable**. The foil could never
advance the passage, the valid formal passage was never formed, and the deed returned
`valid_process_refused` with **7,194 verification failures**.

**And it accounts for every failure that was being chased.** The trace-fiber deed's
`verification_failures=4` and its four chained dependents were not an independent fault: the
rederivation deed sits upstream, so its empty passage propagated a corrupt handoff down the entire
chain. With the gate corrected and the chain re-founded in order, r30 through r34 all return
`verification_failures=0`.

Two method lessons, both earned here: a gate is not a gate until its pass line has been read, and
**a failure in a chained deed is a claim about its whole upstream, not about itself.**

## The contention that wore a regression's mask

The first founding pass ran under ninja's default of one job per core: two dozen deeds launched at
one card. The plural-rederivation deed returned `executor_state=10`, `kernel_launches=0`, and
**7,194 verification failures** — a deed that never reached the device at all, reported as a
mathematical failure.

This is the same defect that had nineteen entries carrying a two-times timeout margin against a
measured cost. Foundings now run in a `holonic_card` job pool of depth one. **A false failure from
contention is more expensive than the parallelism it buys, and these deeds are device-bound anyway.**

## Four things the graph refused to let stand

Putting the foundings in a dependency graph made the apparatus state its own assumptions, and three
of them were wrong. Each had been invisible while every founding ran unconditionally, because a
graph that runs everything can never be caught believing something false about what depends on what.

**A consumer declared above its producer.** The lineage is read off declaration order, and the
cultivated-organs module declared its seal above the determinism replay whose receipt the seal
reads. ninja duly sealed before replaying. This is now a configure-time refusal — *a founding may
not deposit where an earlier founding already read* — rather than a silent inversion.

**A negative control declared as a product.** The rederivation deed and the conditioned production
deed each name a path for the *foil's* compiled object. The foil is a proof the kernel is supposed
to refuse, so **no object is ever produced there, and its absence is the evidence.** Declared as an
output, that absence read as work left undone: ninja re-ran the founding and everything downstream
of it on every single invocation, chasing a file whose non-existence was the point. The foil's
object is now withheld from the returns, with the reason recorded at the call site.

**A dependency on when a deed was linked rather than on what it is.** Editing a comment in a header
a deed includes recompiles, relinks, strips, and yields a **byte-identical** binary — and dirtied
the whole downstream chain. `cmake/HolonicFingerprint.cmake` writes the deed's content hash and
rewrites it only when the hash moved; the founding edges carry `restat = 1`, so an unchanged stamp
keeps its timestamp and nothing downstream is disturbed.

**An undeclared write onto the standing itself.** The source-access audit re-executes both deeds
under an `LD_PRELOAD` probe to observe what they open — and it handed them **the deeds' own output
paths.** So every audit overwrote the rest, the generated Lean, the compiled object, the dossier and
the atlases of the deed it was auditing. In a graph that is fatal: every founding downstream of an
audit ends each pass with an input newer than its output, so the entire chain is dirty again the
moment the audit finishes. Measured before this was found: **three consecutive twenty-two-minute
passes, re-founding thirty-odd deeds each, converging on nothing.** The audits now redirect
everything the deeds write into a scratch region, basenames preserved so their open-path checks read
the same names.

There is a second consequence worth stating on its own. Until this was fixed, the sealed artifacts a
run left behind were **not the deed's output** — they were the probe-instrumented replay's output,
written afterwards over the top. Determinism guarantees the bytes are identical, so nothing in the
mathematics is affected; but nobody had noticed, and nothing in the apparatus could have said so.

The pattern in all four is one thing: **the graph makes the apparatus say out loud what it depends
on and what it produces, and saying it out loud is what exposes the error.** That is the same reason
a receipt must state its reach.

## The finding underneath, which is not about tests

The machine has no process. **It has forty of them.**

Forty separate `main()` functions in `apparatus/host/`, 7,654 lines, 158 `argv` references. The
lineage between them is not held by the body — it is a chain of `.rest` files handed between
operating-system processes, wired by hand in CMake at configure time. `body/returned_standing.hpp`
exists, and it is reached by exactly one deed, the one written to demonstrate it.

So the build now understands that the deed chain is a graph, and the body still does not. Deed *N+1*
can see only deed *N*'s rest, and only because a human chose that path in a CMake file. Nothing
mounts a population of prior returns and selects among them; nothing composes from what it reached;
excluding a return cannot stop a later deed by structure because the later deed never reached it —
it read a file path it was handed.

**That is the same defect at a higher altitude than the one this record closes**, and it is exactly
what the one-standing and current-onto-the-mathematics movements are for. The caching fix is not a
detour from them; it removes the twenty-four-minute tax that made iterating on them impractical, and
it makes the shape of the missing organ legible: the body should reach its own standing the way
ninja now reaches the artifact graph.

## What is not claimed

That the standing is durable across a discarded build tree. The founded rests total **111 KB across
23 files**, and with the generated Lean sources **377 KB** — the other 40 MB is `.olean` and
diagnostic atlases. That 377 KB is the machine's entire founded mathematical production and it
currently lives in a gitignored directory. Depositing it as committed standing is the next step and
is not done here.
