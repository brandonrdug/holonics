# The source capacity bounds the admitted clock, not the observed batch

**Date.** October 6. **Issues.** #73, #76, #62. **Lane.** A/D after the identity-scoped
encoded-source boundary, #383. **Grade.** [definition; agent-inferred] for the clock
bound. The sealed host/card implementation passes its targeted native controls below.
The new Lean leaf is not yet formal-checked; no whole-library, adaptive or scientific
acceptance is claimed.

The computational object is the helical pair interaction. This join touches the
**helix** (digits, phase and winding) and **faces and placement** (the source-state
cardinality read), with the pair, cell holonomy, tube and tower thread attached through
the existing field and its closing source rings. The repeatable failures are an
uncertified consumer, a located cause left unrepaired in the next consumer, a local
count read as product progress, and a refusal answered by a larger resource limit.

## The recovered owner and missing term

`HNN/Moment.SelectiveDecl` proves a Boolean fit plus carry moves a ring by at most
two ticks. `SourceDecl` owns the persisting lift, phase histogram, offset histogram
and held-cell carrier, their exact totals and the cardinality/log-concavity proof.
Rust `hnn/moment.rs::{capacity, Capacity, state_count}` uses its lift factor
`2n + d_g`. `Field::declare` and the ingest/state receipts consume that certificate.
The atlas row is `hnn.moment-capacity`; the located-source record already states
that located ticks are at the period's width.

The concrete missing term is the located digit, `a_g(c)`, in that lift bound.
Admission gives `0 <= a_g(c) < d_g`; the predecessor contributes zero or one carry,
so `0 <= Delta tau_g <= d_g`. A phase below `d_g` plus this step crosses at most one
section, proving the same carry bound inductively along the chain. Ring zero has
no predecessor and a strictly smaller maximum; using `d_g` uniformly is a valid
conservative bound, not an inferred fit of the observed classes.

## The bound and its supported source state

For a fixed opening with no re-key, after **n consumed cells**:

```text
tau_open,g <= tau_g <= tau_open,g + b_g*n
b_g = 2                    Boolean identity clock
b_g = d_g                  every admitted located digit (also bounds the identity)

N_b(n) = |A|^(max Delta) * product_g (b_g*n + d_g)
       * product_(g in sources) [choose(n + d_g*|A| - 1, d_g*|A| - 1)
         * product_(delta in offsets)
           choose(max(n-delta,0) + d_g*|A|^2 - 1, d_g*|A|^2 - 1)]
```

The lift's fixed-opening interval has `b_g*n + 1` points, bounded by the declared
factor since every period is positive. A varying initial phase within one fixed
winding gives the same conservative `b_g*n + d_g` factor. Every consumed cell adds
one first-histogram entry, every offset adds `max(n-delta,0)` pairs, and the held
suffix has length `min(n,max Delta)`. A first-carry stop is a prefix, so unconsumed
cells add no lift, histogram or offset entry. Splitting across ingest calls changes
none of these invariants and does not reopen the source moment.

The count is an **upper bound**, not the observed number of distinct states. The
pigeonhole conclusion additionally requires a total source map on the full declared
`A^n`; it does not establish lossiness on a restricted terrain family. It counts the
named source carrier, not an adaptive constitution, a full resident, or scientific
improvement. Learned coefficients and other persistent operands need their own count.

In particular, Rust `SourceMoment::open_with` may retain `Leaky` maps and their
parameters; later `normalized_counts` reads them. The histogram theorem does not
count these additional registers. A whole-moment capacity consumer must either add
their bounded-state factor or refuse that reading. This is a source-scope obligation,
not a numerical disproof of the overall product count.

The proposed runtime certificate keeps both the identity and full-period profiles.
Its lift-factor arithmetic widens to `BigUint` **before** multiplying word-sized
rates and counts. Exact `states(n)` admits `u64` counts; comparison with `|A|^n`
refuses an exponent beyond its existing `u32` power wire. Ring periods are at least
two, offsets positive, and source indices must belong to the declared ring partition.
The device's existing narrower admission is unchanged: `d_g < 2^31`, a `u32` batch
wire, counts below `2^63` and unbounded host windings. No carrier or budget is raised.

A continuing moment's profile must not be selected from the latest batch. #383's
persistent `located` flag supplies the needed promotion: once located cells were
counted, a later identity or empty passage cannot restore the identity certificate.
The flag's save/restore provenance must be enforced; an old unmarked located state
cannot be silently interpreted as identity.

## Implementation and acceptance status

### The shared clock and the source's own clock

The `128235e8` consumer check treated the moment's own accumulated ticks as the
entire shared Current's advance from its opening. That equality fails after a
phase rekey or when another open source advances Current. A per-aeon replacement
opening alone would also omit the independent adaptive anchor from the count.

The consuming repair preserves the original opening, source bins, own tick count,
source-age endpoint and held suffix. A mandatory saved
`source-clock M plain|reframed` counts all actually consumed occurrences on the
shared Current since this moment opened. Its own injections are `n <= M`.
Sibling ingestion adds the actual consumed prefix; a phase rekey adds no cells
and no elapsed source time. `Reference::ingest` synchronizes siblings and
`Reference::locate_keys` synchronizes every ingest source. The device consumes
the same host interface beside its card's coordinate rekey.

The physical aging operand is separate from that capacity population: each
sibling synchronization consumes the actual per-ring tick vector
`Delta t_g = Current_after[g] - Current_found[g]` of the accepted prefix. Its
Leaky first and offset coordinates pay the existing carried nearest-lattice
decay once per actual external ring tick. This uses `hnn.leaky-count` and
`LeakyCapacity.tick_nonexpansive`; it injects no datum, changes no bins or own
tick count, and needs no pending history or new save field. A phase-only rekey
supplies zero external ticks. The checked interface requires the full vector
and its native `0 <= Delta t_g <= d_g * external_cells` footprint before any
coordinate or metadata changes; the host and card consumers derive it from
the actual reached lift, never the requested suffix.

Freezing the source endpoint is sufficient only for the zero-time rekey. The
first synchronization draft omitted physical aging caused by another source:
at `rho = 1/2`, an old unit, one sibling source-ring tick, and a fresh owning
unit without a source-ring tick read `1/2,1/2` rather than the ring-clock
weights `1/3,2/3`. The fixed consumer pays that external tick before the fresh
unit arrives. A targeted fixture also checks the old and new offset-pair
weights and exact save/read equality. The population chart reads these
ratios at its declared dyadic grain; the fixture compares those exact chart
representatives, not floating approximations. Non-Leaky dissipative ages
retain their existing alias/refusal rule. These new runtime checks pass on the
sealed host source and the card's supported, unit-modulus route.

Since every admitted native occurrence advances at most one period and a rekey
preserves winding, each current lift lies in a winding window of
`d_g(M+1)` values. Its source's endpoint phase and own tick count become
independent coordinates, with `d_g(b_g n+1)` values. At fixed opening, producing
partition, true reframed profile and declared `(n,M)`, the source-state bound is

`H(n) * product_all_g[d_g(M+1)] * product_source_g[d_g(b_g n+1)]`,

where `H(n)` is the original histogram and held-suffix factor without its lift
factor. The existing Leaky coordinate factor multiplies this using actual `n`
injections. This does not count adaptive constitution/key state or assert a
compression crossover for an interleaved/rekeyed input. `SourceCapacity::Reframed`
therefore returns an upper bit bound and shared-clock population, with no `n*`.

`HNN/ReframedMoment.lean` drafts the corresponding joint finite box, single-rekey
membership, one-period winding step and coordinate extension. These new formal terms
are **unverified** pending their focused queue check. The native synchronization/save
regressions pass as described below. The previous compiled no-rekey and Leaky leaves remain
evidence for their original scope. The incomplete lib suite at its 219-second
deadline supplies no test-specific slowdown measurement; the unfinished pumped
test needs its own development read before any projection.

The initial draft used base `c0275dd0647d265c73525d12584bb224c6e90b25`;
the ranged and Leaky source-capacity baseline was subsequently committed at
`128235e82943276a1eaa1ca9a7bc21fab0826f8e`.
`lean/Holonics/HNN/RangedMoment.lean` owns the digit/carry bound, source bookkeeping
with an explicit lift update on the existing state carrier, unchanged offset totals,
prefix bound, parameterized state count, pigeonhole theorem and persistent crossover.
Substituting `b_g = 2` recovers the original definitions; substituting `b_g = d_g`
is the located join. It imports the old owner and is imported by `HNN.lean`.

That baseline contains the Rust capacity/accessor and native fixtures in their actual
owners. `SourceCapacity::checked_of` checks the producing source/clock partition and
the full lift using the **consumed** cell count. `Field` caches the derived located
capacity; explicitly identity-only controls retain their narrower certificate.
The committed [baseline receipts](receipts/2026-10-06_ranged-leaky-capacity/README.md)
record successful workspace checking, eight ranged tests, eight source-entrance/cold
restore tests before the final atomicity preflight, and the completed Lean checks.
They also preserve the earlier failed checks, the Leaky deadline raise and the
incomplete full-library test. These receipts establish their original source scope;
they do not validate the new shared-clock synchronization, external-tick aging,
mandatory clock metadata or `ReframedMoment` leaf described above.

The bounded scalar controls pass: periods `[2,3,5]`, source ring 2, five classes,
offsets `{1,3}` give identity crossover `436 = 2^2*109` and ranged crossover
`438 = 2*3*73`. A full-period carry takes lift `[1,2,4]` to `[2,5,9]`, moving the
last ring five ticks where the old box allowed two. At `n = d = 2^64-1` the widened
lift factor is `2^64*(2^64-1)`. The baseline's eight native ranged fixtures cover
these exact arithmetic controls. They establish no learning or scientific claim;
the new reframe and sibling-aging fixtures still need current-source acceptance.

The baseline native acceptance covers independent crossover comparisons,
exact wide arithmetic, malformed declaration/lift refusals, the existing located
source fixture entering through emitted cells, high winding, first-carry prefixes,
offset masses and continued identity/empty input. Its development seed is
`2026100962`; it reads no held-out scientific dataset. Current reframe, rekey,
sibling-ring aging, malformed synchronization and save/restore acceptance require
their separately sealed current source/cache inputs and fixed measured projections.
No training or scientific synthetic generation is authorized by these unit gates.
The formal leaf remains pending the existing validation queue.

### Current native source acceptance and its limits

The source-clock receipt bundle is
`receipts/source-clock-join-20261006/native-validation-v1/VALIDATION.json`, with the
original diagnostics, exact source/compiler/executable pins, projections, aggregate
CPU, group memory peaks and verified final cleanup/release beside it. On host seal
version 4 and CUDA patch version 5, the queue executed and passed `26 = 2*13`
selected controls: twelve ranged/retained/reframed capacity fixtures, four actual
source-entry fixtures, four cold-restore fixtures and six exact GPU parity/integration
fixtures. These cover the external-tick aging fixture, save/read continuation,
zero-time key reframe, sibling clock population, refusal atomicity and actual card
consumption. The device still refuses Leaky transport below unit modulus; no new
dissipative device kernel is inferred from host acceptance.

The first combined link failed only in new CUDA fixture assertions which tried to
clone `HnnError`. Its preserved wall/projected ratio is `20196230265/65000000000`,
aggregate CPU `57885056000` nanoseconds and group peak `3419713536` bytes. The
owned fixture repair borrows the error; it adds no public Clone law and changes no
runtime source law or resource limit. The accepted cached link's wall/projected
ratio is `2188906986/65000000000`, aggregate CPU `3747139000` nanoseconds and
group peak `843120640` bytes. Every stage published quiescence and released its
source-read lease. No full-library/full-GPU suite or scientific run is claimed.

After that release, the tested physical chart/observation consumer at `280fa010`
was joined to this integration tree with its immutable source and receipt bytes.
Its source moment uses the supported continued station carrier and does not borrow
this ingest-only capacity bound. The two lanes' separate passes do not establish
joined-source acceptance: the exact combined source is submitted to the same queue
for focused linkage and affected physical/carry/Leaky controls. The source comments
and record status above now distinguish those completed unit gates from the pending
formal leaf and combined integration.
