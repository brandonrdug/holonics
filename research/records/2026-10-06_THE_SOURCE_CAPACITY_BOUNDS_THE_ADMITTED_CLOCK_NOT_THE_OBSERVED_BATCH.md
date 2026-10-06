# The source capacity bounds the admitted clock, not the observed batch

**Date.** October 6. **Issues.** #73, #76, #62. **Lane.** A/D after the identity-scoped
encoded-source boundary, #383. **Grade.** [definition; agent-inferred] for the clock
bound; implementation drafts and scalar controls below. The new Lean leaf is not yet
formal-checked, and no Rust or device acceptance is claimed.

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

The isolated base is `c0275dd0647d265c73525d12584bb224c6e90b25`.
`lean/Holonics/HNN/RangedMoment.lean` drafts the digit/carry bound, source bookkeeping
with an explicit lift update on the existing state carrier, unchanged offset totals,
prefix bound, parameterized state count, pigeonhole theorem and persistent crossover.
Substituting `b_g = 2` recovers the original definitions; substituting `b_g = d_g`
is the located join. It imports the old owner and is imported by `HNN.lean`.

Rust capacity/accessor and native fixture drafts are private under this worktree's
`.local/ranged-capacity-checks/`, pending Opus's explicitly requested scoped #383 pin
and the consumer reservation. The proposed consumption checks the entire source/clock
partition and the actual full lift against the bound using the **consumed** cell count.
Caching the derived located capacity once in `Field` avoids recomputing a crossover
at every ingest. The existing narrower certificate remains available for explicitly
identity-only controls. Ingest, encoding, repair and cold-carry owners remain fenced.

The bounded scalar controls pass: periods `[2,3,5]`, source ring 2, five classes,
offsets `{1,3}` give identity crossover `436 = 2^2*109` and ranged crossover
`438 = 2*3*73`. A full-period carry takes lift `[1,2,4]` to `[2,5,9]`, moving the
last ring five ticks where the old box allowed two. At `n = d = 2^64-1` the widened
lift factor is `2^64*(2^64-1)`. These are arithmetic controls, not compiled Rust,
Lean, device, learning or scientific validation.

Planned native acceptance fixes these invariants: independent crossover comparisons,
exact wide arithmetic, malformed declaration/lift refusals, the existing located
source fixture entering through emitted cells, high winding, first-carry prefixes,
offset masses and continued identity/empty input. It reuses development seed
`2026100962`; no held-out seed or scientific dataset is read. Rust and Lean checking
need separately sealed source/cache selectors and a fixed measured projection;
no compiler, training, GPU job or synthetic scientific generator has been launched.
