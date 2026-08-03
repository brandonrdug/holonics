# THE CONIC OWNS THE FRAME; THE CARD WAITS FOR THE HOST

**Status:** DIRECT PERFORMANCE AUDIT / HEADLESS RTX 4080 SUPER MEASUREMENT /
EXACT ARITHMETIC RETAINED / MULTICORE RECEIPT DEFECT CORRECTED / NO WINDOW
OPENED / NO SOMA CHANGE

## Present question

The changed local-star geometry is visibly informative but interaction is
extremely slow. Determine the computational cost of one actual presented
successor, distinguish causal evolution from presentation, and identify the
physical and asymptotic source of latency without replacing exact ratios by
floating point or opening the desktop window.

The standing trace was insufficient: it flushed only every sixty records and
was therefore empty after a short or failed run. Its one `wall_nanoseconds`
field also began after coefficient packing and combined device allocation,
kernel conduct, download, decode, arbitrary-precision host support, and merge.

## Physical cut

- CPU: AMD Ryzen 9 7900X, 12 physical cores / 24 hardware threads
- GPU: NVIDIA GeForce RTX 4080 SUPER, compute capability 8.9, 16,376 MiB
- executor limit: 12 host workers
- initial aperture: `640 x 400`
- changed aperture: `640 x 720`
- presentation: 22 primitives, consisting of the same eight local-star
  triangular faces and three native conics received by each of two receivers
- current hybrid carrier: 8 primitives on signed-i128 CUDA; 14 on exact host
  rationals, comprising 6 conics and 8 linear primitives

The measurement command was:

```text
cargo test -p holonic-engine --example desktop_receiver \
  cuda_aperture_preserves_receiver_input_beyond_i128 \
  -- --ignored --nocapture
```

The independent species command was:

```text
cargo test -p holonic-engine --example desktop_receiver \
  exact_host_species_cost_profile \
  -- --ignored --nocapture
```

Both are headless. Neither constructs or controls an X11 window.

## Complete changed-event cost

All values are integer nanoseconds from the same exact changed successor.

| stage | nanoseconds |
|---|---:|
| return input into the addressed receiver | 3,537 |
| local-star physics event | 270,427 |
| synchronize caused construction vertices | 6,612 |
| receive both complete faces / construct assembly | 271,285,859 |
| transport primitives and form pair relations | 89,452,050 |
| exact hybrid aperture trace, total | 7,384,960,388 |
| turn returned addresses into receiver layers | 62,830,342 |
| superimpose layers into the outer display carrier | 3,536,676 |

The measured pre-X11 input-to-display path is therefore `7,812,345,891 ns`.
The physical change itself is not the latency source. Exact presentation
dominates.

The initial CUDA admission costs `7,091,512,559 ns` because it conducts the
hybrid candidate and then independently conducts the complete exact-host
authority once before admitting the executor. This is a one-time parity cost,
not steady-state physics.

## Hybrid trace decomposition

| frame | aperture | pack | device prepare | kernel + sync | download | device decode | exact host trace | host merge | total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| initial | 640x400 | 4,548,672 | 119,374 | 250,770 | 2,623,756 | 3,151,554 | 3,388,868,632 | 1,224,835 | 3,408,084,784 |
| changed | 640x720 | 6,604,574 | 247,774 | 361,126 | 3,960,460 | 4,959,071 | 7,361,510,945 | 1,447,482 | 7,384,960,388 |

For the changed frame, host exact tracing occupies more than
`9,968 / 10,000` of the measured hybrid trace. The CUDA kernel interval is
only one part in more than `20,000` of the total. GPU arithmetic is not the
present bottleneck.

The card evaluates 129,216 exact support queries. The host evaluates 57,430.
The count alone is misleading: one host query operates on arbitrary-precision
rational conic ranges, while the admitted card query uses bounded signed-i128
integer conduct.

The device output carrier is also over-broad:

```text
bytes = 4 * aperture_width * aperture_height * selected_primitive_count
```

It is `40,550,400` bytes at 640x720. This reserves and downloads rows for all
22 selected primitives although only 8 are conducted on the card. This waste
is real, but its measured milliseconds are secondary to the host seconds.

## Aperture scaling

The same changed geometry gives:

| aperture | exact-host support queries | exact-host nanoseconds | device output bytes |
|---|---:|---:|---:|
| 160x180 | 15,160 | 1,732,457,106 | 2,534,400 |
| 320x360 | 29,508 | 3,432,793,394 | 10,137,600 |
| 640x720 | 57,430 | 7,361,510,945 | 40,550,400 |

For this bounded world, doubling each matrix dimension approximately doubles
the visited support tree and host time, while it quadruples the dense device
carrier. The present support search is therefore behaving like a traced
one-dimensional boundary in a two-dimensional aperture, approximately
`O(width + height)` at fixed geometry, rather than a complete
`O(width * height)` cell classification. This is a measured law of this
construction, not a universal worst-case claim: broad ambiguous ranges can
still visit a two-dimensional fraction of the subdivision tree.

## Species cost

At 640x720 on the changed successor:

| species | primitives | workers | support queries | wall nanoseconds |
|---|---:|---:|---:|---:|
| conics | 6 | 6 | 34,034 | 6,579,104,646 |
| all linear | 16 | 12 | 49,988 | 2,386,264,238 |

The six conics form the critical path. One conic is currently one CPU task, so
the dominant work admits at most six-way concurrency regardless of the
12-worker limit.

The exact conic predicate explains the cost. At every visited subdivision it:

1. clones four rational grid boundaries into an `ExactCell`;
2. recomputes the quadratic's edge-stationary denominators and interior
   determinant;
3. forms every admitted stationary candidate;
4. evaluates the six-term rational quadratic at four to nine candidates; and
5. normalizes the resulting arbitrary-precision rational products before
   deciding whether zero lies in the range.

If `Q` regions are visited and the active integers carry `b` bits, this is not
constant-cost `O(Q)`. Its operative form is `O(Q * M(b))` multiplied by
several rational normalizations, where `M(b)` is the cost of exact
multi-precision arithmetic at the current bit extent. The changed frame
reaches a 257-bit required intermediate; earlier receiver states have reached
more than 493 bits.

## Multicore correction

The executor formerly set:

```text
workers_used = min(worker_limit, task_count)
chunk_size = ceil(task_count / workers_used)
```

and then spawned one worker per chunk. Fourteen tasks with a twelve-worker
limit therefore spawned only seven threads while reporting twelve. The
partition is now the exact quotient/remainder division into twelve nonempty
contiguous batches, and a regression observes the twelve physical thread
identities. Canonical result order remains unchanged.

This correction makes the receipt honest and exposes all admissible primitive
parallelism. It does not solve conic granularity: six dominant primitive tasks
still use only six cores, and the measured conic wall time remains about 6.6
seconds.

## Event-loop consequence

The application currently performs:

```text
one boundary or continuation
-> complete face assembly
-> complete exact aperture trace
-> complete layer and display composition
-> present
-> poll the next input
```

Every continuation therefore inserts a multi-second presentation barrier into
the causal loop. The observed choppiness is not continuous physics consuming
the machine; it is synchronous observation blocking later input and later
events.

CUDA and host work are also serialized:

```text
launch card -> synchronize -> download -> decode -> run host fallback -> merge
```

Their primitive populations are independent at this cut and could be
conducted concurrently. Overlap alone cannot remove the 6.6-second conic
critical path, but the present serialization is unnecessarily additive.

## Engineering conclusion

The geometry need not be simplified and exact ratios need not be abandoned.
The current performance obligation is sharply mechanical:

1. make the exact conic support carrier integer/projective once per conic and
   aperture, clearing common denominators before subdivision;
2. hoist conic invariants and stationary witnesses out of the region loop;
3. divide one conic's support frontier into independent deterministic
   subregions so the six conics are not the maximum concurrency;
4. compact and persist the CUDA output carrier for only device-admitted
   primitives;
5. overlap independent host and card conduct;
6. decouple causal continuation from complete observer presentation while
   retaining event-identified returned faces.

The first two change representation and repeated work, not mathematical law.
Their acceptance condition is exact address and multiplicity identity against
the current arbitrary-rational authority across the initial, changed,
resized, horizon-crossing, and wide-intermediate witnesses.

## Instrument retained

`CudaApertureReceipt` now records selected/device/host populations, host conic
and linear populations, device output bytes, device and host query counts, and
separate integer timings for pack, device preparation, kernel, download,
decode, host trace, host merge, and complete wall time.

The desktop TSV carries the same stage fields and flushes every event. A short
run or crash can no longer leave a zero-byte trace.

## Construction return

The measured defect was removed without changing the support law.

### Exact terminal carriers

Every conic is now substituted into the terminal chart once. Its six rational
coefficients are cleared to one primitive integer quadratic, common content is
removed, and edge/interior stationary witnesses are retained in exact
projective ratios. Every visited aperture region thereafter asks only integer
sign and order questions.

Every linear primitive is likewise carried by homogeneous integer terminal
endpoints. Region intersection uses exact determinant and projective-between
tests. The former rational conic and segment implementation remains as an
independent authority.

At `640 x 720` on the changed successor:

| exact host species | wall nanoseconds before | wall nanoseconds after |
|---|---:|---:|
| six conics | 6,579,104,646 | 15,684,113 |
| sixteen linear primitives | 2,386,264,238 | 17,185,476 |
| complete 22-primitive support | not separately retained | 24,310,514 |

The complete optimized host carrier is exactly equal to the retained rational
authority in addresses, support multiplicities, and primitive counts.

The proposed subdivision of each individual conic frontier did not enter the
source. Integerization changed the critical path first: six already-independent
conic tasks now finish in about fifteen milliseconds together. Splitting their
small terminal frontiers would add scheduling and merge structure after the
measured bottleneck had departed.

### Exact relation conduct

Independent line/line, line/conic, and conic/conic relation tasks now execute
through the bounded CPU executor and return in canonical task order. The
executor's quotient/remainder partition reports and physically uses all
declared workers.

Presentation formation now builds the transported arrangement once. The former
pair wrapper rebuilt each primitive's internal edges once per neighbour,
duplicated self-relations, and attributed those duplicates to the wrapper's
receiver pair. Primitive-instance ordinals now retain plural receiver identity.
When the receiver-to-presentation transport is exactly identity, already
formed local relations are retained and only genuinely cross-receiver
relations are added.

### Card/host carrier

The dense CUDA return now contains only the eight device-admitted primitives:

```text
40,550,400 bytes -> 14,745,600 bytes
```

Card launch overlaps the independent exact-host population. On the changed
frame the remaining synchronization wait is about fifteen microseconds. The
forced hybrid carrier measures approximately 31--39 million nanoseconds across
the retained runs, while the complete exact host carrier measures
approximately 24--25 million nanoseconds. CUDA admission therefore measures
both exact carriers and selects the host carrier for this bounded ecology.
CUDA remains admitted and directly measurable; device presence no longer
overrides observed physical cost.

### The crossing atlas cannot block the live face

The exact continuous support face and the complete all-crossings atlas are two
lawful products of one caused geometry. Aperture support consumes the former,
not the latter. New explicit support APIs carry every primitive, coordinate
field, seam, and receiver relation without making a visible return wait for
every pairwise proof witness. The complete face and presentation APIs remain
available when the crossing atlas itself is the research object.

The RGB quotient was also factored correctly. One receiver's exact phase ratio
is now derived once and only the integer support multiplicity is applied per
returned address. This preserves every output channel exactly and reduces
layer construction from about 46 million to about 1.4 million nanoseconds.

## Retained changed-frame measurement

The live support path on the same `640 x 720` successor is:

| stage | nanoseconds |
|---|---:|
| return input | 3,677 |
| local-star physics | 266,278 |
| synchronize changed construction | 7,143 |
| receive complete continuous support faces | 22,524,117 |
| transport complete support into the presentation face | 7,335,923 |
| selected exact aperture carrier | 24,172,179 |
| derive receiver layers | 1,420,899 |
| superimpose the outer display carrier | 3,506,038 |
| **complete pre-X11 return** | **59,236,254** |

Relative to the audited `7,812,345,891 ns` path, this is approximately a
132-fold reduction. Physics remains sub-millisecond. The surviving dominant
cost is exact receiver projection plus support tracing, not a hidden raster
retile, stochastic diffusion, or floating arithmetic.

## Acceptance

- complete changed `640 x 720` CUDA/host support equals the retained
  arbitrary-rational authority;
- the admitted executor selects the faster exact carrier;
- support and full crossing-atlas APIs remain typed apart;
- phase color output is exact while its invariant quotient is formed once;
- no window was opened or controlled during the audit and construction; and
- `cargo test -p holonic-engine --all-targets --no-fail-fast` returns
  `57 passed / 0 failed / 2 ignored` across the library and example targets;
- both ignored headless physical instruments pass explicitly on the RTX 4080
  SUPER, including CUDA/host/rational support parity; and
- `cargo clippy -p holonic-engine --all-targets --no-deps -- -D warnings`
  returns clean.
