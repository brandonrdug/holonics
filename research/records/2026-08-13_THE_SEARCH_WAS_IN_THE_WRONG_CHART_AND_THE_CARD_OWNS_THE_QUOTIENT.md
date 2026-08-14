# The search was in the wrong chart, and the card owns the quotient

**Date:** 2026-08-13
**Truth status:** `established-bounded [measured]` for every figure; `implemented-exact` for the
sieve and the sweep.
**Evidence:** `measured` on this machine, RTX 4080 SUPER with an active display, against
`/home/b/models/gemma-4-E4B-it/model.safetensors`. Both figures are the driver's own prints.
**Occasion:** Brandon, twice in one evening, on the same run: *"Dropped to 16MB in RAM, 100% on one
core, and no activity on the GPU… I was alerting you of this same exact behavior earlier and it is
still the same set of issues"*, and then *"Why are you not rebasing? This isn't a real limit, it's
like counting with your hands."*

---

## 1 · The measurement, and it is a rebase

`crates/holonic-engine/examples/the_foreign_map_founds_its_axes.rs` returned in **93.1 s**. The
driver's own phase prints put 23 ms of that on everything touching the sixteen-gigabyte map — two
blocks of 6.5M words read, aligned through the declared float mouth, two contractions over
4096 × 2560, `Φ` assembled — and the rest on `exact_spectrum` over an 8 × 8 operator.

Instrumented, the split was:

```text
   characteristic polynomial      78 ms
   rational root census           93,000 ms
```

**The census was not wrong. It was asked in the chart where the magnitudes live.** It bounds its
search by the Cauchy bound `max |coefficient| + 1` and runs Sturm sequences across it. `Φ`'s entries
are 103-bit integers — genuine content, from exact 2560-term contractions of BF16 products — so by
Hadamard the degree-8 characteristic polynomial's constant term reaches `8 × 103` bits, and the
measured `t^0` is **232 digits**. The search interval therefore has half-width `2^770`, while the
eigenvalues themselves cannot exceed `8 · 2^103 = 2^106` by Gershgorin on the operator's own entries.
**664 bits of the search were paid for a magnitude the material never had.**

### The rebase

A rational root of an integer polynomial reduces, modulo any prime not dividing the leading
coefficient, to a root of the reduced polynomial over `Z/p`. **So one prime at which the polynomial
has no root refutes every rational root at once** — exactly, no interval, no isolation, no
approximation. `Z/p` has `p` elements and the question is answered by looking at all of them.

That is `H.0104`'s rebase and nothing else: an invertible change of chart with **zero remainder**,
the free stroke of the compression trichotomy.

```text
   before   93.135 s      0 rational eigenvalues, degree 8 unresolved
   after     0.118 s      0 rational eigenvalues, degree 8 unresolved
```

**785×, and the returned spectrum is identical.** The refuting prime is 31, found in 53 µs.
`crates/holonic-engine/src/lattice_gauge.rs::refuting_prime`, called from `exact_spectrum` before the
census; 1,431 engine tests unchanged.

### The first attempt failed, and why is the content

The sieve's prime ceiling was first derived from the **degree** — `2 × 8 = 16`, six candidates — and
**nothing refuted**. A degree-`d` polynomial over `Z/p` has at most `d` roots, so a single prime
refutes only sometimes; six candidates leave a real chance of no refutation and this material took it.

The ceiling is now derived from **the cost being avoided**: the census bounds its search by the widest
coefficient, so that coefficient's bit-width is exactly what a refutation is worth. Each prime costs
microseconds against a census costing seconds. **The level is read off the material's own number
rather than chosen**, which is the level rule, and the first derivation's failure is why this is
recorded rather than merely fixed.

## 2 · The card owns the quotient, and it did not before

Brandon's standing complaint was not the timing: *"You consistently neglect the GPU, I do not
understand why there is this gate that starts and stays at the CPU for information transport."*

**There is no gate in the body.** The card carries the receiver quotient, morphological conditioning,
conduct grouping, the material shadow, the recurrent law, live lineage events, and exact-integer
support at 384 bits, and conditioning has no host fallback by declaration. The gate was in this
driver, which mounted nothing and never said so — and the operating contract names that exactly: *a
run that pins one host core while the card idles is a defect to diagnose, not a mystery to narrate.*

And the sharper fault was the deed. One head at one layer **is the format**, which Brandon's own
ruling discards. The driver read 6.5M words in 11 ms and then thought for 93 seconds about 64 numbers.

### What now runs

`sweep_on_the_card` reads **every head of every layer** — 336 transports over 48 layers × 8 heads —
takes three faces off the weights, and enacts the quotient through
`receiver_exact_compression::compress_on_device`, the resident `(current class, exact key)` path.

```text
   336 transports read from 42 layers x 8 row blocks   1.076 s   (host I/O, its own place)
   the declared aperture named 6 further layers this map does not carry: [42..47] — reported
   THE FRAMES: block widths {64: 35 layers, 128: 7 layers}; common denominator 327680, exact
   device: NVIDIA GeForce RTX 4080 SUPER
   quotient enacted on the card                          884 us
   one-shot classes 328 -> conduct classes 336, 1 round
   collapsed pairs: 8
```

Eight pairs the one-shot family cannot separate, **all eight separated by conduct after one step
along the residual stream**, including `L29b2 ~ L29b6` — two row blocks of one layer, sitting in
different KV heads — and pairs as far apart as `L0b7 ~ L26b2`.

### Three corrections to this section, made the same day by reading the map instead of the driver

**The figures above are the corrected run.** The first form of this record printed
`336 transports read from 48 layers x 8 heads`, and three things in that line were wrong.

1. **`48 × 8 = 384`, and the number that returned was `336 = 42 × 8`.** The driver declared
   `(0..48)`, layers 42–47 name no tensor and were skipped, and the print reported the *declared*
   count rather than the layers that produced a transport. An authored level in the organ, and a
   receipt carrying a figure nobody multiplied. The driver now prints the layers it read **and names
   the six it was handed and could not use**, rather than dropping them.

2. **"Head" was a label the material does not carry.** This map declares `num_key_value_heads = 2`,
   so `v_proj` is `[2 · 256, 2560]` and an eight-way row split cuts *inside* a KV head — four blocks
   to a head. The pair reported as *"two heads of one layer"* was two row blocks in **different** KV
   heads. They are `block`s now, and the earlier reading is withdrawn. This is the third time in one
   evening that a unit was fetched off the architecture the deed claims to discard.

3. **The counts were being compared across two frames, and the horizon law forbids it.** Seven of
   this map's layers carry double-width attention — measured, `{5, 11, 17, 23, 29, 35, 41}` — so a
   block spans 64 rows at 35 layers and 128 at seven, and the negative-hand count was a bare
   magnitude taken over populations of 163,840 and 327,680. **Magnitudes do not cross a frame
   boundary; a `Ratio` does.** Each population divides 327,680 exactly, so the counts are rebased
   onto that denominator with **zero remainder** — `H.0104`, not a normalisation.

**The rebase moved the return, which is why it is worth recording rather than quietly fixing.**
One-shot classes went `329 → 328` and collapsed pairs `7 → 8`: the un-rebased count had been
**spuriously separating** a pair that carries the same ratio in different frames. And the new pair is
`L34b4 (64 rows) ~ L35b0 (128 rows)` — **a pair across the two frames**, which the earlier reading
could not have seen at all, because the two counts were not comparable quantities.

**Every face is read off the weights**: the regime the entry walk sits at (`regime_reading`, built
the same day), the population carrying a negative hand, and the octave span. **No layer index, no
head index, no tensor name.** That is `CLAUDE.md` §8's returned-partition rule obeyed at the design
step rather than checked afterwards — had a face been the layout, a collapsed pair would restate this
driver's declaration table and carry no evidence. The one structural fact used is the successor, one
step along the residual stream, declared as **conduct** rather than as a face.

The executor **refuses by name** when no device is present rather than falling back to the host, so a
host figure can never be reported as though the deed had been mounted.

## 3 · What this does not establish

Eight collapsed pairs out of 336 says this three-face family is nearly discriminating **on this
material**; it says nothing about the map. A finer family collapses fewer and a coarser one more, and
the family here is declared, not derived.

**And "nearly discriminating" is a finding against the design, not for it.** A family that separates
328 of 336 on its first pass leaves almost nothing for `found_to_exhaustion` to work on: the
archetype the lift is looking for lives in what a family holds *together*, so a panel this fine has
pre-empted the founding it was supposed to feed. The next reading starts from **one** face and lets
the material add the rest.

The 1.094 s read is I/O against a 16 GB file, not compute. The single-head spectrum still stands
beside the sweep and is still one head at one layer — retained because it founds an axis by name, not
because it is the deed.

**And no timing figure here is a cost law.** Both were taken on one machine, in one frame, with the
card scanning out a desktop. What the 785× establishes is that the earlier figure measured **a chart
and not a cost**, which is the only thing it may be cited for.

**One correction to this record, made before it stood.** A first form of this paragraph said the
companion record
`2026-08-13_THE_DEPOSITED_MAP_IS_READ_BY_RATIO_AND_WINDING_THE_ARCHETYPE_IS_A_FINITE_TYPE_WITH_INFINITE_MODULI.md`
carries a 97.2 s figure needing correction. **It carries no timing figure at all** — grepped, and the
number lived only in this session's working notes. Asserting a defect in another document without
opening it is the same species as the absence claims corrected elsewhere today, and it is recorded
here rather than quietly deleted.
