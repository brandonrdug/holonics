# The documents described a body they had not opened, and the operand had no residency

**Date:** 2026-08-13
**Truth status:** `established-bounded [measured]` for every figure below; `implemented-exact` for
the alignment guard, the device residency, and the batched grid.
**Evidence:** `measured` on this machine, RTX 4080 SUPER with an active display. Commands and
`file:line` citations are given inline; every claim about code was taken by opening the file.
**Occasion:** Brandon, closing the day: *"Scope out, we're done with the transformers now. Audit and
review the machine, use agents."* And the sentence that set the object: *"None of what I have said
in this session is new, this is egregious."*
**Band:** GRADE THE IMPLEMENTATION, NOT THE RECEIPT / A CENSUS IS A MEASUREMENT AND DECAYS LIKE ONE
/ THE INVARIANT CROSSES ONCE / A SIGN IS A PASSAGE AND NEVER A STATE

---

## Present question

The day's work sat entirely uncommitted, and the day's corrections were almost all repetitions of
rules already written down. What is actually wrong — with the tree, with the documents, and with the
one organ that reached the card?

## 1 · The claim was checkable and it checks out

About 23 of ~55 substantive messages on 2026-08-13 were corrections, and **each maps to a rule
already in force**:

| correction, and how many times it was issued | where it already lived |
|---|---|
| the card is idle / one core — **7 today, plus once to Sol on 08-12** | `CLAUDE.md`, *"The GPU owns the deed"*; `AGENTS.md`, the apparatus clause |
| stop rediscovering, use the network — **6** | `canon/THE_EXPLORATIVE_FAILURE.md`; the partials rule |
| overcomplication / a fabricated wall — **3** | `canon/THE_DIALECT.md`, which measures *"You overcomplicated it"* at ~7% of every message he has ever sent — the dominant archetype in the corpus |
| no floats, no percentages — **1** | the no-float law and the horizon law |
| signs are directions, do not `.abs()` — **1** | the sign-is-a-passage law |
| scalars are not the return — **1** | the causal-atlas-before-its-scalars rule |

**So the rules were not missing.** They are read at session start and then not consulted while
working — and, as §2 shows, several of them were describing a body that no longer existed, which is
why re-reading them did not help.

## 2 · Four false statements in the governing documents, each verified by opening the file

Every one is the same defect: **a document asserting the state of code nobody opened.**

1. **`positive_form` was convicted of being deleted while live.** `CLAUDE.md` carried *"CORRECTED
   2026-08-11 by reading the owner: `positive_form` was REMOVED 2026-08-08"*. It is
   `crates/holonic-engine/src/supported_realizers.rs:173`, called at `:333` by `induced_placement`,
   imported by three drivers. The error is a **misparse of the module's own sentence** — *"A test
   asserting it was removed 2026-08-08"*, whose subject is the test. A correction that convicted a
   live organ, in the file every session reads first, two days old.

2. **`kelvin` was called unreached in three documents while driven.**
   `crates/holonic-engine/examples/the_loop_carries_its_circulation.rs:58` imports it, committed
   `27fc74d` on 2026-08-10. The roadmap, the spine and the position record all carried in-degree
   zero. `CLAUDE.md` meanwhile *described driving it*, with the nine-of-nine junction result.

3. **A deleted module was listed as a live 273-line organ.** `soma/abi/src/cuda_execution.rs` was
   removed 2026-08-10 (`soma/abi/src/lib.rs:16`). It sits in the same table as `kelvin` in all three
   documents. **The named-path gate passes it** because a mirror copy sits under
   `reference/engine-a07ff376/` — a live document naming a deleted live path, resolved against an
   archived one.

4. **A document contradicted a module built the same day.** `canon/THE_INFORMATION_ENGINE.md`
   reported a *live measurement dated 2026-08-13* of zero owners for fractal, Hausdorff and
   box-counting; `crates/holonic-engine/src/regime_reading.rs`, built that day, cites that passage
   as the gap it closes and supplies ten. **The absence was true when taken and false in the tree it
   was committed into.**

**The common cause of 2 and 3 is one thing: a `now` column copied forward from a mechanical census
taken 2026-08-08 and never re-run**, into three documents. A census carries its date; a reading off
it does not inherit one.

### Smaller, same shape

The pickup table said "nine" over ten rows. `without_stem`'s line citation had drifted a **second**
time (`:352`/`:1516` → `:525`/`:1758`). `THE_MEASURED_CAPABILITIES` called `cross_ratio` private and
unwritable across the crate seam when it is `pub`, exported, imported by
`the_swing_is_the_invariant.rs:64`, and printed there as `cross_ratio(T.p) == cross_ratio(p)`; and
it named a gauge defect that had been repaired **the same day the file was deposited naming it**.
`tools/claim_index.py` omitted `THE_TIMELINE.md` from the spine it declares itself a copy of, and
`--check` structurally cannot catch that: it compares the index to the generator, never the
generator to `CLAUDE.md`.

### The owner atlas, audited on its day of deposit

Thirteen citations sampled: **13 of 13 resolve at the commit, 10 of 13 already fail against the
working tree**, because 12 of the 19 files it cites were edited the same day. This is the standing
condition of the genre, not a sampling artifact, and the file now says so. A line number is the most
perishable thing an index can carry.

## 3 · Provenance is clean, and that is worth recording

Every quoted span attributed to Brandon in the day's nine records and three new canon files was
checked against **all 49,615 of his messages** across `~/.claude/history.jsonl`,
`~/.codex/history.jsonl` and every rollout under `~/.codex/sessions/`. **No fabricated quote.** The
composite-quotation failure convicted on 2026-08-08 did not recur.

Method and its limit: quoted spans of ≥8 words carrying an attribution marker, normalised and
matched as 7-grams against the conversation corpus, with misses re-checked against the repository's
own documents (a quote copied from a document is lawful). Spans shorter than that, and paraphrase
presented without quotation marks, are outside the instrument.

## 4 · The tree: 90% of the day's diff was formatting

207 modified Rust files. Formatting the committed blob with the current rustfmt and diffing against
the working tree separates them exactly:

```text
   180 files   changed by `cargo fmt` alone      (2024 style edition: import order, brace reflow)
    27 files   carry semantic change
```

The whole day sat uncommitted, **`standing/` received nothing**, and the instrument behind the
largest deposit was untracked. Split into three commits — the sweep, the work, the normalisation —
the day's real diff is legible for the first time.

**The ownership ratchet was red for a real reason**: 27 new occurrences, of which **20 are in
existing owners** (`codec_recovery.rs` Vec 150 against 79 allowed, `codec_system.rs` 87 against 60,
`derivation_codec_intake.rs` 56 against 44, `incidence_production.rs` 123 against 115) and 7 are the
two new modules at a zero baseline. Construction moved the wrong way on the one gate that measures
materialization discipline.

## 5 · The card was idle for three different reasons, and only one was a defect

The complaint was raised seven times and answered by measuring each driver rather than by hedging:

| driver | GPU peak | RSS | why |
|---|---|---|---|
| `the_readout_returns_a_fiber_not_a_winner` | 79% | 7,985 MB | 6 seeds × 131,072 rows — one large deed per mount |
| `the_readout_founds_its_own_receivers` | 75% | 470 MB | 4,096 serial calls re-uploading one invariant |
| `the_foreign_map_founds_its_axes` | 4% | 114 MB | the card receives 336 items of 3 fields; the bulk reduction is elsewhere |
| `the_map_deposits_and_a_later_current_rides_it` | 0% | 5.4 MB | **never opens a context** |
| `the_later_current_rides_the_deposit` | 0% | 5.4 MB | **never opens a context** |
| `the_foreign_codec_is_recovered_from_its_testimony` | 0% | 255 MB | **never opens a context** |

**The three zero rows have nothing for a card to carry.** `the_map_deposits_and_a_later_current_rides_it`
opens a four-billion-parameter safetensors and takes **twelve rows of 320 entries** out of it;
`the_later_current_rides_the_deposit` declares an extent of 8 and returns 10 constituents and 13
contacts; `the_foreign_codec_is_recovered_from_its_testimony` declares a six-character alphabet
against a 514,906-entry merge table. Real material, an aperture written inside the driver, a toy.
That is *an archetype does not define the experiment*, recurring.

**No driver in this workspace uses more than one core.** No `rayon` in any manifest;
`std::thread::scope` exists in `executor.rs` and `thread::spawn` in two more owners, and none of the
new code calls them. The committed reference driver measures 99.0% CPU as well. Single-core is the
workspace's CUDA-driving shape, not a regression: every executor is driven from a serial loop.

**And the kernel chain was never broken.** `exact_embedding_fiber.cu` → `build.rs` nvcc
`--ptx compute_89` → PTX → `include_bytes!` → `cuModuleGetFunction` on every symbol → three
`cuLaunchKernel` sites. It builds, loads and launches. Two of six drivers reach it.

## 6 · What was actually wrong, and it is a residency, not a kernel

`ResidentReadout::score` declared **every device pointer as a local inside the call** — allocate,
upload the whole readout, launch, free. The 4,096-question driver therefore moved the same 83,886,080
octets 4,096 times:

```text
   4096 x 83,886,080  =  343,597,383,680 octets across the bus
```

measured as a sustained 13–15 GB/s of receive traffic for the whole run, for arithmetic worth
milliseconds. Nothing about the kernel was wrong. `cuda_refine.rs` already owned the shape — an RAII
`Buffer` and a `DeviceCorpus` whose comment reads *"the whole corpus, laid out once for the
device."*

**Repaired by routing through what exists rather than by adding an organ:**

- `MountedReadout` owns the device allocation and releases it on drop; `mount` uploads once;
  `score` becomes `mount(…)?.score(…)`, so every existing caller is unchanged.
- `score_many` takes a query population and issues **one grid**, `blockIdx.y` selecting the query.
  `dim` was already a stride in the kernel, so the batched deed is the same arithmetic indexed —
  `exact_readout_scores_batched`, thirty lines beside the three that were there.
- The launch geometry now comes from `cuda_aperture::DerivedLaunch`, lifted into
  `from_admissions` so the rule lives in one owner. `embedding_fiber` had written
  `max_threads.min(256).max(1)` — a level authored inside the organ, blind to the warp and blind to
  what its own kernels admit.

**Measured, same driver, same material, same returns:**

```text
   before   4,096 launches, 343.6 GB across the bus, 42.0 s wall
   after    map mounted once in 4.2 ms, 83.9 MB across the bus,
            4,096 constructions transported in 6 grids in 895.96 ms, 16.0 s wall
```

The remaining 14.15 s is `found_to_exhaustion`, which is a different organ and a different question.
The bus traffic falls by a factor of 4,096 exactly, and that figure is arithmetic rather than a
clock.

**Graded by a parity test that can fail:** three queries with **distinct exponents**, batched
against per-query against the independent serial chart, all three populations required to be equal
and required to differ from each other — so a batch that scored one query three times, or carried
one query's frame to all of them, fails rather than agreeing vacuously.

## 7 · A silent sign flip, and the parity test could not have caught it

`align_bfloat16` guarded `if spread >= 63` and then called `significand.checked_shl(spread)`.
**`checked_shl` refuses an out-of-range shift *amount* and never inspects the value.** So:

```text
   spread 56, positive significand  ->  Some(-72057594037927936)
   spread 60, negative significand  ->  Some(+1152921504606846976)
```

The magnitude carries into the sign bit, `Some` comes back, and **the hand is reversed** — on a
conduct path, in a body whose standing law is that a sign is a passage and never a state. The
resident-versus-serial parity test is structurally blind to it: both charts consume the same
already-wrapped material and therefore agree on the wrong value.

The demand is the entry's **own octaves plus its spread**, and the spread alone cannot decide it —
a spread of 40 is admissible for a one-octave entry and inadmissible for a twenty-four-octave one.
Repaired with `FiberError::AlignmentOverflows { octaves, spread, needed, carrier }`, a separate
refusal because it has a separate cause, and a test that exhibits the wrap it prevents.

On the Gemma material the spread tops out near 33, so **this never fired in any deposited figure**.
The guard was about thirty octaves too loose and nothing would have said so.

## 8 · The float left library source

`embedding_fiber.rs`'s zero-remainder test evaluated its claim in `f64` — the only machine-float
*arithmetic* in any library `src/` in the workspace, checking a rebase in the very carrier the module
exists to avoid. It now checks against the decoded `(significand, ulp_exponent)` pair in exact
integers, as a left shift by the spread, with no division anywhere. Strictly stronger, and the
workspace's library sources carry no float arithmetic at all.

## 9 · 222 GB of abandoned agent worktrees

Four full checkouts under `.claude/worktrees/`, dated 2026-08-10 and 08-11, each with its own
`target/`: 223 GB, **untracked and not ignored**, one `git add -A` from being staged. The repository
directory measured 540 GB.

Before removal, every symbol their uncommitted edits added was checked against main and found
present — merged by `e2d1c6e` on 2026-08-11. The patches were saved regardless. `.claude/` is now
ignored, with the reason written where the next reader will meet it.

```text
   repository directory   540 GB -> 318 GB
   free on /home          321 GB -> 378 GB
```

## 10 · What is open

- **The deposited-map record's statistics** rest on 336 per-head units that are 84 under
  grouped-query attention, on three control figures with no committed producer, and on a `1e-9`
  float threshold producing the integers it calls Windings. The errata block is in place; the
  figures are not retracted and not defended until their scripts exist.
- **Two claims reported by the audit and not verified here**: that a matched random operator beats
  the transported median, and that the raw embedding beats the headlined archetype. If either holds,
  the corresponding claim is inverted rather than merely overstated. Both are cheap and neither is
  checked.
- **The three zero-GPU drivers** need their apertures decided by the material rather than by a
  constant in the driver. Routing them to a card changes nothing; what their apertures exclude is
  the finding.
- **The ownership ratchet** is red in six existing owners and wants a pass of its own.

## What this record is not

It is not a construction schedule. The roadmap and the position record remain the only scheduling
authorities.
