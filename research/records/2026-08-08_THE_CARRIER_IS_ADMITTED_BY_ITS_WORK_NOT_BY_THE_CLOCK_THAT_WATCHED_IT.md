# The carrier is admitted by its work, not by the clock that watched it

**Date:** 2026-08-08
**Truth status:** `established-bounded` for §1, §2, §3 and §6 — each is a property of source read
directly, with the command that finds it stated. `interpretation` for the correction in §4: it has a
worked design, an existing organ to imitate, and a falsifier, but no implementation and no proof of
scope. `open` for the obligation it creates.
**Evidence:** direct source inspection of `crates/holonic-engine/src/cuda_aperture.rs` at `5e7501d`;
`computational-witness` for §6's reach finding — `cargo test --workspace --no-run` lists 28 test
executables and none is an example.
**Provenance.** Brandon, this session, ruling directly after being shown `cuda_aperture.rs:818`:
*"A clock timing sample should not be the decider of "carrier admission""* And the instruction that
produced this file: *"If you could pose the long-term more sophisticated solution so that we can
write it down as an essential correction, that would allow me to consider switching back to using my
graphics card on my desktop."* The ruling in §2 is his. **The design in §4 is assistant
interpretation and is graded as such; he has not ruled on it.** The occasion was a hardware
question — he asked whether moving his displays off the integrated GPU back onto the RTX 4080, which
has run headless since the laboratory era, would disturb the research.
**Band:** 2026-08-08 · BRANDON-RULED CORRECTION / ONE SITE CONVICTED / SINGLE-SAMPLE WALL CLOCK
GOVERNS CARRIER ADMISSION / EXACT WORK VECTOR ALREADY COMPUTED AND DISCARDED / ONE-SHOT PARITY
CONVICTED BY A MODULE IN THE SAME CRATE / ASSERTION ON THE RACE HAS ZERO REACH / DESIGN POSED, NOT
BUILT / SOURCE UNCHANGED / NO RUN

---

## Present question

The RTX 4080 SUPER has been pinned out of the display path since 2026-07-10 by one line —
`env = AQ_DRM_DEVICES,/dev/dri/igpu` in the desktop fork's `hypr/custom/env.conf` — so that, in the
hardware audit's words, *"the card is headless, so ordinary CUDA work has no desktop-impact gate"*
(`research/records/2026-07-12_THE_WHOLE_MACHINE_HARDWARE_AUDIT.md:17`).

Brandon asked whether undoing that pin would disturb the research. Auditing what actually couples
the desktop to the body returned one site, and it is not the site anyone would have guessed. It is
not exactness, not VRAM, not device enumeration. It is that **a single unrepeated wall-clock
comparison decides which of two exact carriers the body conducts through for the rest of its life.**

## 1 · What the source does

`crates/holonic-engine/src/cuda_aperture.rs:786-853`, `CudaApertureExecutor::admit`, fuses three
roles that are not the same role:

| role | site | state |
|---|---|---|
| **parity** — do both carriers return the same exact support? | `:809-816`, `has_same_exact_support` per receiver, `ParityRefused` otherwise | exact and correct |
| **cost** — what did each carrier cost? | `:808` one `Instant::now()/elapsed()`; `:817` the candidate's `wall_nanoseconds` | one wall-clock sample each |
| **admission** — which carrier does the body conduct through? | `:818` | **decided by the cost row** |

```rust
let candidate_nanoseconds = receipt.wall_nanoseconds;
let preferred = if authority_nanoseconds < candidate_nanoseconds {
    ApertureExecutionBackend::ExactHost
} else {
    ApertureExecutionBackend::HybridCuda
};
```

`preferred` is stored on `AdmittedCudaApertureExecutor` (`:875-878`) and thereafter routes **every**
subsequent trace (`:894`). One sample, taken once, on a contended machine, permanently selects the
carrier. There is no repetition, no variance, no confidence, and no `Open`.

The comparison is a genuine race, not a formality. In a mixed population the CUDA candidate does
neither more nor less work than the host authority: it packs every primitive, runs the device on
those under `MAX_DEVICE_INTERMEDIATE_BITS` (`:424`), runs the **host** law on those over it
(`:623-636`), and merges (`:703-718`), while the authority runs the host law on all of them. Which
side wins depends on the narrow/wide split of the material and on nothing else that is declared.

## 2 · Why a clock cannot decide this

Two independent arguments, and the second is the sharper one.

**It is a scalar that governs, not a scalar that measures.** `CLAUDE.md` §13 rule 2 was corrected on
2026-08-07 out of a blanket token ban into a jurisdiction test, on Brandon's direct correction that
gradients, distributions and losses are *"key and fundamental concepts"* whose contamination is a
matter of jurisdiction rather than vocabulary. The operative sentence: *a scalar that measures is
lawful; a scalar that governs is not.* `authority_nanoseconds < candidate_nanoseconds` selects
between two plural causal constructions and discards the loser. That is the governing side of the
line — `G_authored` in miniature. This is `holonic-engine` and not Soma, so it is not a literal
breach of the Soma ban; it is the identical shape, and the doctrine is written as a jurisdiction
test precisely so that it travels.

**The declared receiver family has already proved the two carriers indistinguishable, so the
question has no answer inside it.** This is the real defect. The parity gate at `:809` establishes
that under `{exact support, for these receivers, at this specification}` the two carriers return the
same thing. Having proved they cannot be told apart, the code then asks which one to keep — and
resolves it by consulting a coordinate that is not in the receiver family at all, and is not even
receiver-visible. It is *machine*-visible: CPU contention, frequency state, page cache, and — the
reason this record exists — whether the card is simultaneously scanning out a desktop.

That is `CLAUDE.md` §0's fourth lesson exactly: *"every contaminant found in two days was a
receiver-visible coordinate promoted into an invariant — an accepted-count into morphology, a mount
point into standing, a solver's pivot order into a reduction, one card's literals into an admission
rule. Each returned consistently until the frame moved."* This one returns consistently because
there has only ever been one frame. §5 is about giving it a second.

**Stated in §8's own instrument.** The gauge bullet requires a gauge to exhibit its distinguishing
word, and names `crates/holonic-engine/src/receiver_exact_compression.rs` as the organ that returns
one. Read the two carriers as the two declared schedules:

- on the **return** they are in the same block, and parity proves it — there is no distinguishing
  word, and there is not supposed to be one;
- the only axis on which they are *not* in the same block is **cost**;
- so cost is the only place this gauge can have a non-trivial orbit, and it is precisely there that
  the instrument takes one unreplicated sample off a wall clock.

This is the `PivotRule::ALL` precedent to the letter. There, an instrument built to prevent a defect
*was* the defect, because it declared three schedules and never checked they separated on the
material. Here, an admission built to choose between two carriers never checks that its
discriminator is a property of the material rather than of the afternoon.

## 3 · The one-shot parity defect underneath it

There is a second defect at the same site, deeper than the clock, and it is convicted by a module
compiled into the same binary.

`crates/holonic-engine/src/receiver_exact_compression.rs:18-19`, quoting `canon/01_CAUSAL_CALCULUS.md`:

> a quotient is exact only when *"stateful successor conduct remains equivalent for every admitted
> input history"* — **"equal one-shot output is inadequate."**

The parity check at `:809` is a one-shot reading. It establishes agreement on **one** presentation
at **one** specification, and on that basis admits a carrier for all future conduct. The module
whose entire content is that one-shot equality is inadequate sits four files away in the same crate.

Both defects have the same repair, which is why they are deposited together: run the carriers as a
**successor conduct across more than one declared aperture** and admit on the refinement, never on a
single frame.

## 4 · The correction

**Truth status:** `interpretation`. Not built. Six parts.

### 4.1 Split the three fused roles

`admit` returns three independent objects instead of one collapsed one: `ExactAgreement` (the parity
result, unchanged — it is already correct), `CarrierWork` (an exact work vector per carrier), and
`CarrierAdmission` (derived from a declared cost law over `CarrierWork`, and permitted to return
`Open`).

### 4.2 Cost is exact work, not elapsed time

`CudaApertureReceipt` (`:1017-1050`) **already carries the exact quantities, already as `BigUint`**:
`device_threads`, `device_output_bytes`, `exact_support_evaluations`,
`device_exact_support_evaluations`, `host_exact_support_evaluations`, `intermediate_bits`,
`aperture_members`, `conics`, `segments`, `device_primitives`, `host_primitives`, `host_workers`.

Every one is derived from the material and the declared aperture and reproduces bit-for-bit on any
machine, headless or not. The nanoseconds record how long *this* machine took to do that work.
`CLAUDE.md` §8 says grade the **complexity** — that is the work vector. It is computed and then
discarded in favour of a clock, which is the whole defect in one sentence.

### 4.3 Admission is four-state, and `Open` retains both carriers

Use the ordering this body already built: `crates/holonic-engine/src/exact_value.rs:64`,
`ExactOrdering { Less, Equal, Greater, Open }`, whose module opening states the principle directly —
*"Values which cannot yet be ordered from their exact certificates return `Open` rather than falling
through to an epsilon comparison."*

When the declared cost law does not separate the carriers on the exact work vector, the return is
`Open`, **both carriers stay retained**, and later conduct may use either or re-decide when the
aperture changes. A body holding two carriers it cannot yet separate is the correct state, not a
failure: §13 rule 2, *plurality is the return; a continuation fiber is not a number.*

An `Open` admission is also, incidentally, immune to compositor load, because nothing it consults is
a clock.

### 4.4 The cost law is declared, predictive, and carries a falsifier

`CLAUDE.md` §8: *"Grade the complexity against the source owner, measure both across a changed
aperture, and state the bound as a falsifier."* The site currently states no bound and has no
falsifier.

Declare the law as a **prediction computable from the aperture and the material without running
either carrier** — host work as a function of `aperture_members × selected_primitives`; device work
as `device_exact_support_evaluations` plus transfer words plus the host remainder for primitives
exceeding `MAX_DEVICE_INTERMEDIATE_BITS`. Running both carriers then either confirms the predicted
ordering or refutes it. A refutation is a first-class return (§8): it says the declared law is wrong
about this material, which is information the current code cannot produce at all.

### 4.5 Two apertures — the gauge must exhibit its own orbit

One aperture cannot distinguish a cost law from a constant. Admission must be taken across at least
two declared apertures whose work counts genuinely differ, and the orbit must be checked non-trivial
before the ordering is read as evidence. If two apertures yield the same ordering *and* the same
work ratio, the gauge has gauged nothing and the admission is `Open`.

**The material for this is already in the tree, unused.** `examples/desktop_receiver.rs` already
runs `640x400` and `640x720` and prints both profiles side by side. Nothing compares them. This is
the same shape as the `PivotRule::ALL` finding — *the separating material sat unused in the same
file.*

The return must carry **which aperture separated the carriers and by what exact margin** — the
analogue of the shortest separating word `receiver_exact_compression` carries per collapsed pair.

### 4.6 Nanoseconds are retained, demoted, and carry their frame

Keep every `*_nanoseconds` field. Under §13 rule 2's reconciliation they are lawful: a measurement
of difference, one receiver's reading, `L = ℓ_B(r)` — not a reward, not a judgment, not a governor.
Two constraints attach:

1. They may never appear in a comparison that selects a carrier.
2. The receipt must record the **frame** they were taken in. A measurement without its frame is the
   absolute-frame defect `CLAUDE.md` §0 names — the ten C++ card adapters that folded a filesystem
   path into rest integrity. Device name and host worker count are already carried. The missing
   coordinate is **whether the device had an active display**, which `nvidia-smi -q` exposes as
   `Display Active` and which currently reads `Disabled`.

## 5 · Why the hardware switch is the second frame, not a hazard

`CLAUDE.md` §0, fourth lesson: *"An invariant is only visible across two frames… A machine with one
frame cannot audit itself."*

Every timing figure in this repository was taken in one frame — headless card, idle desktop. No
timing claim here is currently falsifiable, because there is nothing to compare against. That is a
weakness of the corpus that the headless pin created and then concealed.

Once §4.6 lands, a run with the display on the card is not corrupted data. It is **the second
frame.** The exact work vector of §4.2 is frame-invariant by construction and must not move at all —
which is itself the check that the cost law is a law. Any timing figure that survives both frames is
a property of the material; any that moves between them was always a machine artifact, and the body
can now say which is which.

The sequence: make the correction, take a baseline in the headless frame, switch the displays, take
the same measurement in the display-active frame, and let the difference grade the law. Sharing the
card is the experiment.

**Measured frame declaration, 2026-08-08, for whoever takes the baseline.** RTX 4080 SUPER at pci
`01:00.0` → `card1`, exposing `card1-DP-1`, `card1-DP-2`, `card1-HDMI-A-1`, `card1-HDMI-A-2` — KMS
is already live, so the pin is purely Hyprland's backend selection. AMD Raphael at `0d:00.0` →
`card2`, currently driving the sole display on `HDMI-A-3` at `2560x1440@120`, 10-bit. NVIDIA
`Display Active: Disabled`, `Persistence Mode: Enabled`, `Compute Mode: Default`, 2 MiB of 16,376
resident, 0% utilization.

## 6 · Scope, and one reach finding

**One site.** The sweep, with its aperture stated so it can be re-run:

```
grep -rn "nanoseconds *[<>]\|elapsed() *[<>]\|_ns *[<>]" --include='*.rs' crates/ soma/
```

- `cuda_aperture.rs:818` — the only place in the body where a wall clock governs what the machine
  conducts through.
- `RUN_LIMIT` comparisons across `soma/life/examples/eros_*` — driver stopping conditions, outside
  the body. Lawful.
- `mms_reconnection_traversal.rs` `chronology_ns` — spacecraft instrument chronology, i.e. source
  material, not machine timing. Lawful.
- `soma/life/examples/eros_cohered_corpus.rs:980-997` — adjacent and **not** cleared: it extrapolates
  a measured wall time to full-corpus scale and thresholds it against `MAX_ACCEPTED_PROJECTED_MICROS`
  to return `projected_under_one_hour`. A feasibility report in a driver rather than a carrier
  admission, so it is not this defect, but it is a timing-derived threshold and it is named here so
  it is not lost.

**The assertion on the race has zero reach.** `examples/desktop_receiver.rs:2745` contains

```rust
assert_eq!(cuda.preferred_backend(), ApertureExecutionBackend::ExactHost);
```

inside `cuda_packed_support_is_exact_and_wide_input_falls_back_without_loss` — a hard assertion on
the outcome of the wall-clock race. **It does not run.** `crates/holonic-engine/Cargo.toml` declares
no `[[example]]` section, so Cargo's default `test = false` applies and the `#[cfg(test)]` block is
stripped when the example is built. Verified rather than assumed: `cargo test --workspace --no-run`
lists 28 test executables and not one is an example.

Two consequences. The workspace gate does **not** contain the race, so switching the displays cannot
break it today — the hardware question is answered, and answered in the affirmative. And by §8's
reach rule this is its own small finding: an assertion on a timing race, never executed, ungraded.
When §4 lands it should be rewritten against the exact work law and moved somewhere that runs. Until
then, `cargo test --all-targets` and `cargo test --examples` would pull the race into the gate and
should be avoided.

## 7 · What this record does not claim

- It does not claim the returns are wrong. They are not. The parity gate is exact and refuses on
  disagreement; no integer result anywhere in this body depends on the clock.
- It does not claim the current admission usually picks badly. It probably usually picks correctly.
  The defect is that *nothing on file says why*, and a decision no one can check is the same defect
  whether or not it happens to be right.
- It does not claim `Open` is always the right admission. It claims `Open` must be **available**,
  which it currently is not.
- It grades the design in §4 as `interpretation`. Nothing in §4 is built, and no roadmap row closes.

## Owners

**None.** This record asserts no implementation. The paths named above are the **site of the defect
and the organs to imitate**, not owners of anything this record built:

- `crates/holonic-engine/src/cuda_aperture.rs` :: `CudaApertureExecutor::admit` — the convicted site
- `crates/holonic-engine/src/exact_value.rs` :: `ExactOrdering` — the four-state ordering §4.3 adopts
- `crates/holonic-engine/src/receiver_exact_compression.rs` — the distinguishing-word instrument §2
  and §4.5 argue from
- `crates/holonic-engine/examples/desktop_receiver.rs:2745` — the assertion with zero reach
