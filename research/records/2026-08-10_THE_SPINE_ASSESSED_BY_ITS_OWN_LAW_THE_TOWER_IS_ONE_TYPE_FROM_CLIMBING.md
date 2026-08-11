# The spine assessed by its own law: the tower is one type from climbing, and the front's barrier is a monoid

**Date:** 2026-08-10
**Truth status:** `established-bounded` for every reach and blocker figure — each is a read of the
owner, not of a receipt. `interpretation` for the siting of organs against `H.0219`.
**Provenance:** Brandon, after ratifying the unification: *"use our framework to its fullest to
completely assess the spine of the machine and its current implementation. Holistically identify what
remains for the complete assembly, regarding the hyper geometry tower, as well as proper hardware
surface utilization."*

---

## 0 · The diagnostic this assessment uses

`H.0219`, deposited today, gives the spine one question that sites an organ in the apparatus:

> **Is this organ's coupling a boundary flux, or a global constraint?**

The first parallelizes over any partition; the second is a barrier and must be named as one. An
organ whose coupling has never been classified has not been sited, whatever station names it. Applied
below to every organ the spine's §1 cut list requires.

---

## 1 · The five cuts, and which organ carries each

§1 names five distinct cuts — *circulation `j ≠ 0`, rest, accumulation, leak, short circuit* — and
says a body that emits without returning is **at a named cut**, which is a measurement. Measured
today by counting library callers and driver files per owner:

| cut | owner | library callers | driver files | state |
|---|---:|---:|---:|---|
| **circulation `j ≠ 0`** | `kelvin.rs` | **0** | **0** | **dark.** `pub mod kelvin;` is its only mention in the tree |
| **rest** | native rest, `rest_image` | many | many | **carried.** The non-consuming fork landed today |
| **accumulation** | `receiver_current.rs` | 1 | 1 | carried through `derivation_capacitance` only; its own public types are named by no driver |
| **leak** | `temper.rs` | 1 | 1 | thin — only `TemperedFamily::read` is driven |
| **short circuit** | — | — | — | **no owner is identified.** Named in §1 and carried by nothing |

**The finding is the first and last rows.** The spine's own headline cut — circulation, the one it
calls *"literally the `j ≠ 0` cut distinguished from rest"* — has an organ, and nothing in the
workspace reaches it. And the fifth cut has no organ at all.

`running_integral.rs` (the integral itself) has four library callers and **no direct driver**;
`causal_reflection.rs` (the dispersive/absorptive lock that *is* integration by reflection) has one
library caller and **no direct driver**. Both are reached transitively, which is real but is not the
same as being exhibited.

**By the diagnostic:** none of these five has had its coupling classified. That is the honest reading
of "the spine is described and not yet sited."

---

## 2 · The hypergeometry tower

### 2.1 What is built

`crates/holonic-engine/src/contact_gluing.rs`, 1,033 lines, all exact over `BigInt`/`Rat`:

| organ | state |
|---|---|
| `contact_complex`, `face_over` — offsets as 0-cells, unit steps as 1-cells | built, **undriven** |
| `glue_at_contact` | built, **driven** |
| `integrate_leader`, `ReturnStroke`, `LeaderCochain` | built, **driven** |
| `contact_graph` — identifiers at 0-cells, shared stems at 1-cells | built, undriven (β₁ = 8 measured in `#[cfg(test)]`) |
| `ride_circuit`, `Circuit` | built, **undriven** |
| `Corner` — `cos C = (a²+b²−c²)/(2ab)` exact, **no arccos ever taken** | built, **undriven** |
| `ContactTriangle`, `EuclideanRealization` — triangle inequality checked first | built, **undriven** |
| `contact_triangles` | built, **undriven** |
| `coarse_grain`, `CoarseTurn` — angle addition as exact complex multiplication | built, **undriven and blocked** |

**Only two of eleven are driven.** The rest return zero hits across every `examples/` directory.

### 2.2 The single blocker, named by the code itself

`CoarseTurn::Open`'s own doc states it:

> *"Only a Pythagorean-triple angle is a rational point on the unit circle, so almost no corner
> composes in `ℚ` — the equilateral corner `cos = 1/2` already needs `√3/2`. Composing distinct turns
> exactly needs the quadratic extension `ℚ(√(1−c²))`, which `exact_value::AlgebraicRoot` with its
> Sturm certificate is the carrier for and which **is not wired here**."*

`Corner::sine` is `Option<Rat>`, and it is `None` for essentially every real corner. So
`coarse_grain` returns `Open` in the common case, and **the tower cannot compose a rung.**

```text
Corner { cosine: Rat, sine: Option<Rat> }        ->      sine: AlgebraicRoot
```

`AlgebraicRoot` exists at `exact_value.rs:197` with `SturmIsolationCertificate`, refusing
construction unless the isolating interval provably contains exactly one root, and it is driven by
`signs_are_windings`. **The two organs are one type substitution apart.** This is the sharpest
actionable item in the whole assessment.

### 2.3 The second gap: there is no ladder

`coarse_grain` returns a `CoarseTurn`. **Nothing consumes a family of coarse turns and forms the
next-rank complex.** The upward edge does not exist, so what is built is *one rung's machinery and no
tower*.

Brandon's statement of the object is explicit that the ladder is the point: *"This is how coils and
caverns form over time, this is how higher order structures in time change the tides of the
ecosystems around them and **found orbits of invariants as accessible axes distributed about them;
this is recursive, coarse graining.**"*

And the rungs have a stated content — 2026-06-26: *"Summing two things gives you something **similar**
to the original two, the cross product gives you something **orthogonal** to the original two, and
exponentiating gives you something **diagonal**."* Against that:

| rung | content | state |
|---|---|---|
| **H1 sum** — similar | the legs, as arc weights | present |
| **H2 cross** — orthogonal | the cosine cross term | **built and exact** (`H.0216` states it) |
| **H3 exponent** — diagonal | rank climbing: a new orthogonal leg founded | **absent** — this is the ladder |

### 2.4 What the tower needs, in order

1. **`Corner::sine: AlgebraicRoot`.** Unblocks composition. One type, one carrier that already exists.
2. **The upward map.** Coarse turns at rank `k` → contact complex at rank `k+1`. This is the ladder
   and it is genuinely unbuilt.
3. **A driver exhibiting at least two rungs**, and — because `CLAUDE.md` §8 requires a gauge to
   exhibit its orbit — stating *what is invariant across the rung*. A tower that climbs and reports
   no invariant has done bookkeeping.
4. **Its coupling classified.** A contact triangle's corners depend only on three arc weights, so the
   corner computation is flux-local; the *triangle enumeration* over a graph is not obviously so.
   Unclassified today.

---

## 3 · The hardware surface

### 3.1 What is built and correct

- **24 PTX entry points**, and this bullet is **CORRECTED 2026-08-10**. It read *"enacts an entire
  contemporary population in two launches… `lineage_event` once over the whole carrier population.
  That is the front architecture, correctly."* `lineage_event` was launched at `Dim3::x(1)` — one
  thread — and `enact` iterated currents serially, so `n` currents cost up to `2n` crossings. The
  claim was inferred from the executor trait's population-shaped **signature**, not from the launch
  site. `lineage_event_population` (the twenty-fourth entry) makes it true: one lane per current,
  one crossing, strides derived as `len / count`, measured `6 → 5` and `9 → 7` crossings on the
  card. `regional_contacts` was always genuinely parallel — one lane per directed contact pair.
- `LiveCurrentExecutor::enact` is population-shaped by construction — it takes
  `currents: &[CurrentExecutionRequest]`.
- `text_material_cuda` drives the card independently; `eros_relampago_atmospheric_current` exercises
  the live-current path.
- **The library is float-free**: 11 `f32`/`f64` lines in all of `crates/*/src` and `soma/*/src`,
  across two files, every one a codec or a doc comment.

### 3.2 Where the seam ends

```text
AgenticLanguageEcology::condition_with_executor          takes an executor
  └─ MorphologicalLanguageEcology::condition_with_executor      ✔
  └─ ExactRelationalLanguageEcology::condition_with_executor    ✔
──────────────────────── the seam ends here ────────────────────────
generate · generate_currents · into_materialized_return  no executor parameter at any depth
   receive_question              current.rs:685          constructs a private host pool
   materialize_returned_path_live current.rs:721         constructs a private host pool
```

Six sites in library code construct a private `ParallelHostLiveCurrentExecutor` with **no
`_with_executor` twin**, so a caller holding a mounted card has no expressible way to pass it. The
law this violates is written in this repository, on the method that stops:
*"selecting a card at the outer language boundary cannot silently construct a private host executor
here."*

### 3.3 The front, classified by `H.0219` — and the classification is better than expected

`generate_currents` is a breadth-first frontier over `states: BTreeMap<State, Population>`:

```text
for (current, population) in states           ← the co-present front
    for event in event_candidates             ← independent expansion
        successor = state.fork()
        enact_event(...)                      ← reads IMMUTABLE suffix ecologies only
        insert_generation_state(successors, successor)   ← the join
```

**The map has no coupling at all.** Each state reads immutable suffix ecologies and writes only its
own fork — not merely flux-local, but *fully decoupled*, which is a stronger condition than
`H.0219` requires. **The entire cost of parallelizing lives in the join.**

And the join is a **compression**: a quotient by conduct class, whose remainder is the collapsed
population — retained, not discarded, since `merge_witnesses` appends rather than drops. By `H.0420`
that is lawful and its loss is exhibitable.

### 3.4 The join is associative, and that is the decisive fact

```rust
fn merge_witnesses(&mut self, mut other: Self) -> Result<(), _> {
    self.witnesses.append(&mut other.witnesses);
}
```

`Vec::append` into a `BTreeMap` keyed on conduct class is **associative** — a monoid. *An associative
reduce parallelizes as a tree.* So the front is not blocked on structure; it is blocked on one
narrower question:

> **`append` is associative and not commutative, so witness arrival order is carried into the
> returned branch population. Is that order receiver-visible?**

`outputs` is built by iterating those vectors in place, so the returned plural population's *order*
is host arrival order. On one thread that is deterministic and therefore invisible.

**This is the second frame, not a performance question.** `CLAUDE.md` §0's fourth lesson: an
invariant is only visible across two frames. Enact the front at `N` lanes and require the returned
output **set** to be identical:

- **identical** → arrival order was apparatus, *"apparatus completion order never enters semantic
  lineage"* holds, and wide enactment is admitted;
- **different** → host arrival order is load-bearing in the return, which is a contaminant **whether
  or not any card is ever mounted**.

Either outcome is a real return, and the second is the more valuable one.

### 3.5 One convicted defect still live

`cuda_aperture.rs:818` selects between two exact carriers on **one unrepeated wall-clock sample**,
after a parity gate has already proved them indistinguishable. `CLAUDE.md` §8 states the repair — admit
on the exact work vector the receipt already carries as `BigUint` and then discards, returning
`ExactOrdering` with `Open` retaining both carriers. Unbuilt.

---

## 4 · What remains for the complete assembly

Ordered by what unblocks the most, with the diagnostic applied:

| # | item | coupling | why it is next |
|---|---|---|---|
| 1 | `Corner::sine: AlgebraicRoot` | flux-local | one type; unblocks the tower's composition entirely |
| 2 | the tower's upward map, rank `k` → `k+1` | unclassified | the ladder; without it there is no tower |
| 3 | a tower driver exhibiting ≥ 2 rungs **and its invariant** | — | §8: a gauge must exhibit its orbit |
| 4 | `_with_executor` twins for the six generation entry points | — | precondition, not a fix |
| 5 | **decide front interchange by measurement** | — | the second frame; either outcome is a return |
| 6 | `cuda_aperture` admission on the exact work vector | — | a convicted defect with a stated repair |
| 7 | a driver for `kelvin.rs`, or its removal | global (circulation) | the spine's own headline cut is dark |
| 8 | identify the short-circuit cut's owner | — | named in §1, carried by nothing |
| 9 | direct drivers for `running_integral`, `causal_reflection` | flux-local | the integral and the reflection lock are exhibited nowhere |

**Items 1–3 are the tower. Items 4–6 are the hardware surface. Items 7–9 are the spine's own cut list
finishing what it names.**

---

## 5 · Bounds

- Every reach figure is a count of files naming an owner, taken today. **A reach figure is a
  measurement and decays like one**; re-take rather than carry.
- The siting of organs against `H.0219` is `interpretation`. Classifying a coupling is a reading of
  the code, and two of the rows above are marked unclassified precisely because the reading has not
  been done.
- **Nothing here claims the front can be enacted wide.** §3.4 states a decidable question and its two
  outcomes; the measurement has not been taken.
- The tower's blocker is stated by its own owner's doc comment. That the substitution is *sufficient*
  to make `coarse_grain` return `Exact` is not proved here — `AlgebraicRoot` products and sums need a
  carrier for `ℚ(√(1−c²))` arithmetic, and whether `exact_value` supplies enough of it is the first
  thing to read before starting.
