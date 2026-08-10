# The front is the parallel unit, and the apparatus mouth stops before generation

**Date:** 2026-08-10
**Truth status:** `established-bounded` for the map and the seam measurement; `open` for the
construction it names, which is deliberately not attempted here.
**Evidence:** direct source inspection of the executor seam, the PTX entry table, and the
generation frontier; phase-stamped timings from an instrumented driver run; `nvidia-smi` at 0 %.

**Provenance.** Brandon, mid-run, on being shown a driver at 100 % of one core with the card idle:

> *"You naively call the card the 'hot path' and speak like it's acceptable that the card isn't
> being utilized firstmost ahead of the CPU, when the parallelization is essential to the physics.
> This is a longstanding problem, there are many failure modes associated with implementing holonics
> across agnostic hardware distributions… The theory cannot be dropped here, you cannot try to wing
> it and implement on the fly for this."*

He is right and this record exists because of it. What follows is the map he asked for before any
construction.

---

## 0 · What I got wrong, stated first

I reported the idle card as a **fact about reach** — *"the language body cannot reach the card,
mounting CUDA would move 60 ms of conditioning and none of the 20 minutes"* — and let that stand as
though it settled the question. It does not settle it. It is an apparatus observation, and the
project's own doctrine already rules on exactly this:

> *"Low utilization is a diagnostic receiver, not an explanation; **locate the active
> causal/apparatus mouth** before modifying code."*
> — `archive/blueprints/REALIZATION_AND_HARDWARE.md`, Telemetry aperture

The archive banner on that file is explicit that this survives the body it was written for: *"the
apparatus laws it states are language-independent and survive; the realization choice it names does
not."* So the correct response to 0 % was to locate the mouth, which is what this record does.

**The failure archetype, named so it is checkable:** *reporting an apparatus coordinate as a
semantic conclusion.* "The card is idle" and "the card cannot help" are different claims; the first
is a measurement and the second is a construction verdict, and I moved from one to the other without
doing the work in between. It is the same shape as `CLAUDE.md` §0's fourth lesson — a receiver-visible
coordinate promoted into an invariant — one level up, at the apparatus.

---

## 1 · The ontology: what parallelism *is* here

Not an optimization. `REALIZATION_AND_HARDWARE.md`, *Parallelism*, and every clause matters:

```text
one thread/current is serial along its own caused order;
a FRONT contains co-present local events with PROVED INTERCHANGE;
work partitions by local incidence/support, not by semantic category;
overlaps use declared interaction/gluing and return residual stress;
feedback opens only through an explicit returned boundary; and
apparatus completion order NEVER enters semantic lineage.
```

and the prohibition:

> *"Cards are built for wide local operations over vertices, edges, cells, fields, rays, particles,
> constraints, and sparse incidence. Express algorithms in those elementary terms wherever their law
> actually has that geometry. **Do not translate a serialized host foreman into a monolithic kernel
> and call it parallel.**"*

So there are exactly three species of plurality and they are not interchangeable:

| species | shape | lawful realization |
|---|---|---|
| **a path** | ordered continuation; each step's predecessor is the previous step's return | serial, by the physics |
| **a front** | co-present local events at one instant, interchange **proved** | wide, one launch |
| **a category** | "these are all clauses" | **not a partition** — the doctrine forbids partitioning by semantic category |

The spine states the same thing at the level of the loop: `∂E_k = Σ_{k+1} − Σ_k + Γ_k`, and the five
distinct cuts — *circulation `j ≠ 0`, rest, accumulation, leak, short circuit*. A front is one
instant's `Σ_k`. Serializing a front does not merely take longer; it **imposes an order the physics
does not have**, and by the last clause above that order must never enter lineage.

---

## 2 · The apparatus surface that exists, measured

This is not a machine lacking a device path. It has a substantial one.

**23 PTX entry points** in `soma/mount/soma-kernel-cuda/soma_kernel_cuda.ptx`:

```text
regional_contacts   lineage_event
chart_count  chart_mark  chart_recast  chart_register_mark
link_finish  link_founded_grain  link_founded_sum  link_grain
link_register_finish  link_register_grain  link_register_sum  link_sum
register_carrier_rebase  register_own_recast  register_own_recast_finish
scope_felt  scope_founded  scope_register  scope_register_surface
text_incidence_select  text_section_restrict
```

plus two hand-written engine kernels, `crates/holonic-engine/kernels/exact_conic_support.cu` and
`exact_relation_support.cu`, and a committed `soma/kernel/soma.spv`.

**`CudaLiveCurrentExecutor` enacts a whole contemporary population in two launches**, which is
exactly the front architecture:

- `regional_contacts` — **`pairs.len()` parallel lanes**, one per directed contact pair, forming
  every receiving current's immutable standing-before field at once
  (`live_current_cuda/executor.rs:74-99`);
- `lineage_event` — **once per `enact` call**, taking `carriers`, `owns`, `relations` as spans over
  the whole population, changing every current's sole mutable carrier (`:416-425`).

Its own opening states the residency law: *"One context and one module remain mounted… No active
cut, dataset, journal, receipt, or ancestry population is allocated on the card."*

**The trait is substrate-neutral and population-shaped by construction:**

```rust
fn enact(&mut self, physical_revision: u64, standing: &SparseStandingSurface,
         currents: &[CurrentExecutionRequest<'_>],       // ← the front
         relations: &[DirectedExecutionRequest],
         regional: &[RegionalExecutionRequest<'_>]) -> Result<ExecutedContemporaryEvent, _>;
```

*"Implementations may own a resident host pool, CUDA context/module/buffers, or another substrate,
but receive no source material, cut, journal, receipt, or standing-after authority."*

**The device path is correct, complete, and idle. Nothing presents it a front.**

---

## 3 · Where the seam terminates, measured

The executor threads down three levels and then stops:

```text
AgenticLanguageEcology::condition_with_executor        ✔ takes &mut dyn LiveCurrentExecutor
  └─ MorphologicalLanguageEcology::condition_with_executor   ✔
  └─ ExactRelationalLanguageEcology::condition_with_executor ✔
─────────────────────────────── the seam ends here ───────────────────────────────
MorphologicalLanguageEcology::generate                 ✘ no executor parameter
  └─ generate_currents                                 ✘ no executor parameter
  └─ into_materialized_return                          ✘ no executor parameter
       └─ receive_question              current.rs:685 ✘ CONSTRUCTS ITS OWN HOST POOL
       └─ materialize_returned_path_live current.rs:721 ✘ CONSTRUCTS ITS OWN HOST POOL
```

The law this violates is written in this repository, on the very method that stops:

> *"Condition through one caller-retained physical executor. The executor crosses every Swing event
> in this organ; **selecting a card at the outer language boundary cannot silently construct a
> private host executor here.**"* — `relational_language/ecology.rs:135-137`

Eleven sites construct a private `ParallelHostLiveCurrentExecutor` inside library code. Five are
lawful convenience wrappers that delegate to a `_with_executor` twin the caller may choose instead.
**Six are not, because no twin exists**: `morphological_language/current.rs:685,721` and
`causal_language.rs:528,682,819`. For those, a caller holding a mounted card has **no expressible way
to pass it**, so the card is not declined — it is unreachable.

---

## 4 · The generation frontier IS a front, and it is the one stage with no mouth

`MorphologicalLanguageEcology::generate_currents` (`ecology.rs:760-860`) is a breadth-first frontier:

```rust
loop {
    let mut successors = BTreeMap::new();
    for (current, population) in states {          // ← the co-present population at one instant
        for event in self.event_candidates(...)? { // ← each state forks per admitted event
            let mut successor = state.fork();
            self.enact_event(&charge, &mut successor, event, ...)?;
            insert_generation_state(&mut successors, successor)?;   // ← the join
        }
    }
    states = successors;
}
```

- `states: BTreeMap<MorphologicalCurrentState, MorphologicalCurrentPopulation>` is a **sparse
  frontier** — the representation the doctrine names for current (*"sparse frontier for current"*).
- Every expansion in one pass is **independent**: `enact_event` reads the immutable suffix ecologies
  (`longest_matched_sources`, `token_germs`, `mark_germs`) and writes only into its own forked state.
- `insert_generation_state` is the **join** — a merge into a map keyed on conduct class, which is the
  Nerode/Moore gluing the receipt counts as `conduct_equivalent_states_glued`.

**That is map-then-reduce over a front, exactly the geometry `enact` was built to receive** — and it
runs entirely on the host, on one thread, and takes no executor at any depth.

`generate` then materializes the outputs:

```rust
let outputs = generation.outputs.into_iter()
    .map(|current| current.into_materialized_return(prompt, action, worker_threads))
    .collect::<Result<Vec<_>, _>>()?;
```

Three plurality species live here and only one is serial by the physics:

| plurality | is it a front? | how it runs today |
|---|---|---|
| the frontier `states`, per instant | **yes** — co-present alternatives, independent expansion, order-independent-looking join | one host thread, no executor |
| `generation.outputs` — plural branches | **yes** — independent alternatives, no shared state | serial `.map()`, a fresh `LiveCurrentMachine` and a fresh private host pool each |
| one output's token chain, in `materialize_returned_path_live` | **no** — a genuine path, `(t_{k-1}, t_k)` bigrams | serial, and **correctly so** |

Note the third row: it *is* a chain, so its serialization is lawful and must stay. That is precisely
why "just parallelize the language body" would be wrong, and why the front/path distinction has to be
made before anything is built.

---

## 5 · The proof obligation, which is the whole reason not to wing this

The doctrine does not say *a front may be enacted wide*. It says **a front contains co-present local
events with PROVED INTERCHANGE**. The proof is missing here, and the code is honest about it:

> *"Administrative member order remains stable; **plurality here makes no claim of complete-successor
> commutation**."* — `ExactRelationalLanguageEcology::condition_copresent_with_workers`

And the frontier's join is `Vec::append`:

```rust
fn merge_witnesses(&mut self, mut other: Self) -> Result<(), _> {
    self.witnesses.append(&mut other.witnesses);   // associative, NOT commutative
    Ok(())
}
```

`witnesses: Vec<MorphologicalWitness>`, and the returned `outputs` are built by iterating those
vectors in place (`ecology.rs:885`). So **host arrival order is currently carried into the returned
plural branch population.** On one thread that is deterministic and therefore invisible.

This is the finding worth having, and it inverts the framing entirely:

> **Enacting the front on an apparatus is not a performance change. It is the SECOND FRAME.**

`CLAUDE.md` §0's fourth lesson: *"An invariant is only visible across two frames… Each returned
consistently until the frame moved. A machine with one frame cannot audit itself."* The generation
front has exactly one frame — single-threaded host arrival order — and under it, the question *is
witness order semantic?* has no answer. Run the same front on N lanes and require the returned output
**set** to be identical, and the question is decided:

- **identical** → arrival order was apparatus, `apparatus completion order never enters semantic
  lineage` holds, and wide enactment is admitted;
- **different** → host arrival order was load-bearing in the return, which is a contaminant by §0's
  fourth lesson **whether or not any card is ever mounted**.

Either outcome is a real return. That is why this is worth building carefully and why guessing at it
would waste the one thing it is actually good for.

---

## 6 · Where the time actually goes — what is measured, and what is not

An instrumented run of `eros_repository_language_agent` (phase clock added; measurements in one
frame, selecting nothing):

```text
[    0.1s] agent conditioned in 66 ms
[    0.1s] live deed emitted / world sections 6 / first answer
[    0.1s] second answer
[    0.3s] uncorrected control forked: 3 causes replayed in 0.1s
[    0.4s] revised answer
[    0.8s] detached remount answer
[    0.9s] first cultivation returned; active transductions 0
            ── then no further phase in 20+ minutes, 100 % of one core, card 0 % / 2 MiB ──
```

**Two corrections to what I said earlier this session:**

1. **The forks are not the cost.** I told Brandon the two counterfactual arms had roughly doubled the
   driver's runtime. Measured: **3 causes replayed in 0.1 s.** The replay-fork is cheap here and that
   claim was wrong.
2. **The stall is localized to the second cultivation question and no further.** The generation
   frontier is the known super-exponential organ — separately measured at 1 token 57 ms, 2 tokens
   403 ms, 4 tokens 55,098 ms, 8 tokens no return in 200 s — and is the prime suspect, but **this run
   did not measure that link.** Localizing it inside the second cultivation question is one more
   measurement and it is owed before any construction is chosen.

---

## 7 · What is owed, in order, and none of it is attempted here

1. **Localize the stall inside the second cultivation question.** Front expansion, codec
   transduction, or the relational think-fiber. Nothing should be built before this returns.
2. **Extend the seam.** `generate`, `generate_currents`, `into_materialized_return`,
   `materialize_returned_path_live` and `receive_question` need `_with_executor` twins, so a caller
   holding a card can pass it. This is the mechanical part and it is a *precondition*, not a fix —
   with the seam extended and a card mounted, the front is still enacted one member at a time.
3. **Decide the interchange question by measurement, not assertion.** Present the frontier pass as a
   population and require the returned output *set* to be invariant across lane counts. Report the
   separating witness if it is not.
4. **Only then** consider what a front launch would look like, in the doctrine's own elementary terms
   — sparse incidence over the state population — and never by lowering the host loop into one kernel.

**Explicitly not claimed:** that the front can be enacted wide; that the card would make this driver
fast; that witness order is or is not semantic. Each is a measurement nobody has taken.

**Also unchanged and worth stating:** `condition_with_executor` reaching CUDA is real and works —
`text_material_cuda` and `live_current_cuda` both drive the card, and
`eros_relampago_atmospheric_current` exercises the latter. The problem is not that the machine cannot
use its card. It is that **the one stage whose geometry most demands a front has no mouth to present
one through.**
