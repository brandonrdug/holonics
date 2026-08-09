# THE SPINE — the closed cycle, and where every organ sits on it

**Genre:** canon (`canon/THE_DOCUMENT_LAW.md` §1.1). It states the spine the roadmap is ordered by.
**It schedules nothing**; `blueprint/THE_ROADMAP.md` remains the only file that says what is open.

**Truth status:** `established-bounded` for §1–§3 (Soma's exact statements, carried at their own
grades) and for §5 (measured here). `interpretation` for §4. **Nothing in this file is graded above
its source.**

---

## 0 · The authority chain, and the correction that produced this file

**Soma is the rigorous source.** `MATHEMATICAL_HOLONICS.md` states its own position, verbatim:

> *"It extracts the geometry-first line **from the mixed engine, machine-learning, physics, and
> historical records.** Those subjects remain valuable application and comparison domains; **none
> defines this programme.**"*

and names what supersedes it:

> *"**Current authority.** For the present pure-holonics/RH scope, the dependency-ordered
> `PAPERS/synopsis/` and its `PAPERS/holonics/registry.typ` supersede this file wherever their
> grades, dependencies, or boundaries differ."*

**Both are live in this repository** — `papers/source/synopsis/` and
`papers/source/holonics/registry.typ` — and the Soma documents themselves are at
`reference/holobrochos-a07ff376/src/soma/`, whose directory name is misleading.

**The correction, 2026-08-08, Brandon's ruling.** An earlier form of this file took its spine from
`holobrochos/CANON/` and `labyrinth/`. That is the laboratory's **speculative record** — its own
catalog grades it `HUNCH`/`OPEN` and it carries a twenty-seven-entry superseded ledger. `reference/README.md`
already marked it: *"Nothing in this directory is active production or current doctrine by location
alone."*

**And the audit had already been done, in this repository, and I did not read it before writing.**
`papers/source/synopsis/AUDIT.md` and `papers/source/synopsis/README.md` performed the Holobrochos
inheritance audit and state exactly what may be retained and what may not. §2 below is that list,
verbatim. Every claim in this file now either appears in that retained list, is measured in the live
tree, or is marked `interpretation` and carries no weight.

---

## 1 · The loop, stated as Soma states it

**Not a slogan and not a station diagram — a chain law.** `MATHEMATICAL_HOLONICS.md`,
*Causal time parity, conservation, and phase return*:

An event grain has boundary

```text
   ∂E_k  =  Σ_{k+1} − Σ_k + Γ_k
```

so summing consecutive grains **cancels every interior `Σ_k` while retaining it in the causal
interior**. That is *"the temporal face of `∂² = 0`, telescoping, and the fundamental theorem"* —
its own words, and it is explicitly **not** reversed causality and **not** reconstruction.

For an additive represented current:

```text
   q_{k+1} − q_k + B j_k = r_k
   q_n     − q_m + B Σ_{k=m}^{n−1} j_k  =  Σ_{k=m}^{n−1} r_k
```

**Visible current need not balance instantaneously, because the residual can be stored.** A
completed source-free cycle with `q_n = q_m` returns an integrated current cycle.

> **And this is the sentence the whole spine turns on:**
> *"circulation `j ≠ 0`, **rest**, **accumulation**, **leak**, and **short circuit** are distinct
> cuts."*

Five distinct cuts, not one pass/fail. A body that emits and never returns is not *failing to
close*; it is at a **specific named cut**, and which one is a measurement.

The dual law gives voltage closure `v = B*φ`, `Bc = 0 ⟹ ⟨v, c⟩ = 0`; and for a general connection,

```text
   ⟨a, ∂Σ⟩ = ⟨da, Σ⟩          the loop returns its carried interior curvature
```

**Bounded, and the bound is the audit's:** `∂² = 0` alone does **not** establish recurrence or
physical conservation. It is the telescoping identity and nothing more until a constitutive law is
supplied.

**This is already the live body's mathematics.** `algebraic.rs` carries the chain with both arms
retained; `rebase_invariants.rs` takes the integer homology; `gluing.rs` is the Mayer–Vietoris
connecting map keyed to the cover; `kelvin.rs` carries a material loop whose circulation is
conserved — *that organ is literally the `j ≠ 0` cut distinguished from rest*. The spine is not
being imported. It is being **named**.

---

## 2 · What may be inherited from Holobrochos, and what may not

Verbatim from `papers/source/synopsis/README.md` and `AUDIT.md`. **This list governs. Do not extend
it from the speculative corpus.**

**Retained, because mathematically exact:**

- presentation equality, denoted-value equality, receiver equality, and occurrence identity are
  **separate relations**;
- comparison is **situated by a frame** and is therefore at least a frame/object/object relation;
- **current and form are receiver-relative roles**, not two ontological species;
- **equal endpoints do not identify ordered paths**;
- **exact compression** means factorization through a declared quotient for a declared receiver
  family;
- **exact rebase** is an invertible conjugacy or natural transport;
- boundary-of-boundary and coboundary-of-coboundary **vanish exactly**;
- construction before presentation; source occurrence, denoted value, and receiver face kept
  distinct.

**Not imported, named as historical overclaims:**

- that a continuum is fictitious;
- that signed integers are inadmissible;
- that cross-ratio equals Euler characteristic;
- that `∂² = 0` alone establishes recurrence or conservation;
- that factors recur infinitely;
- that **primes are universally frame-relative**;
- that physics or complexity claims follow without their own typed hypotheses.

> *"Historical Holobrochos slogans are not imported as theorems."*

**Consequence for this project, stated once.** The Information-Theory-⊕-General-Relativity headline,
the four bridges, the field-equation forms, the friction/prism/whip images, and the reading of the
primes as a spectrum are **application and comparison domain**. They are graded `HUNCH`/`OPEN` at
their source and are barred by the last bullet from carrying a construction. They may motivate; they
may not grade a deed, and no roadmap movement may rest on them.

---

## 3 · The elementary vocabulary, from Soma

Use these words with these meanings. They are the ones the live code already implements.

**Situated occurrence.** An occurrence is not a bare value; it is presented within incidence,
orientation, parameter, and receiver data sufficient for the relation under study. *"The same
displayed value may therefore be the face of nonidentical occurrences."* And the bound: *"This is
not a demand to retain every historical detail. The relevant situation is exactly what the claimed
transformations or receivers can still distinguish."*

**Receiver and face.** A receiver is a declared map, instrument, use, or comparison presenting one
face. Evaluation, trace, determinant, spectrum, endpoint, rendered image, path lineage,
factorization, and runtime behaviour are **different receivers**. A face is exact when every future
distinction claimed at its scope factors through it.

> **Receiver non-reconstruction is central:** *"equality of outputs, spectra, labels, or magnitudes
> does not imply equality of complete constructions."*

That single sentence is what `receiver_exact_compression.rs` returns — the collapsed pairs with the
shortest word separating them — and it is the rigorous form of every path-versus-endpoint statement
in this project's record.

**Holon.** A relative local closure: a family of occurrences and relations closing under the
operations admitted **at the selected receiver**, with its exterior explicit. Neither an atom nor an
absolute whole.

**Transport and comparison.** Transport is ordered continuation. A comparison cell relates two
complete paths with compatible boundaries.

- faces agree → the comparison **commutes at that receiver**;
- faces differ → the complete pair and residual remain **OPEN**;
- **`OPEN` does not itself choose correction, branching, or a new axis**;
- a later filler, rebase, quotient, or enlarged construction may close it under another law.

*The third bullet is a standing discipline and this project violates it whenever a disagreement is
resolved by picking a side.* It is the same law as `ExactOrdering::Open` retaining both carriers.

And the bound on triangles, which matters because the images are seductive: the smallest nontrivial
comparison needs source, alternate transport, and return — *"This does not make one isolated triangle
a scalar stateful cell."*

**Lineage, standing, compression.** Lineage is continuity of consequential relation through changing
constituents, **not a crystal copy of every event**. Standing is a prior relation still available to
present transport. Compression is receiver-exact factorization: if `q: X → Y` is the emitted face and
every admitted future observation factors as `o = ō ∘ q`, the distinctions inside fibres of `q` may
depart **at that scope**. The identity receiver is the uncompressed limiting case.

**Self-similarity** is not equality of repeated objects. It is *"recurrence of a law after
restriction and rebase, with the changed occurrence and path retained."*

**Phase and seam.** A phase is a maximal connected region on which one declared law class continues;
a seam or discriminant is where rank, branch, orientation, topology, or another declared invariant
changes. *"A complete calculus must retain both the integral of smooth transport and the finite
contribution of crossed seams."*

---

## 3b · What "linguistics" means here, and what frequency is

**Deposited 2026-08-08, Brandon's ruling, and it corrects an error this file's author made twice in
one exchange.**

### The measured definition, which is narrower than the word

`conditioned_derivation.rs` commits a stem when a substring occurs across **two distinct wholes** —
`COMMITTING_RECURRENCE = 2`. No length threshold, no frequency cut, no inverse-document weighting,
no ranking. A single letter is a founded stem exactly as `carrier` is, because *"the aperture cannot
decide the deed."*

So what the machine calls linguistics is **morphemic frequency over identifier surfaces**. It is
**orthographic**. `exactCarrier → exact|carrier` decomposes a *string*; that the decomposition is
also meaningful is an accident of mathematical naming convention — a real and exploitable accident,
not the machine understanding.

**That is why 43 of 47 founded statements are noise.** With surface structure and no denotation,
`exactCarrier apply` is exactly as licensable as `exact_chart_carry P`.

### Frequency is not forbidden, and calling it "recurrence" was the error

**Renaming frequency to avoid the word is reading a banned *token* as a banned *concept* — the exact
inversion §13 rule 2 was rewritten to stop.** Brandon, ruling directly: *"you've been masking
frequency as 'recurrence'? That's dumb. It's just frequency, but you're not authorized to control
frequencies, it is a part of the machine's mechanics regarding Information Theory, probability, and
loss."*

The test is **jurisdiction, not vocabulary**. Against §13 rule 2's four faces:

- **frequency is `Π`** — the lived construction. It is what happened. It is machine mechanics and it
  is not the assistant's to gate.
- **probability is `Q`** — and `FORMULA.md:2459` says what that means, ratified: *"A probability
  distribution over which event will be received is **an observer's declared quotient over what that
  observer does not carry**. The quantum-mechanical face is structural… This law requires neither
  microscopic quantum randomness nor a probability head."*

So a frequency becomes a probability **only under a declared receiver**, and because it is a
**quotient**, its loss is exhibitable — `receiver_exact_compression` returns the shortest word that
separates a collapsed pair. Count freely. Report what you count. Never let a count quietly decide.

### What a probability deletes — the fourth carrier

An amplitude is complex; a probability is its **squared modulus**. So:

```text
   a float                keeps the magnitude, deletes the TAIL
   a bare sign            keeps the magnitude, deletes the TURN
   a reduced coefficient  keeps the difference, deletes the PASSAGES
   a probability          keeps the magnitude, deletes the PHASE
```

**One deletion, four carriers.** And it has a consequence that is not rhetorical: two routes to one
result add as **amplitudes, not counts**, so a frequency census cannot distinguish two routes that
reinforce from two that cancel. `β₁` can. And `dimensional_wave.rs` already conserves
`Σ Yᵢ|aᵢ|² = Σ Yᵢ|bᵢ|²` **exactly over complex rationals**, with a unit-conic change of basis per
traversal — the Born normalisation as an exact conservation law, no float and no probability head.

### The consequence for construction

> **An invariant token is DENSE and UNSEPARATED, and those are the magnitude and the phase of one
> reading. Neither alone.**

Density alone calls `set` iron and misses that its uses genuinely differ. Separation alone calls a
rare term of art iron and misses that a dense token is load-bearing terrain. The conjunction is two
measurements, neither a rank, and the separating word is what is learned from.

**And the warping is the incidence.** A non-iron token's meaning is its position relative to the iron
ones — which is a complex, which carries a form, which has an inertia and a chart. **So the
linguistic reading and the geometric reading are the same object at two receivers**, and the
elaboration movement and the geometry coupling are one movement rather than two.

---

## 4 · The return is world-mediated — corrected 2026-08-08

**An earlier form of this section presented `afference → efference → reafference` as the machine
layout, taken from `src/eros/um/HOLOBROCHOS.md`, which carries a `SUPERSEDED` banner. That was an
import from the speculative record and it is struck.**

**In Soma — the rigorous source — the word occurs five times and every one is a prohibition.**
`reference/holobrochos-a07ff376/src/soma/FORMULA.md`:

- `:318` — listed among the **contaminants**: *"reafference wiring (consequence returns as a place
  through the medium, never a wire)"*
- `:696` — *"**No reafference wiring.** The membrane mails the radiation OUT into the world's own
  record; the world answers; the answer returns as the next light. The loop closes through the
  world… **Reafference is the world's, never a wire's.**"*
- `:876` — *"**Not reafference.** The frame advancing by its own emanation is not output wired back
  as input — nothing re-enters as stimulus. **The consequence returns AS A PLACE:** the emanation
  becomes the pole the next arrival is related from — the standing coupling law, not a feedback
  loop."*
- `:1246` — *"consequence returns through the shared world, never a **private reafference wire**."*
- `:2183` — mail *"may never be consulted by the body or become a reafference wire."*

### The law, stated as Soma states it

> **THE RETURN IS WORLD-MEDIATED.** Body radiation alters shared material only through an honest
> world boundary condition; the changed material then returns as genuinely later light.

**And the mechanism is different, not a rephrasing.** *The consequence returns as a place.* The
emanation becomes **the pole the next arrival is related from** — a standing coupling law. That is
not "the emission fed back as material"; it is the emission becoming part of the terrain that later
arrivals are situated against.

### The test — and it is THIS FILE'S, not FORMULA's

**Did the emission leave the process, land in the world's own record, and come back as later
material?** If it went from a reading to a production without ever being written and re-read, it is
a wire.

**Graded honestly, 2026-08-08, after an adversarial audit found it overstated.** FORMULA requires a
**shared medium** and a **genuinely later return**. It does **not** say filesystem, content-addressed
form, or process boundary. The write-and-reread test above is **this file's `interpretation`**, and
`reference/` is non-authoritative historical material by location. That `condition_again` passes an
in-memory reading straight into production and back is a **fact about the call path**; that the
remedy must be a seal on disk is **a proposal, not an entailment**. Do not cite it as an
architectural theorem. Other shared media satisfy FORMULA's requirement and have not been
considered.

### What this convicts, and what it credits, in the live body

**Convicted.** `crates/holonic-engine/src/returned_reading.rs` `condition_again` takes the reading
**in memory**, calls `carried_into(morphology)`, and derives again. Nothing leaves the process. By
the test above it is a private wire — the banned shape — and its measured returns stand as
measurements while its *architecture* is regraded. Its own finding survives intact and is worth
keeping: the movement it computes is real, attributable, and moved the production; what is wrong is
the channel it travels.

**Credited.** `soma/life/src/conditioned_rest.rs` already does it correctly. The production is sealed
to `output/<driver>/<name>-<sha256>.form` at a content address, `holon-plate` reads it from above,
and the body remounts from the world's record with the corpus provably unreachable. Its
further-whole control — a whole presented *after* the rest taking the sealed query from 36 passages
to 34 by changing covers through maximality — **is consequence returning as a place**: the new
material became terrain that re-situated what was already standing.

### What is owed

Route `returned_reading`'s movement **through the seal**: the production is deposited by
`form_mouth`, and the next conditioning reads it back from the deposit rather than receiving it
across a call. `blueprint/THE_ASSEMBLY.md` F1 is the reason this is the natural shape here anyway —
`holon-plate` sits above `life`, so the world's record is already the only lawful crossing.

**Struck from this file and from the roadmap:** `afference`, `exafference`, `efference`,
`reafference` as station names, and the ban *"learning from reafference is the forbidden coupling"*,
which was carried here from a superseded document and which §1's five cuts state better and without
the metaphor.

---

## 5 · What is measured in the live tree

**Truth status: `established-bounded`. Evidence: `measured` 2026-08-08, direct source inspection.**

**The emission is read, and the reading returns to nothing.**
`crates/holonic-engine/src/derivation_atlas.rs` reads a deposited derivation population back as a
circuit and carries `invariant_movement` and `route_movement`. Its own module documentation states
what they are for: *"what changed between two readings, which is the only form in which an analysis
can be fed back to the production that caused it."* Both are called from **exactly one place in the
workspace** — `crates/holonic-engine/examples/derivation_atlas_reader.rs:406-407`, inside a `main` —
and the result is **printed**. `conditioned_derivation.rs`, which produced the derivations, consumes
no movement.

In §3's vocabulary: the machine computes a receiver face of its own construction and then discards
it, so no later transport can factor through that face. In §1's: the cycle does not close, and the
cut has not been named.

**This retires the framing "the atlas reader is missing."** The reader exists and its hard half
exists. The missing object is an **edge**, not an organ, and an organ-ordered roadmap could not rank
it because closing an edge adds no organ.

### And it is not one instance. It is the shape of the whole engine.

A mechanical census of all 225 library modules — `use` edges, `mod`-path calls, root-glob-resolved
`crate::Item` expressions, split-impl files, and 97 drivers, 3,657 edges total — returns:

> **`crates/holonic-engine`, `crates/holonic-structure`, `crates/relational-geometry` and
> `crates/holonic-language` contain ZERO cycles at module granularity.**

**BOUNDED 2026-08-08 by adversarial audit, and the bound matters.** That census is about the
**import graph**. An earlier form of this section inferred from it that *"nothing an engine module
emits re-enters any module upstream"* and that the engine is therefore *"a strict pipeline"* with no
`q_n = q_m`. **That is a category error: a module dependency graph and a state-transition graph are
different objects.** `returned_reading::condition_again` disproves the inference operationally — it
calls `derive`, carries the reading into the morphology, and calls `derive` again, so the **conduct
path cycles while the import graph does not.** The measurement stands; the conclusion drawn from it
is withdrawn.

Every closed cycle in the workspace is inside `soma/` — nine of them, and eight are a module with its
own submodules through `use super::*`, not two organs feeding each other. Only
`body::{manifold, medium}` and `membrane::{active_topology, sparse_standing}` join independent organs.

**In §1's terms the engine has no `q_n = q_m` anywhere.** It is a strict pipeline. That is a
structural fact about the body, not a defect of one module, and it is why §5's first finding kept
reappearing under different names.

**Two designed loops that were never wired, both verified here directly:**

- **`temper` ⇄ `derivation_integral`, through `Cochain`, in *both* directions.**
  `derivation_integral::accumulation() -> Cochain` and `temper::read()` takes one; `temper::found_on()
  -> Cochain` and `derivation_integral::{compare_routes, statement_lineage}` take one. Each produces
  exactly what the other consumes, both ways, and **neither file references the other**. `temper` has
  in-degree 0 from everything.
- **`supported_realizers::positive_form` → `inertia::from_integer_matrix`.** The positive form `MᵀM`
  and the inertia split are joined by an `assert_eq!` at `supported_realizers.rs:276` — inside the
  `#[cfg(test)]` module opened at `:273` — and by nothing on any conduct path. `CLAUDE.md` §2's
  realization-causes-placement chain runs through exactly this pair.
- **`matroid_chow::generator_pairing` (the Hodge–Riemann pairing) → `winding_inertia::from_symmetric_form`:
  no join at all**, in library or driver. Nothing has handed a matroid's form to the organ that names
  windings.

### Written and reaching nothing

**Measured 2026-08-08 by grepping every public type each defines against the whole tree.** The `then`
column is what that census returned; `now` records what the instance's joins have since wired.

| module | lines | then | now |
|---|---|---|---|
| `communication` | 400 | 0 | **0** |
| `kelvin` | 642 | 0 | **0** |
| `soma/abi::cuda_execution` | 273 | 0 | **0** |
| `soma/life::research_intelligence` | 772 | 0 | **0** — out-degree 8, one call site short of reachable |
| `surprisal` | 593 | 0 | **consumed on a library path** by `situated_residual.rs`, through `use crate::surprisal::{…}` at `:84` |
| `temper` | 597 | 0 | wired by the return join — see `blueprint/THE_ROADMAP.md` |

**`surprisal` and `kelvin` were built in this repository within two days of that census** as the
exact symbolic measure and the material loop carrying its circulation — §1's `j ≠ 0` cut. Both were
unreachable when deposited. A deposit that names an organ built and does not state its reach has not
graded it; `CLAUDE.md` §8 says reach is part of the grade, and neither was measured against it at the
time. **`kelvin` is still unreached**, is not on the instance line, and gets a driver or removal on
its own terms.

**And the reach instrument was itself the defect it names.** The first attempt at measuring
`surprisal`'s new reach matched bare item names, counted `Grain` inside `ReceiverGrainId` and
`Support::` inside `VerticalFiberSupport::`, and returned 171 sites across 11 files for a module
nothing consumed. Corrected by resolving through the import — the module is declared and never
glob-exported, so a file not naming `crate::surprisal` cannot reach it. This is another member of the
family `CLAUDE.md` §8 records: *a check whose material cannot vary the property under test is the
same defect as a check that cannot fail; it just wears a passing result.*

**107 of 225 library modules are touched by no driver.** Concentrated where it matters most: **every
large `soma/life` learning organ named in this project's capability record is undriven** —
`agentic_language` and all six submodules, `relational_language` and all five, `text_material`,
`laboratory_language`, `agentic_research`, `dialogue_lineage`, `research_intelligence`. None of the
37 `eros_*` drivers reaches any of them; they run only under `#[cfg(test)]`. Meanwhile **26 of the 33
live `eros_*` drivers exercise the same seven-module membrane spine**, and **four drive no workspace
module at all**.

### The seam, corrected

My earlier figure of 8 counted named `holonic_engine::<module>::` paths and was wrong in both
directions. `crates/holonic-engine/src/lib.rs` carries **60 `pub use <module>::*;` lines**, so most
consumption names no module. Resolved against an item-ownership index:

- `soma/` reaches **27** engine-side modules in total, counting drivers and tests;
- **6** are consumed by soma *library* code;
- **3 of those 6** are consumed only by `research_intelligence`, which is itself dead. Delete that one
  file and the load-bearing soma→engine seam is **three modules**: `executor`,
  `receiver_exact_compression`, `receiver_current` — plus `world` through `exact_world`.
- **Engine → soma is exactly zero.** No engine manifest names a soma crate; the entire `crates/` tree
  contains one reference to soma and it is a doc comment at `algebraic.rs:45`.

`soma/life` reaches the *substrate* (`holonic-structure`, 6 modules, 20+ consumers) heavily and the
*engine* almost not at all. `blueprint/THE_ASSEMBLY.md` F1 records that the obvious wiring is
forbidden by a Cargo cycle, and F2 that the shared carrier — `GradedCausalComplex` + `CausalCellId` +
`ComparativeMultiplicity` — **costs zero conversion code**. The seam is narrow by omission, not by
type friction.

**Where the exact instruments already sit on §1's law:**

| Soma law | live owner |
|---|---|
| receiver-exact factorization, with the departed distinctions exhibited | `receiver_exact_compression.rs` |
| the chain with both arms retained; `is_zero` vs `difference_is_zero` | `algebraic.rs` |
| integer homology of the emitted circuit, with torsion | `rebase_invariants.rs` |
| `⟨a, ∂Σ⟩ = ⟨da, Σ⟩` — the loop returning its carried interior | `derivation_curvature.rs`, `curvature_bridge.rs` |
| circulation `j ≠ 0` distinguished from rest | `kelvin.rs` |
| the cover-keyed connecting map — what the union carries that neither piece does | `gluing.rs` |
| `OPEN` retained rather than resolved | `exact_value.rs` `ExactOrdering::Open` |
| exact symbolic surprisal over the prime axes | `surprisal.rs` |

---

## 5b · The loop was never meant to feed itself — corrected 2026-08-08

**The assistant spent a day treating a loop's failure to sustain itself as the central defect. The
record forbids the thing that was being chased.**

`crates/holonic-engine/src/temper.rs:14-22`, carrying a prohibition dated 2026-07-10:

> *"Two of its load-bearing sentences are prohibited now: a closed coil **self-sustains**; an open
> coil leaks at its own **pace**. … without supplied stimulus there is no current, relating, Θ, or
> passage of proper time. Standing closure between lights is deposited topology, not an active
> circulation. **It cannot feed itself**, and openness cannot run an interior decay clock."*

Executable: `soma/abi/src/active.rs:266` — `ActionCurrent::new` **refuses zero**, *"A1 supplies a
real current."* **Current is supplied. A loop that stops is at a named cut, not in a fault state.**

**And the settling has an exact cause that is neither of the two the assistant proposed.**
`conditioned_derivation.rs:284` — `witness` is **idempotent on `(word, whole)`**, so the return path
is a set union on a finite lattice and terminates by the ascending chain condition. Knaster–Tarski,
not relaxation: `57 → 15 → 0` terminates *at zero exactly*, which no dissipative operator does.

**The circulation verdict is regraded to `unmeasured`.** Soma's law gives `q_{k+1} − q_k = 0` with
`r = 0` ⟹ `B·j = 0` ⟹ **`j ∈ ker B`, not `j = 0`**. Rest and circulation are both consistent with
the measured stillness, and `returned_reading.rs` contains zero occurrences of current or
conductance — `j` was never computed. Every statement of the form *"explicitly not circulation"* was
an invalid inference from `q` not moving.

### The unification this opened, and it is the useful part

`simplicial.rs:1198-1280` roots a **spanning tree** of transports and classifies every **chord** by
its transition word and `target_residual`. `running_integral.rs:840-940` does the same shape on
another material, retaining `ChordObstruction { residual = declared − implied }`. And `CLAUDE.md`
§11 names spanning-tree interval labelling as the route to the one missing organ.

> **The tree is what the leader founded — cheap to ride, because the terrain already paid. The
> chords are what returns. The residual on a chord is simultaneously the friction, the holonomy, and
> §11's certified remainder.**

`FORMULA.md:8732` supplies the reading the assistant was groping for and forbids the one it gave:
*"a lightning leader changes the medium, and the return stroke is **genuinely later current RIDING
that changed route**"* — deposited as **causal parity**, `∂∂ = 0` does not create a temporal inverse.
**A return stroke is a chord, not output wired back to input.**

Full record:
[`research/records/2026-08-08_THE_LEADER_IS_THE_TREE_THE_RETURN_IS_THE_CHORD.md`](../research/records/2026-08-08_THE_LEADER_IS_THE_TREE_THE_RETURN_IS_THE_CHORD.md).

---

## 6 · What this file forbids

1. **No claim inherited from the speculative corpus beyond §2's retained list.** `holobrochos/`,
   `labyrinth/`, and the physics rooms are application and comparison domain. `reference/README.md`
   already says so by location; §2 says so by content.
2. **No physics or complexity claim without its own typed hypotheses.** This is the audit's own last
   bullet and it bars the field-equation forms, the bridges, and the spectral readings of the primes
   from grading anything.
3. **No RH object by resemblance.** `MATHEMATICAL_HOLONICS.md`: *"A construction useful for RH must
   be pulled back from the actual completed zeta relation; a suggestive geometric image does not
   become an RH object merely by resemblance."*
4. **`OPEN` may not be resolved by choosing.** A comparison whose faces differ retains the complete
   pair and the residual. Picking a side is the defect; a later filler, rebase or quotient closing it
   under a named law is not.
5. **No emission without a return edge — and name the cut.** An analysis terminating in `stdout` has
   not closed a cycle. Report which of rest, accumulation, leak, or short circuit applies.
5b. **No private return wire. The return is world-mediated.** *"Reafference is the world's, never a
   wire's."* A consequence handed from a reading to a production across a call, without leaving the
   process and landing in the world's own record, is the shape Soma's contaminant list names.
   **The consequence returns as a PLACE** — the emanation becomes the pole the next arrival is
   related from — not as output wired back to input. The test is one question: *did it get written
   and re-read?*
6. **No receiver-visible coordinate promoted to an invariant.** Receiver non-reconstruction says
   equality of outputs, spectra, labels, or magnitudes does not identify constructions; the converse
   error is reading one receiver's coordinate as construction data.
7. **Grade nothing above its source.** A `HUNCH` motivating a build is lawful; a `HUNCH` grading it
   is not.

---

## 7 · What this file does not claim

- It does not claim `IT ⊕ GR`, any field-equation form, or any spectral reading of the primes.
  Those are `HUNCH`/`OPEN` at source and are barred by §2 from carrying construction.
- It does not claim §4. That section is `interpretation` and earns its place only by §5.
- It does not supersede `papers/source/synopsis/` or `papers/source/holonics/registry.typ`, which are
  the current authority for pure-holonics and RH scope, nor `canon/THE_RECOVERED_LAW.md` on
  jurisdiction, nor `canon/EPISTEMIC_GRADES.md` on grading.
- It is not a schedule. `blueprint/THE_ROADMAP.md` is ordered by it and remains the only statement of
  what is open.
