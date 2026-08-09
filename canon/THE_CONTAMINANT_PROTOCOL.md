# The contaminant protocol

**Genre:** canon (`canon/THE_DOCUMENT_LAW.md` §1.2). It names a family of contaminant species, gives
each the condition that identifies it and a verified instance in this tree, and states the procedure
a reader follows by hand before depositing.

**Truth status:** `project-postulate` for the procedure. `established-bounded` for every instance
below, each a direct source read at the `file:line` given, re-verified by the depositing session.

**Provenance:** Brandon, 2026-08-09, on being handed a script where a procedure was asked for:
*"I don't know what you're talking about with the census, you're overcomplicating it when my request
you to formally recognize and document the contaminants we've identified was very clear. 'it sees x,
it does not see y' and 'found by hand' do not make sense semantically, you're using weird avoidant
logic based in a census script I did not even ask you to make. **I used the word 'protocol'.** The pin
overcomplication is unnecessary as well; you don't need a script to tell you about inappropriate
coding conventions where you've hard-coded magic numbers."* And on how a failure is carried:
*"failures and mistakes are merely signals in our ontology."*

---

## 1. Two laws

> **1. A defect is identified by its condition, never by what found it.** How a defect was detected
> is not a property of the defect and never bounds a finding. *"The instrument does not see this
> class"* is a statement about the instrument; it licenses nothing and excuses nothing. A hard-coded
> magic number in a library organ is a bad coding convention and recognising one takes reading.

> **2. An instance found alone is a species not yet named.** When a defect is found, the obligation
> is not to fix it — it is to state the condition that identifies it and enumerate its population in
> the same deposit. A fix without an enumeration guarantees the next instance is found serially, and
> each serial find generates a sentence about the next one down.

Both exist because their negations were run. The first produced a census script offered in place of
the procedure that was asked for, and then used the script's blind spots as grounds for hedging. The
second produced the pinned-constant search: `characteristic_delay: 1`
(`soma/life/src/relational_language/ecology.rs:626`, `:639`), then `LEADER_WITNESS_DEPTH: usize = 1`
(`crates/holonic-engine/src/derivation_integral.rs:135`), then `REFINEMENT_APERTURE: usize = 64`
(`crates/holonic-engine/src/winding_inertia.rs:129`) — three weeks, one at a time, each reported as
though it were the last.

This is read by a person before a deposit. It has no gate and fails no build.

## 2. The species

### 2.1 The unconsumed return

**Condition.** A library organ computes a value and no other library organ reads it. Every call site
is a test body, an `examples/` driver, or a doc comment. The composition it is described as
completing does not exist; what exists is a formula with a passing test.

**Verified instance.** `crates/holonic-engine/src/founded_receiver.rs:238` —
`pub fn capacities(&self) -> BTreeMap<ReceiverId, BigUint>`. Its only call sites are
`crates/holonic-engine/examples/the_receiver_is_founded_at_the_junction.rs:298` and `:483`, and one
test at `founded_receiver.rs:924`. It was deposited as closing

```text
residue -> capacity -> service_rounds -> delay -> what conducts -> residue
```

of which **one arrow exists**. `founded_receiver.rs:221` names `receiver_current`'s law in a doc
comment and the file contains no other reference to `receiver_current`: **the consumer is prose.**

**Two prior instances the same session, both reported by the author before the third was committed.**
`derivation_atlas::invariant_movement` (`derivation_atlas.rs:945`) reached only from
`examples/derivation_atlas_reader.rs` and tests; `temper` named in the roadmap as *"wired by the
return join"* with a `temper::read()` that does not exist. Both now have library consumers —
`crates/holonic-engine/src/returned_reading.rs:134` and `:540`. `capacities()` does not.

**Corrective form.** Name the consumer by `file:line` in the deposit, or state that the return is
unconsumed and grade accordingly. A doc comment naming another module is not an edge. **"Closes the
loop" requires one `file:line` per arrow.**

### 2.2 The unfailable control

**Condition.** A declared control whose orbit over the declared material is trivial — no
configuration of that material could have made it fail. It passes, it looks rigorous, it carries no
evidence. `CLAUDE.md` §8 already convicts this as *"a gauge whose group acts trivially on the
declared material is not a gauge"*; the species here is that convicting it in prose did not stop it
being built four more times.

**Four verified instances, one driver, one day** — all in
`crates/holonic-engine/examples/the_development_declares_its_own_chain.rs`.

| control | why it could not fail |
|---|---|
| the null, control 8 | zero declared names land in `tactics` or `local_bindings` across all 66 declarations, so the edge equality it asserts was structurally immune |
| the sub-illicium control | its predicate was satisfied by a single `obtain ⟨a, b⟩` — two names founded simultaneously by one tactic on one line, reported as a completion arriving one grain up |
| control 1, `:96` | `const DECLARATIONS/EDGES/THREE_LINK` set **after** measuring, compared against the measurement that set them |
| the "independent" second scanner | it imports `holonic_engine::derivation_atlas::DECLARATION_FORMERS`, the vocabulary under test. Two readers of one shared list agreeing is one computation compared with itself twice |

**Corrective form, and its boundary.** A control returns its **orbit** over the declared material and
refuses itself as evidence when the orbit is trivial. The driver now does the first half — the label
reads `SNAPSHOT: orbit trivial` when the orbit is zero — and the snapshot still counts toward the
control tally. **Declaring a trivial orbit is not yet refusing it, and closing that is owed.**

The stronger form this project already owns: a control should exhibit its **distinguishing word** —
the shortest input separating the two things it claims to separate — which is what
`crates/holonic-engine/src/receiver_exact_compression.rs` returns per collapsed pair. Absent one, the
control has not gauged anything.

A snapshot is lawful and useful. It is not a null, and the deposit must say which it is.

### 2.3 The unreconciled figure

**Condition.** A figure is deposited from one route. No second route was run, or one was run and the
disagreement was narrated away rather than named.

**Verified instances, all in work committed before they were caught.** Internal arrivals deposited as
**29**, actual **5** — 22 names founded simultaneously by one destructuring pattern, 2 cross-focus
leaks keyed on `rfl`. Depth chains deposited as **7**, actual **1**, then **3** after the cohort and
focus stacks were built. Declared edges deposited as **80**; a second reading found **81**, and the
printed reconciliation called the 81st a projection *"to another namespace"* when it is the same
namespace — the reconciliation text was false, and the honest return is **80 asserted plus 5 `OPEN`
projections**. And a record contradicted itself in adjacent paragraphs: *"the walk does not rebase"*
then *"those are two frames"* — if it never rebases there is one frame.

**Corrective form.** Every deposited figure carries the route that produced it. Where two routes
exist both figures appear and the disagreement is named as a finding. **A reconciliation is itself a
claim about the material and is checked before it is written.** A record's sections are read against
each other before deposit; an internal contradiction is a figure disagreeing with itself.

### 2.4 The grade above source

**Condition.** A claim is cited at a grade its source does not carry, or a grade is attributed to
Brandon for something he did not ratify. The source is one `grep` away and was not opened.

**Two verified instances, one day.** `reference/holobrochos-a07ff376/src/soma/FORMULA.md` §XVIII was
cited as *"ratified"*. Its header reads `derived, presented for stone`; §XVII, four lines earlier,
reads `RATIFIED`. **The file distinguishes the two explicitly and the distinction was one line
away.** Two elisions in the same quotation made it say the opposite of its paragraph. The second
reached a commit: `blueprint/THE_ROADMAP.md` carried *"Ratified by Brandon"* for a **reading**, when
what he approved was an **order of work**. Introduced at `d734a02`, removed at `b3f8e4e`.

**Corrective form.** Open the line that carries the grade and copy the token verbatim. A ratification
names *what* was ratified: an order of work is not a reading, and the deposit says so in those words.
**When quoting a permission, quote the condition attached to it** — `FORMULA.md` §CXXVI's clause 3
survived a cited permission intact: *"no tokenizer … enters Soma as a primitive without an
independent live-lifecycle derivation and demonstrated need."*

### 2.5 The authored level

**Condition.** A numeric bound inside a library organ decides how far a construction goes, how much
it admits, how deep it looks, or how many it returns — and nothing derives it.

> **A level is either read off the material or declared by the caller. It is never authored inside
> the organ.**

The full statement and the enumerated population are `canon/THE_AUTHORED_LEVEL.md`.

**Verified instances.** `token_invariance.rs:180` — `SEPARATION_EXHIBIT: usize = 512`, truncating a
**returned population**, which `CLAUDE.md` §9 forbids outright: the artifact is the return and a
count is never a substitute. `token_invariance.rs:175` — `WINDOW_APERTURE: usize = 64`, which
truncates the population *presented to* the compression organ, so `iron_at` on a busy surface is
measured on a subsample. `derivation_integral.rs:135` — `LEADER_WITNESS_DEPTH: usize = 1`; **a leader
whose witness depth is one takes a single step.** `codec_recovery.rs:111` — `FREE_ENTRY_APERTURE: u64
= 12`, whose refusal shape (`GaugeApertureExceeded` rather than sampling) is lawful and whose value
nothing derives. `rational_polynomial.rs:643` — `MAXIMUM_ISOLATION_DEPTH: u32 = 200`, where the root
separation is computable from the discriminant. `prime_ecology.rs:44` —
`DEFAULT_HORN_LOCAL_SECTION_LIMIT`, which names the defect in its own prefix: **a default is a level
the organ picked because the caller was never asked.**

**The excuse this species generates, named so it is not re-run.** *"A declared aperture that returns
its outside"* was offered as a third category beside facts and pins. **Refusing past a number you
invented does not make the number derived.**

**Corrective form.** Read the level off the material, or move it to the caller as a receiver-declared
parameter whose refusal names what the material would have required. Where neither is done, it stays
a held contaminant — **a level is a pin until someone shows it is a theorem, never the reverse.**

### 2.6 The restriction named as a definition — and why this one is not hygiene

**Condition.** A constant, type, or name presents a *restriction the organ imposes* as though it were
a *fact about the subject*. The name defeats the check: a reader who accepts the name never asks what
derives the number.

**This is the highest-value species in the list and it was misfiled as naming hygiene for weeks.**
Brandon, 2026-08-09: *"I believe there's a longer standing misinterpretation of my obsession with
FLT, polynomials, quadratics, quintics, and higher degree figures. Algebraic geometry, self-similar
scaling, fractals, stellation … I'm just talking about math transport mechanisms, **every degree is
relevant, the machine grows, there's no floor or ceiling to this, it's simplicial emergent
complexity.** … Why is it not obvious to you why we'd want the machine to solve arbitrary geometry
and polynomials in varying charts?"*

**A degree is a rung, not a category, and the ladder is the mechanism.** The objective sentence is
*"transport mechanisms between arbitrary charts"*; a polynomial of degree `n` presented in a chart is
the most concrete instance of an object in a chart, and every classical solving technique is degree
transport. Depressing kills the sub-leading term. A quartic's resolvent **is a cubic** — the transport
lands one rung down. Bring–Jerrard is a chart change that returns or names its obstruction. `A₅`
simple says something only *relative to* degrees 2–4, where it is false. Stellation is the same
figure at varying `{n/k}`. FLT is the same equation with `n` varying. Fractal scaling puts the rung
between the integers.

So §4's four slots are filled exactly by this organ, and by nothing else in the tree as cleanly:

```text
source geometry  ->  receiver map     ->  transport      ->  returned residual
a polynomial f       which coefficients   a Tschirnhaus      the auxiliary's rational-root
                     the chart kills      transform g        census, or the Galois obstruction
```

**Verified instances.** `arithmetic_monodromy.rs:38` — `const QUINTIC_DEGREE: usize = 5`. `:77`
refuses any polynomial whose coefficient count is not six; `:1109` declares
`type Permutation5 = [u8; QUINTIC_DEGREE]` with six further fixed-size-5 sites. The organ cannot see
a quartic. **The restriction deletes the mechanism the organ exists to demonstrate:**
`solvable_by_radicals` refusing at degree 5 is meaningful only against the degrees where it does not
refuse, so an organ that only ever sees degree five **cannot state its own theorem.** Alongside it,
`quintic_chart.rs:118` pins the same 5 through the whole Tschirnhaus tower.

`field_atlas.rs:23` — `QUADRIC_COEFFICIENT_COUNT: usize = 10`. A quadric in `n` variables has
`C(n+2,2)` coefficients, so **10 pins the ambient dimension at 3** while the name reads as a count.
`:24` — `AFFINE_PHASE_COEFFICIENT_COUNT: usize = 4` is `n+1` at `n = 3`. `ExactAffineVersionFiber::new`
already **takes the count as a parameter** (`:972`), so the machinery is dimension-agnostic and only
the caller pins it. The module's own first line reads *"The atlas has no authored population
ceiling"* — and then authors the ambient dimension in two `const`s.

**The cost law the ladder makes visible, which the pinned organ cannot state.** `quintic_chart.rs`'s
header already contains the general theorem at one rung: *"Three homogeneous conditions in `P^2` meet
in six points by Bezout, which is also why the classical Bring reduction costs a square root and a
cube root: six is `2 * 3`."* Generally: a Tschirnhaus transform of degree `k` killing the top `k`
coefficients has `p_1 = 0` solve linearly for `c_0`, leaving `k-1` conditions of degrees `2..k` in
`P^{k-1}`, so the Bézout number is

```text
   2 · 3 · … · k  =  k!          radicals of degree at most k
```

`k = 2` gives 2 (principal form, one square root); `k = 3` gives 6 (Bring, a square and a cube root).
**The ladder has a structural feature at `k = 5` that is not authored** — it is the same obstruction
one rung up — and an organ pinned at one rung can neither exhibit nor test that. Truth status
`derived`; checkable by the organ itself at `k = 2, 3` today and at higher `k` once it climbs.

**Corrective form.** Ask what the name asserts and what the code enforces. Where they differ, **the
code governs and the name is the defect.** Then excise by reading the quantity off the material —
not by renaming.

### 2.7 The metaphor over a defined object

**Condition.** A physical or biological picture is used as the *name* of an object that already has
an exact definition, or that would have one if written down. The metaphor then licenses reasoning the
definition does not support, and the licence is invisible because the picture is vivid.

**Verified instances.** "Silt" was deposited across code, canon and records for the quantity
measuring what a founded axis separates that nothing else separates. Brandon: *"please don't refer to
it as silt or like it is a mystical physical process, there is a mathematically pure way of
discussing the subject, I think you've also called this 'residue' in the past; it's just geometry and
higher dimensional mathematics, please don't overcomplicate it."* The object is a **residue
quotient**:

```text
  Res(r) = ( ⋂_{s ≠ r} ≡_s )  ∖  ≡_r
  Res(r) = ∅   ⟺   removing r leaves the partition unmoved   ⟺   r is redundant in the family
```

recomputed directly at `founded_receiver.rs:896` rather than trusted from an accumulator. Every
occurrence of "silt" is struck from the live tree.

The second is **"walk"**. Brandon: *"that's a graph traversal term that carries baggage with it."* A
walk presupposes a vertex set standing before the traversal, a visitor that does not change the
medium, a `visited` mark making re-entry a no-op, and reachability as the question. The name licensed
the build: `crates/holonic-engine/src/name_elaboration.rs:996` is a layered BFS whose re-entry branch
records a further depth and does not re-open. **The correction is not a rename** — renaming it
RIDE/FOUND would mislabel graph traversal as causal conduct. The noun is not the defect; **a medium
that does not change under traversal is.**

**Corrective form.** Before naming an object with a picture, search for the exact term this project
already uses. If a definition exists, use it and state it as a set equation. If none exists, write one
before naming it. Where the picture is genuinely doing explanatory work — traffic, enzymes, diffusion
— deposit it as an analogy with `CLAUDE.md` §4's four slots named, never as the object's name.
`canon/THE_TRAFFIC_SYSTEM.md` is the worked form.

### 2.8 The serial find

**Condition.** A defect is reported one instance at a time. Each report closes with a sentence about
the next one, and no deposit ever enumerates the population.

**Verified instance.** *"That is the same law one level down"*, written about `characteristic_delay`
being pinned by its only caller, in a session that had already found `LEADER_WITNESS_DEPTH` and
`REFINEMENT_APERTURE` the same way. Brandon named it: *"you will keep saying things like 'that is the
same law one level down', when the fact is that we already know how the network needs to work, and
that **we are not the ones meant to be pinning levels to minimums and maximums**."* The unconsumed
return ran the same loop faster — three instances in one session, two reported by the author before
the third was committed.

**Corrective form.** State the **condition**, enumerate the **population** under it in the same
deposit, then plan the excisions against the enumeration.

## 3. The reading, by hand, in order

Any means of looking is admissible. A negative result from any instrument is a statement about that
instrument (§1 law 1) and is never reported as a bound on the finding.

**Read the diff you are about to deposit, then:**

1. **Every new or changed `pub fn`/`pub struct` that returns a value.** Search the identifier across
   `crates/*/src` and `soma/*/src`. If every hit is the definition, a `#[cfg(test)]` body, an
   `examples/` file, or a doc comment — **2.1**. Write the consumer's `file:line`, or write that
   there is none.
2. **Every numeric literal and `const` you added or touched in a library path.** Answer in one
   sentence: *what derives this?* A theorem — name it. The caller — check the caller supplies it.
   Neither — **2.5**. Then read the **name**: does it assert a fact the code does not enforce, or
   enforce a restriction the name does not disclose? — **2.6**. Fixed-size arrays, `.take(n)`, and
   `min`/`max` against a literal are levels; the declaration form is irrelevant.
3. **Every control, null, gauge, cross-check.** Ask: *what configuration of the declared material
   would make this fail?* If you cannot construct one it is a snapshot — **2.2**. Then check its
   inputs: does the "independent" side import anything from the side under test? Are its comparison
   constants literals set after measuring? Does it compare cardinalities where it should compare sets
   — one deleted edge plus one manufactured edge passes a cardinality null.
4. **Every figure.** Name the route. Where a second route ran, both figures appear. **Verify any
   reconciliation you write.** Then read the deposit's sections against each other.
5. **Every grade, ratification, quotation.** Open the line carrying the grade; copy the token
   verbatim. Where a grade is attributed to Brandon, name what he approved. Where a permission is
   quoted, quote its condition.
6. **Every name introduced.** Is it a picture over an object that has, or should have, a definition?
   — **2.7**.
7. **For every defect found in 1–6:** state the condition and enumerate the population — **2.8**. A
   deposit with a fix and no enumeration is not ready.

## 4. The order of operations for a corrective construction

### Before an excision is admitted

1. **The owner is read.** Every use site named by `file:line`. An excision planned against a list you
   did not produce by reading is not planned.
2. **The replacement is named and its source stated** — read off the material, or supplied by the
   caller. *"Derived"* means you can write the computation. If neither is available the excision is
   deferred and the item **stays a held contaminant**; it is not reclassified.
3. **The cost is named** — which callers change, which return shapes change, which grades move, which
   records go stale.
4. **The material that separates before from after is exhibited.** This is §2.2's demand pointed at
   the change instead of at the check.

### An excision is graded by its orbit

Lift the pin, re-run the declared material, exhibit the difference. Three outcomes, and **all three
are reportable returns**:

| outcome | reading |
|---|---|
| **the return moves** | the level was deciding the answer. The movement **is** the finding, and it is the strongest evidence the species produces. |
| **the return holds, the reachable population grows** | the level was a ceiling nothing had yet hit. Record the new aperture and **state what material would hit it** — otherwise the next reader cannot tell this from the third case. |
| **nothing moves and nothing can** | the level was inert; it was never a level. Delete it as dead code and **say the excision returned nothing.** |

A wave of excisions that reports no movement anywhere has done bookkeeping, and must say so rather
than presenting a green suite as evidence. This is `CLAUDE.md` §8's *"a check whose material cannot
vary the property under test"* applied to the repair.

### What must be exhibited with it

- **The library consumer, by `file:line`, of every return the construction adds.**
- **A control with a non-trivial orbit**, which returns that orbit and refuses itself when it is
  trivial.
- **The distinguishing word** where the claim is that two things differ.
- **Both figures** where two routes ran, with the disagreement named.
- **The population** under the species condition, not just the instance.

### What makes it deposit-ready

- Every figure taken by running, carrying its commit; a gate figure carries its clock time.
- Every grade quoted verbatim from the line that carries it.
- `python3 tools/resolve_named_paths.py` returns zero failures.
- No authored level introduced; if one was, it is dispositioned in the same commit.
- The record exists, the canon points at it, the owners point back (`canon/THE_DOCUMENT_LAW.md` §4.5).

**Sequencing.** Instruments before excisions, and an instrument is a *stated check*, not necessarily
a program. **The item that most directly serves the objective — arbitrary degree, varying charts — is
not deferred for being large.** A restriction that deletes the mechanism under study is the
highest-value excision, not the riskiest thing to schedule.

## 5. What an agent brief must carry

Agents return **evidence to be checked**, never conclusions to relay. Four audits ran on 2026-08-09
and every one was partly wrong: one reported a genuine Brandon quotation as fabricated (the *"Do not
remove chronology"* line, which he wrote in a Codex conversation); another was right about `temper`
where the dispatching session initially doubted it. Neither is unusual and neither is grounds for not
dispatching.

1. **`file:line` for every claim.** A finding with no location is not acted on.
2. **The command and its raw output** for anything measured. A summarised measurement is a claim
   about a measurement.
3. **Negative results with the exact search that produced them.** An absence claim is a measurement
   and decays like one. `CLAUDE.md` §5 carries the worked case: `fn remove|fn forget|fn prune|fn
   ablate` against an owner named `fn without_stem`, false on the day it was written.
4. **No composed quotation.** A quotation attributed to Brandon is copied from a document or
   transcript that already carries it, and the brief **names the source to copy from**. (`CLAUDE.md`
   §9.)
5. **A ranking by what the dispatcher must re-check first**, and an explicit list of what the agent
   could not verify.
6. **Contradictions reported, not merged.** Convergence of independent auditors is evidence; a merged
   summary destroys it.

**The dispatching session's obligation, which the brief does not remove:** every load-bearing finding
is re-verified by hand before it is acted on, and where an agent was wrong that is reported alongside
what it got right. Relaying an agent's conclusion is the same defect as depositing an unreconciled
figure — one route, no second reading.

## 6. What this protocol does not cover

- **Mathematical error.** A false theorem, correctly graded and correctly consumed, trips no species
  here. Grading truth is `canon/EPISTEMIC_GRADES.md`.
- **Fabricated provenance.** `CLAUDE.md` §9 owns it. `tools/verify_quotes.py` was struck 2026-08-09
  by direct ruling — *"just read my quotes it's not that hard, we don't need to overengineer that"* —
  and reading is the replacement. Its ~100 normalization artifacts around one real hit were
  themselves an instance of §1 law 1.
- **The conditioning contaminants.** `CLAUDE.md` §13, discharged rather than open. Do not
  re-litigate.
- **Priority and scheduling.** It says what may be deposited, never what to build.
  `blueprint/THE_ROADMAP.md` holds the order of work; `canon/THE_HOLOBROCHOS_SPINE.md` decides whether
  an organ is on the spine at all.
- **Figures whose source is unrecoverable.** `canon/THE_MEASURED_CAPABILITIES.md` §4 holds those.
- **The correctness of a replacement.** Deriving `MAXIMUM_ISOLATION_DEPTH` from a Mahler bound is real
  mathematics and this protocol says nothing about whether the bound is right. It requires only that
  the derivation be stated and checkable.
- **Its own completeness.** Eight species because eight have verified instances. A ninth will be found
  the way these were, and §1 law 2 governs what happens next.

**It has no gate.** `tools/authored_levels.py --check` and `tools/resolve_named_paths.py` exist and
are useful; neither is a precondition of following this document, and **neither being unable to see a
class of defect is ever a reason to leave one standing.**
