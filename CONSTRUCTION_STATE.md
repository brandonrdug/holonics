# Construction state

**The position record. One file, no siblings** (`canon/THE_DOCUMENT_LAW.md` §1.4). It says what is
admitted right now. It is not a log, not a plan, and not a history; git is the log and
`blueprint/THE_ROADMAP.md` is the plan.

**Currency:** 2026-08-07, 14:34. **Body:** Rust. The C++/CUDA engine's position record is
`archive/cpp-engine/CONSTRUCTION_STATE.md` and governs nothing.

**Read the currency stamp, not just the date.** This record was written while other work was
landing in the same working tree; two of its measurements moved between 14:09 and 14:34 and were
re-taken. Every figure below carries the clock time it was measured at, and the permanent checks at
the foot of this file are the way to re-take any of them. A number in a position record is a
measurement, never a standing fact.

---

## The admitted body

**Truth status:** `established-bounded`. **Evidence:** `implemented-exact`, `measured`.

One Rust workspace at `/home/b/Workspaces/holonics`, 282 tracked `.rs` files, 277,006 lines.

```
crates/  holonic-structure            ordinal and relation atlases, local populations,
                                      branch lineage, typed atomic membrane
         relational-geometry          exact projective geometry over BigRational,
                                      Sturm-certified roots
         holonic-engine               receiver-relative geometry and physics, float-free,
                                      two hand-written CUDA kernels under kernels/
         holonic-language             the reflective runtime: reify, absorb, resume
         holonic-architecture-lint    the monotone ownership ratchet
soma/    body                         pure law, no_std, zero dependencies
         membrane · abi · surface · mount · life · tools
         kernel/soma.spv              committed boundary artifact
```

**The gate, read directly** (`PATH=/opt/cuda/bin:$PATH cargo test --workspace --no-fail-fast`,
2026-08-08, summed across **42** `test result:` lines on a tree with nothing else running):

```
1325 passed, 0 failed, 14 ignored
```

**Take the figure by summing the result lines, never by reading one of them and never through a pipe
to `tail`.** A `tail` cuts the earlier packages off and returns a number that looks like a total; it
happened here on 2026-08-08 and returned 237.

**The two figures before it, and why they moved.** `982` was the tree at `6778219`, before the
assembly landed. `730` was 2026-08-07 14:34. Between `982` and `1184`, eight organs were wired to
`blueprint/THE_ASSEMBLY.md`, eight adversaries refuted the *evidence* for all eight — roughly forty
mutations surviving a green suite, none of them against the wiring — and eight repairs closed them.
The intermediate `1121` figure appears in those reports and was honest when taken.

**Earlier still, this moved during a session.** At 14:09 on 2026-08-07 the same command returned
`543 passed, 1 failed, 14 ignored`, the one failure being `mount-scope-gate`'s
`founded_reference_path_is_deterministic_and_nonvacuous` returning `(255, 159, 35)` against an
expected `(256, 160, 38)` — laboratory fixture drift that predated the import. That fixture was
regenerated against the carriage law, and a Lean kernel witness was added, in the same tree in the
same session. The suite is now green.

**Purity, measured 2026-08-07 14:34.** `grep -rnE '\b(f32|f64)\b'` returns **zero** across every library:
`soma/{body,abi,membrane,surface,mount}`, `soma/life/src`, and all five `crates/*/src`. The 33 float
occurrences in the tree are all in `examples/` and are all boundary codecs — `f32::from_bits` over
GLM and NetCDF source octets, a geographic projection for a rendered figure, and one
`rational_to_f64` at a plotting boundary. That is the declared apparatus role, not the interior.

---

## Verified position — what survived the transition

**Truth status:** `established-bounded`. **Evidence:** direct source inspection and grep, 2026-08-07.

Each row was measured in this tree, not carried over from a receipt. **Archived** means the
mechanism exists only under `archive/cpp-engine/` and is not part of the live body. **Re-establish**
means the live body does not own it and a movement must build it.

| Mechanism the archived record admitted | Status | Where it resolves now |
|---|---|---|
| Exact rational and integer carriers | **survived** | `crates/relational-geometry/src/exact.rs` (`Rat`, `ExactExpr`), `soma/body/src/num.rs` |
| Exact projective geometry, Sturm-certified roots | **survived** | `crates/relational-geometry/src/{projection,exact_analysis}.rs`, `crates/holonic-engine/src/conic.rs` |
| Exact linear and chain calculus | **survived** | `crates/holonic-engine/src/exact_linear.rs`, `holonic_complex.rs` |
| Certified exact enclosure carrier | **survived, in Rust form** | `crates/holonic-engine/src/exact_value.rs` — see below |
| Cellular-sheaf Hodge transport | **survived** | `crates/holonic-engine/src/sheaf_diffusion.rs` |
| Loss as an exact geometric body | **survived** | `crates/holonic-engine/src/basin.rs` :: `enact_outcome_basin` |
| Planar-diagram analysis, Ihara zeta | **survived** | `crates/relational-geometry/src/receiver_topology.rs`, aperture 20 vertices |
| Arithmetic incidence, arithmetic fibers | **survived** | `crates/holonic-engine/src/{arithmetic_dimensional,arithmetic_fiber}.rs` |
| GPU residency with exact host parity | **survived** | `crates/holonic-engine/kernels/*.cu`, `soma/life/src/live_current_cuda/`, `soma/kernel/soma.spv` |
| The learning ecology (nine ecologies) | **survived** | `soma/life/src/` — this is the laboratory's own code, not a port |
| **Toric geometry** | **re-establish** | no owner; `toric` returns zero across `crates/` and `soma/` |
| **Hodge realization / cycle class** | **re-establish** | no owner. `Hodge` in the live body names the *cellular-sheaf Laplacian* in `sheaf_diffusion.rs`, a discrete differential operator — **not** the supported-realization mechanism `CLAUDE.md` §2 and §11 discuss. Do not read one for the other. |
| **Characteristic modules, trace-form spectral placement** | **re-establish** | no owner; `characteristic` and `trace` return zero as module names |
| **Integer homology** | **BUILT — this row was stale and is corrected 2026-08-08** | `crates/holonic-engine/src/rebase_invariants.rs` is a whole module: `smith_normal_form` over `BigInt` with the pivot rule as an explicit parameter, invariant factors, Betti numbers, torsion. The measured `Z/2` at grade 1 in `research/records/2026-08-08_THE_WINDING_IS_THE_PHASE_THE_OPTION_IS_A_DECLARED_RECEIVER.md` is a real return from it. **Hermite** normal form is still absent — `hermite_normal` returns zero — and that remains open. The grep this row quoted was taken before the module existed and was carried forward without re-running; §8's *grade the implementation, not the receipt* applies to position records too. |
| **The Chi pair** | **re-establish** | `ChiPair\|chi_pair` returns **zero** |
| **The deposit registry** (content hash + closure hash) | **archived** | `closure_sha256` resolves only at `archive/cpp-engine/cmake/HolonicDeposit.cmake` and `archive/cpp-engine/standing/MANIFEST.txt` |
| **The conditioned production shape** (two theorems, kernel-refused foil, structural ablation) | **archived** | the C++ body ran it at three declarations; the laboratory mounted 1,164 and never ran it |
| A Lean project | **survived, rebuilt 14:24–14:26** | at 14:09 `soma/formal` was 7 generated `.lean` files under `.lake/` with no `lakefile`, no `lean-toolchain` and no manifest. At 14:34 there are three projects — `soma/formal/{elementary-holonics, kernel-witness, rh-source-transport}` — each with `lakefile.toml` and `lean-toolchain`. Not this movement's work; recorded because a position record states the position |
| Reflection composed into formal mathematics | **re-establish** | `holonic_language\|Reflect` in `soma/life/src/lean_mathematics.rs` returns **zero** |
| A variable traversal schedule | **re-establish** | `pop_front` returns **5 hits, all hardcoded BFS** across `simplicial.rs`, `local_star.rs`, `graph_receiver.rs` |
| Reusable exact rank | **re-establish** | one definition, `crates/holonic-engine/src/algebraic.rs:1081`, **private**, ℚ-rank only |

**Two losses are permanent** and are recorded so they are not searched for again. `git log --all --
"*tiger*"` returns nothing in either repository. `git log --all -- "*semantics_invariant*"` returns
nothing in the laboratory at any commit; the machine's kernel-accepted theorem
`semantics_invariant_under_exact_chart` survives only as a name, the proof term
`by exact semantics_rebase_iff A e θ input output`, the axiom surface `[Quot.sound]`, and SHA-256
`10eeb3fd789972d071498e590e836a5ac036dc4b4261bef29102366c28e00be1`. The residue-stratum atlas the
archived record cites as `output/arithmetic-dimensional-receiver/` is a **third** loss of the same
kind: it resolves in neither repository, at no commit, because it was written to an untracked output
directory.

### The certified exact enclosure carrier exists, in Rust

`CLAUDE.md` §11 names this as the first brick and located it at
`archive/cpp-engine/src/include/holonics/exact/enclosure.hpp`, which is archived. It has a live Rust owner, and the Rust form is the stronger of the two:

- `crates/holonic-engine/src/exact_value.rs:82` — `ExactInterval { lower: Rat, upper: Rat }`. A set,
  never a value, over exact rationals rather than dyadics.
- `:64` — `ExactOrdering { Less, Equal, Greater, Open }`. The module's own first sentences: *"A
  decimal approximation is never a member of this carrier. Values which cannot yet be ordered from
  their exact certificates return `Open` rather than falling through to an epsilon comparison."*
- `:189` — `AlgebraicRoot` with a `SturmIsolationCertificate`, refusing construction unless the
  isolating interval provably contains exactly one root.
- `:238` — `SeriesTailCertificate`, three species (`AbsoluteGeometric`, `AlternatingMonotone`,
  `ExactTail`), each returning an **exact rational remainder interval**; `CertifiedSeries::enclosure`
  is the partial sum translated by that certified remainder.

**Reach, measured.** `ExactInterval` 104 references across 9 files, 20 of them in drivers;
`ExactValue` 57 across 7 files, 36 in drivers. `CertifiedSeries` 13 references in **one** file and
`SeriesTailCertificate` 6 in **one** file, **zero in any driver** — the remainder-certificate half of
the carrier is written and never exercised. That is the part §11's question actually needs.

**What this does not establish.** The carrier is not the organ. §11 asks for an exactly computed
positive form on a supported realizer population with a certified remainder and a reopening rule
keyed to the receiver family. The certified remainder is the first of those four and it is present.
The positive form, the supported realizer population, and the reopening rule are not.

### The contamination audit, re-run against the imported Rust

`CLAUDE.md` §13 convicted the archived C++ body's learning layer. The audit is re-run here against
`crates/` and `soma/` so its standing obligations can be read as discharged or inherited rather than
assumed either way.

| Sweep | Result in the live Rust body |
|---|---|
| Counter-morphology — a retained field named `morphology`/`tally` that is incremented | **zero sites, zero files.** `\b(morphology\|tally\|admitted_tally)[a-z_]*\s*(\+=\|-=)` returns nothing |
| The scorer's own vocabulary — `response_weight`, `transport_weight`, `codec_bias`, `obstruction_threshold` | **zero each** |
| `bias`, `learning_rate`, `softmax`, `sigmoid` anywhere | **zero each** |
| Hardcoded-delta ablation — a literal subtracted from a retained count | **zero.** The one `-= 1` on a count, `soma/life/examples/eros_cohered_corpus.rs:117`, removes one occurrence of a key from an exact multiset and deletes the key at zero |
| `+= if …{N} else {M}` — the C++ tally shape | **2 sites, neither a tally**: `exact_analysis.rs:992` and `radix_residue_character_transport.rs:572`, both the prime-candidate stepper `2 → 3 → 5 → 7 → 9 …` |
| `weight` (39 occurrences) | all legitimate: graded-algebra comparative degree (exact `u32`, refused at zero), exact rational weighted mean, radix place value, and one external OLMo tensor name read as source material |
| `threshold` (7 occurrences) | **all seven are negative declarations** — comments saying the code does *not* use one, e.g. `soma/body/src/chart.rs:2`: *"not ask whether a scalar occupancy is beyond an authored threshold"* |
| `score` (35 occurrences) | **34 are negative declarations** in doc comments across `abi`, `membrane`, `body`, `life` and `holonic-engine`. **One is a live binding**: `soma/life/examples/eros_pretrained_ecology_cultivation.rs:1105`, an exact `Dyadic` magnitude ordering candidate factors of a foreign pretrained model, with a deterministic `factor <` tie-break, in a driver reading external material — not in the body's conditioning path |

**Verdict: the §13 obligations are discharged, not inherited.** The scorer, the counter-morphology,
and the constant-subtraction ablation do not exist in the live body in any form, and the discipline
they were meant to enforce is visible in the source as thirty-four explicit refusals to use a score.

**What this does not establish.** A clean sweep proves the convicted mechanism is absent. It does
not prove the mechanism §13 demanded in its place — a structural change in reusable morphology, a
source-detached remount, and an ablation that removes later conduct by removing structure — is
implemented and driven here. That is a separate grade and it is open.

---

## The established floor

**Truth status:** `established-bounded`. The laboratory's floor is stated in full at `CLAUDE.md` §5
with its exact scope, and is not restated here. **All of its code is now in this tree**, at
`soma/life/src/` and `crates/`, rather than only in the frozen laboratory. That is the single fact
this section carries, and it is what changed on 2026-08-07.

**None of it is a construction target.** An established capability is admissible without limit as
the *carrier* of a deed and inadmissible only as its *return* (`CLAUDE.md` §1).

---

## Current construction position

**Truth status:** `project-postulate`.

`blueprint/THE_ROADMAP.md` is the single active roadmap and the only file that says what is open.
Its Part one exists because the repository could not previously say which of its own claims survived
the transition; the table above is that answer.

The known gap between *written* and *driven* is stated in the roadmap by owner: ten imported
owners — including `ExactReceiverCurrentLaw`, `LeanKernelWorld`, `AgenticResearchSession`, and
`LeanMathematicsEcology` — carry **zero** references from any `examples/`, `tests/`, or `bin/` path,
while `LiveCurrentMachine` carries 223. The proof-line owners are precisely the undriven ones. To
that list this record adds `CertifiedSeries` and `SeriesTailCertificate`, measured above.

No successor is scheduled by incrementing anything, and no movement is named by an ordinal.

---

## Permanent checks

A figure here without a clock time is a defect. Re-take it.

| Check | Command | What it falsifies |
|---|---|---|
| Every path a governing document names resolves | `python3 tools/resolve_named_paths.py` | a live document describing a body that is not this one |
| The gate | `PATH=/opt/cuda/bin:$PATH cargo test --workspace` | any claim resting on the suite |
| Ownership ratchet | `cargo run -p holonic-architecture-lint` | an owner acquiring a responsibility it must not hold |

**The ownership ratchet does not currently run.** Measured 2026-08-07: it exits with
`failed to read /home/b/Workspaces/holonics/HOLONIC_DSA_BASELINE.tsv: No such file or directory`.
`BASELINE_PATH` at `crates/holonic-architecture-lint/src/lib.rs:14` is a repository-root-relative
name inherited from the laboratory layout, and the only copy of that file in this tree is
`reference/engine-a07ff376/HOLONIC_DSA_BASELINE.tsv`, which is archive material. Listing the check
above is a statement of what it is for, not a claim that it passes.

**The path check, in one paragraph.** It reads every `.md` at the root, in `canon/`, and in
`blueprint/`, extracts every backticked or linked path-like token, and resolves each one. A
document opening with a SUPERSEDED or ARCHIVE banner may name archived paths; a live one may not,
and a live document naming a path that resolves **only** under `archive/` without saying so is the
failure. Measured 2026-08-07 14:38: **947 tokens, 0 failures, exit 0**, in 0.11 s. Before the
movement that deposited it: **409 failures**. Its control is direct — planting a bare archived
C++ header name in `CLAUDE.md` returns `ARCHIVE` and exit 1, and planting a non-existent Rust owner
returns `MISSING` and exit 1. *(The bare header name is not written here: this paragraph is in a
live document, and the check reads it. It caught this sentence on the first run, which is the
cheapest possible demonstration that it works.)*

**Thirty-four tokens are declared absent** in `tools/resolve_named_paths.allow`, each with its
reason: a genre the document law defines and this repository has not built, a path named in order
to report its loss, an owner deleted by an excision with the commit that deleted it, a runtime
artifact, a movement's proposed target, or the roadmap's own table of the defect this movement
closed. The check reports any allow entry whose document no longer names it, so the file cannot
rot. **It is not for stale references**: a path absent because a document was never updated is a
failure, and the document gets fixed.

## The scale claim, reconciled — deposited 2026-08-07

Brandon, 2026-08-07: *"evolution is not exclusive to biology, diffusion and coarse graining happens
on a cosmological scale too, that is what our galaxies come from logically."*

A sweep of both repositories returns: **no deposit anywhere states that biological evolution,
information diffusion, and cosmological structure formation are one mechanism at different scales.**
That absence is the finding, and it is not an oversight — the record stops one step short on
purpose, and the stopping is doctrinal.

**The two statements are not in conflict, and this is the reconciliation the record lacked.**

His own governing clause is in the same family of messages
(`canon/THE_QUOTE_NETWORK.md:202-210`): morphology is *"the framework in which biology can be
studied by, the same framework you'd use to study variations of stars that fuse elements into
heavier elements, and the same framework you'd use to figure out astronomical distributions"* — and
in the same breath, **"there is no one general law."** The unification he asserts is of **method**,
and he explicitly denies a single dynamical law. The laboratory's own doctrine says the same thing:
*"the commonality is the operator ecology, not a flattened representation or one formula."*

And the live record's nearest statement, `research/records/2026-07-19_THE_STRESS_IS_THE_TRANSPORT_OF_TRANSPORT_THE_HEAT_IS_THE_BOUNDARY_DEED.md`:

> *"This is the exact sense in which physical, evolutionary, linguistic, and mathematical patterns
> can be self-similar. … The lawful comparison transports cut, symmetry, conservation/hand,
> recurrence, phase boundary, response, and consequence. **It does not identify the material
> interiors.**"*

So the deposit is: **one grammar, many media, no shared carrier.** Coarse-graining is the common
operation; the coupling constants and phase boundaries stay medium-specific. Claiming one mechanism
would flatten exactly what he forbids flattening; claiming mere analogy would contradict his
standing rebuke — *"all of my biological analogies are not really simply analogies … the way
evolution works mechanically is exactly what we are trying to encapsulate. The trees, branches, and
roots of a forest as an analogy is **literal**"* — which the quote network grades as *his most
persistent and least-deposited cluster.* Both are now carried.

**The falsifier, which makes this a claim rather than a posture.** If the same coarse-graining
operation is genuinely the common method, then `crates/holonic-engine/src/receiver_exact_compression.rs`
must return the same *kind* of artifact — a counted, exhibitable collapsed population with the
shortest separating context — on materially unrelated sources, and the *shapes* of those populations
must differ. Identical shapes would mean the instrument is reading itself rather than the material;
no exhibitable population at all on some medium would bound the claim to the media where it works.

**The sharpest open item this sweep found is not cosmological.** The grain-1 quotient of the phase
atlas — **82 coarser points, 71 overlap cells, one with 14 members** — was computed and **has never
been drawn or looked at**. Every figure this project has examined is grain 0. The coarse grain
exists as data and nobody has seen it.
