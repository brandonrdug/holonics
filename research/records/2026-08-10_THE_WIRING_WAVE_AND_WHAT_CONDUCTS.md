# The wiring wave closed six edges, and a return compared against a return cannot witness a transport

**Date:** 2026-08-10
**Truth status:** `established-bounded` for each join that has a conduct path and a driver that ran;
`counterexample` for §7, which refutes a class of control this repository has been relying on;
`open` for the six joins named in §8 that could not be made, each with its exact obstruction.
**Evidence:** `implemented-exact` — every owner cited below was read at the line, and the
`#[cfg(test)]` boundary of its file was located, before it was graded. `measured` — the six
`examples/` drivers were re-run by the synthesis session, not quoted from the builders' reports;
figures below are from those runs. `computational-witness` for the U(3,3) winding decomposition,
which the verifier re-derived by hand and confirmed against a brute-force search.
**Provenance:** assistant derivation. Seven joins were attempted by seven builders and each was
adversarially verified by a separate reader. **Where a verifier refuted a builder, this record
carries the verifier's position and not the builder's claim** — that happened once, in §2, and its
withdrawal is the record's second-most-important content. No sentence below is attributed to
Brandon; §9 of `CLAUDE.md` forbids a delegated session composing one, and none did.
**Band:** **2026-08-10 · ASSISTANT DERIVATION / DEPOSITED FOR REVIEW / SEVEN JOINS ATTEMPTED, SIX
CONDUCT / SOURCE CHANGED IN SEVEN OWNERS ACROSS TWO CRATES / SIX DRIVERS RUN AT `d3dc9c3`+DIRTY /
ONE BUILDER HEADLINE WITHDRAWN / THREE DEPOSITED DOCUMENT DEFECTS NAMED / NOT COMMITTED**

---

## Present question

`canon/THE_HOLOBROCHOS_SPINE.md` names cuts: places where an organ emits and nothing returns. A
wave of seven sessions was sent to close edges at named cuts — **not to build organs.** The
question this record answers is not *did the code compile*. It is:

> **Which of the seven joins put a return edge on a conduct path, which returned a number the body
> already owned, and — where a join looked closed — what instrument was doing the looking?**

The answer to the third clause turned out to be the wave's real return, and it is stated first
because it reframes the other six.

---

## 1 · The finding that outranks the wave: return-equality cannot witness a passage

The `generation-executor-seam` builder did the one thing that separates a wiring claim from a
wiring narration: it **built the fake twin on purpose** — an executor-taking function that ignores
its executor and falls back to the private host pool — and re-ran its own controls. The verifier
independently rebuilt the same fake (`answer_continuation.rs:513` → `let _ = executor;`) and got
the identical table:

```
  [HELD]   the supplied-executor world-return answer equals the private-host answer
  [HELD]   the supplied-executor grounded answer equals the private-host answer
  [FAILED] the world-return answer crossed the supplied carrier (0 enactments)
  [FAILED] the grounded answer crossed the supplied carrier (0 enactments)
  [FAILED] a refusing carrier makes the world-return answer path FAIL
  [FAILED] both refusals were actually consulted (0 and 0)
```

**Both equality controls held under a decorative twin.** The compared object was not a scalar or a
hash — it was the whole `AgenticLanguageAnswer`, tokens and version lineage included. It is
bit-identical whether the carrier was crossed or not, because a correct twin is *required* to
return what the private path returns.

Only two instruments separated the real twin from the fake: the **count of crossings** the carrier
itself recorded, and the **refusal** a deliberately-refusing carrier produced.

That is this project's own object turned on its own instruments. `CLAUDE.md` §0: *the object is the
transformation of information between two things that cannot see each other's interiors.* A return
is the outside of an interior. **Comparing two returns cannot tell you whether a passage occurred,
because a passage that occurred and a passage that did not are required to return the same thing.**
What witnesses the passage is a count taken *inside* the carrier and a refusal issued *by* it —
testimony from the far side, not a comparison on the near side.

And the wave then supplies four more instances of the same defect, none of which its builders had
connected to this one:

| join | the instrument | why it could not fail |
|---|---|---|
| `spine-cut-driver` control 8 | `left.population != right.population` across 491 vs 329 readings | any ablation removing any route makes two maps differ; the stated falsifier ("an ablation that removes no cell") describes a no-op |
| `spine-cut-driver` control 4 | "an open route leaks and its closure does not" | `open_route_leaks` counts routes **constructed**, not routes that leaked (`the_cut_is_named_on_real_material.rs:749`, `open = singles.len()`); and an open path's divergence is non-zero at its endpoints **by construction** |
| `contact-gluing` regression test | `contact_gluing.rs:930-940` | every assertion passes verbatim under the *pre-repair* hardcoded return; the test is called with `("exactcarrier", "exactcarry")`, canonical order, so `vec![left, right, left]` and the computed walk agree. **A revert goes green.** |
| `placement-caller` class-side split | `split.positive == 4`, `split.zero == 7`, `split.negative == 0` | `supported_realizers.rs:135` is `free_obstruction() = class_extent.saturating_sub(supported_rank)`, and `supported_rank = rank(M)`. The three asserted numbers are `RealizerSupport`'s own, already computed at `placement.rs:149` before the join ran. `negative == 0` is convicted as tautological in that module's own header. |

Five instruments in one wave, each built specifically to prove a join was real, each unable to
vary under the property it was testing. This is `CLAUDE.md` §8's `PivotRule::ALL` instance — *the
anti-defect instrument was itself the defect* — recurring at a rate of better than one join in two.
The remedy the wave demonstrates is not more controls; it is **controls of a different species**:
count the crossing, exhibit the refusal, name the separating word.

---

## 2 · The one refutation: an ablation that deletes a family is not an ablation that moves a cut

`spine-cut-driver` reported three returns. The first was withdrawn by its verifier and the
withdrawal is upheld here, verified from source.

**The builder's claim:** *"The ablation moves the cut. Removing the 7 artifacts declaring
`formal_carry` takes accumulation 27 → 0 under the head-determined rule."*

**What the source says.** `derivation_integral.rs:932 recruited_declaration_family` opens with
`let recruited = recruited_declarations(circuit);` and iterates it. Ablating every artifact that
declares `formal_carry` empties `recruited_declarations`, so the family has **zero members**. The
27 `accumulation` readings *were* that family. The verifier's probe measured it directly:
`recruited-declaration pair names surviving the ablation: 0`.

My own re-run at `d3dc9c3`+dirty reproduces the populations:

```
whole      {"accumulation": 27, "circulation j != 0": 36, "leak": 72, "rest": 1, "short circuit": 355}
ablated    {                    "circulation j != 0": 27, "leak": 54, "rest": 1, "short circuit": 247}
```

`accumulation` is not `0`. It is **absent** — the key does not occur. 162 of 491 readings were
removed and **no surviving reading changed cut.** The honest statement:

> The structural ablation removes the family that accumulated. Whether any *surviving* reading
> changes cut is not measured by this driver, and control 8 as written cannot distinguish deletion
> from movement.

The correspondence the builder drew to `CLAUDE.md` §0c's *"circuit E exact after the ablation"* and
its `residual 57` is likewise asserted, not computed by anything in the driver. It is uncorroborated
and is carried here as such.

**What survives of that join, and it is real:** `spine_cut::read_the_chain` is `pub` at
`spine_cut.rs:239`, above the `#[cfg(test)]` boundary at `:341`, and `:270` reads
`reading.residual = reading.divergence();`. The residual is **not a parameter** — that is
dispositive by signature, and it is what makes "no emission without a return edge" checkable rather
than declared. Its control 7 is the wave's strongest single instrument and is §8's vacuous-gauge
test done correctly: it matches loops **by name** across two accumulation rules and requires the cut
to change. **516 loops move**, re-measured.

**Unreported structural weakness, and it is the reason "all five cuts reached" reads better than it
is.** Under whole/route-load the decomposition is exact and by family: 36 statement-lineage pairs →
all circulation; 27 recruited-declaration pairs → all accumulation; 355 shared-identifier pairs →
all short circuit; 72 open routes → all leak; 1 backtrack → rest. Every family lands entirely in one
cut, and two of the five are forced by construction — an open path always has non-zero endpoint
divergence, and `against` then `along` on one cell is always zero current. **The five cuts track
the five families the driver chose to build**, not five species the material distinguishes.

---

## 3 · What conducts now that did not

Four joins put a return where none was reachable. Each is stated with what the *before* state was,
measured, not remembered.

### 3.1 An ablated body can be written to disk at all

**The strongest join of the wave.** The committed baseline contains a test asserting the opposite
behaviour, which the diff removes:

```rust
-    fn a_morphology_the_seam_cannot_refound_is_refused_at_the_seal() {
-        match ConditionedRest::seal(&ablated) {
-            Err(ConditionedRestRefusal::MorphologyNotRefoundable { differing }) => {
```

`FoundedMorphology::without_stem` retains surviving stems' original `StemId`s; the only foreign
constructor `from_founded_words` derives ids from arrival order. An ablated body therefore could
not round-trip, and `conditioned_rest.rs` refused it **at the seal**. `CLAUDE.md` §5 names the lift
required: `FoundedMorphology::from_founded_stems(Vec<FoundedStem>)`. It is built, `pub` at
`conditioned_derivation.rs:313`, with `refoundable` at `:332`, both far above that file's
`#[cfg(test)]` at `:2010`, and reached from four non-test mouths in `conditioned_rest.rs`.

The load-bearing design decision is that **ids are preserved on purpose**: the gap where the removed
stem stood *is* the record of the ablation. Renumber it and an ablated body becomes indistinguishable
from one founded on the smaller corpus. The constructor therefore requires the *chain* — every stem's
parent is its immediate predecessor in the population — and not the numbering, and refuses eleven
named conditions.

My re-run, `soma/life/examples/the_ablated_body_rests_and_remounts.rs`, exit 0, eleven controls held:

```
  1274 founded stems; removing "a" (identity 94): 155 -> 133 passages
    22 passages structurally absent, 110 circuit cells absent, 0 reopened, 0 unaccounted
  sealed 383027 octets, address 62a7d2f77daa9129e9648466cd0ea7edace921c24baead36a2b5dd1d43cf3e8f
  after chdir out of the repository: 118 opens attempted, 118 ErrorKind::NotFound, 0 opened
  remount: 1273 stems, 0 differ on identity/parent/wholes/lineage; identity 94 ABSENT
  production: 184825 rendered octets on both sides over 133 passages
  a further whole: 13 stems moved, 0 of 1273 identities renumbered
```

Its control with the sharpest teeth: *"the ablated population is one the FOUNDING seam cannot
carry"* — `from_founded_words` returns **1179 of 1273 stems differing**. The driver states, and the
engine test asserts, the one material that would make that control vacuous: **ablating the
last-founded stem**, where identities stay contiguous and the founding seam reproduces the
population exactly. That is a control naming its own failing material and then checking it — the
form this record recommends in §1.

**A second, silent renumbering path was found and closed en route.** `receive_whole` replayed the
whole population through `from_founded_words`, so every further whole would have closed an ablated
body's gap. It now takes `max(id)+1`. Without that repair the "goes on receiving without closing its
gap" control would have failed.

### 3.2 A caller-supplied carrier reaches an agentic answer

Measured before-state, independent of any record: `git show HEAD:soma/life/src/agentic_language/answer_continuation.rs | grep LiveCurrentExecutor` → **exit 1, zero matches**; same at `27fc74d`. The
executor seam terminated at `condition_with_executor` and **no caller-supplied carrier could reach
an answer.** Four twins now thread it, all `pub`/`pub(super)`, all above the test boundary:
`ecology.rs:775, 810, 1026` and `answer_continuation.rs:493`. The non-executor `prepare_answer`
wrapper was **deleted** — after the join it had zero callers, and §1 of `CLAUDE.md` refuses a
retired interface.

My re-run of `soma/life/examples/the_answer_crosses_the_mounted_carrier.rs`, exit 0,
`ALL CONTROLS HELD: true`:

```
  (conditioning, before any ask)   0 enactments
  question -> deed                 0
  world return -> answer          18
  grounded question -> answer     13
  total                           31        currents presented: 135
```

**Nothing moved that a caller can measure, and the driver says so.** The 18 and 13 are host-pool
enactments wearing a counter; the answer is *required* to be bit-identical to the private path's. No
speedup is claimed and none was measured. This is a precondition made expressible.

Its negative return is worth as much as its positive one: **`deed_crossing == 0`.** A question that
emits a deed crosses no Swing event, so a mounted carrier is carried unused from question to world
return. On that stretch of the loop the join is bookkeeping, and the driver states it as a control
that would notice if it ever stopped being true.

### 3.3 The ownership ratchet runs, and it had two broken frames rather than one

`CONSTRUCTION_STATE.md` recorded a missing baseline file and stopped there. The first frame **hid**
the second, because `check_repository` reads the baseline before taking the census. Building the
original binary from `d3dc9c3` exposes both:

```
--check:          failed to read .../HOLONIC_DSA_BASELINE.tsv: No such file      (frame 1)
--emit-baseline:  failed to read .../src/soma/body/src: No such file             (frame 2)
```

Three of five `PROTECTED_ROOTS` carried the laboratory's `src/soma/` prefix, so **the ratchet covered
none of `soma/`.** Repaired: `BASELINE_PATH` → `meta/HOLONIC_DSA_BASELINE.tsv`; roots rebased to
`soma/{body,membrane,life}/src`; a missing protected root now refuses by name
(`unresolved_protected_roots`, `pub fn` at `lib.rs:203`, reached from `census_repository:218`,
non-test); `protected_files` counted `(path, construct)` pairs and reported 971 for 193 files, now
counts distinct paths. **The aperture was not widened** — `soma/{abi,surface,mount}`,
`holonic-structure` and `relational-geometry` stay outside it, as inherited. 77 of the 193 baseline
rows are `soma/` (8 body, 20 membrane, 49 life); the ratchet covered zero of them before.

Eight gates now run as one sequence, `tools/gates.sh`, with `tools/gates.sh --control` making each
fail on purpose and restoring.

### 3.4 A matroid's negative directions are named rather than counted

Measured before-state: `git grep winding_inertia HEAD -- crates/holonic-engine/src/matroid_chow.rs`
returns nothing, exit 1. Nothing had handed a matroid's form to the organ that names windings.
`ChowRing::cyclic_generator_receiver` is now `pub fn` at `matroid_chow.rs:1377`, above that file's
`#[cfg(test)]` at `:1859`.

My re-run of `the_matroid_names_its_windings.rs`, exit 0:

```
  a cyclic reading EXISTS: [0, 3, 1, 5, 2, 4]   (walk touched 37 placements)
  the ring's own flat order is blind to it: entry (1,3) is not circulant
    character 0  winding   0   star {1/0}   with the turn
    character 1  winding 1/6   star {6/1}   on the null cone
    character 2  winding 1/3   star {3/1}   against the turn
    character 3  winding 1/2   star {2/1}   against the turn
    character 4  winding 2/3   star {3/2}   against the turn
    character 5  winding 5/6   star {6/5}   on the null cone
  elimination flat order / elimination cyclic reading / character route: (1 with, 2 null, 3 against)
```

This is `CLAUDE.md` §2b's standing obligation discharged on one object: *a count of signs is a state
reading; name the windings instead.* The pairing is `−I + Adj(C₆)` — the point/line incidence graph
of `B₃` is the hexagon — and the split provably **cannot** move, because the reordering goes through
the pre-existing `inertia::congruence`, which refuses a singular basis. Only nameability moves, which
is the point: Sylvester says a change of basis relabels passages and neither creates nor destroys
them.

**The reach is one matroid, and that is a theorem rather than a code limit.** A circulant carries
`c₀` on every diagonal entry; on a simple rank-three matroid `deg(x_L²) = −1` and
`deg(x_p²) = 1 − |{lines through p}|`, so constancy puts every point on exactly two lines and the
partition argument forces `|E| = 3`. `U(3,4)`, `M(K4)`, Fano and non-Pappus each returned
`DiagonalIsNotConstant` **naming the offending flat**; `U(2,3)` and `U(4,4)` never reach the question
(`TopIsNotTwo`). The verifier re-derived the eigenvalues by hand, checked the non-Pappus refusal
index independently (point 6 on 6 lines against points 0–5 on 5), and brute-forced the cyclic-reading
search against exhaustive permutation over 16,000 random forms: **791 found by the walk, 791 by brute
force, 0 mismatches, 0 false positives.**

**The bound that must travel with this join.** Closing an 8-line edge in `matroid_chow` took ~233
lines of new *library* machinery in `winding_inertia.rs`, of which `cyclic_receiver_of_form` and
`extend_cyclic_reading` are a backtracking search for a cyclic symmetry of a quadratic form. That is
a capability, not a wire, and it brushes the wave's own "no new organs" instruction. It survives
because the split cannot move; but **the receiver is discovered by search, not derived from
`Aut(M)`** — U(3,3)'s cyclic symmetry is a point↔line self-duality and `S₃` has no element of order
6. If a searched-for ordering is not admitted as a receiver, the honest reading is that the join
exists and its receiver is found rather than founded.

---

## 4 · What was repaired: two absolute frames, on conduct paths

Both are §0's fourth lesson — *a receiver-visible coordinate promoted into an invariant* — and
neither was found by a test. Both were found by driving an organ nothing had driven.

**`contact_gluing::ride_circuit` folded the caller's argument order into its return.**
`Circuit::through`, `::string` and `::reflected` were `vec![left, right, left]`, `vec![out, back]`
and `vec![false, true]` — the caller's own arguments restated as though measured. `find` accepts an
arc in **either** order, so `(X,Y)` and `(Y,X)` name the same two arcs and the same walk, and the
return reported `["agrees","abbrev","agrees"]` against `["abbrev","agrees","abbrev"]` for it. Now
read off `RunningIntegral`'s per-step `departed`/`arrived`/`orientation`. The repair is in the
non-test body of `pub fn ride_circuit`, `contact_gluing.rs:546-608`, and the file's `#[cfg(test)]`
begins at `:641`. The orbit was measured, not asserted: **0 of 708 circuits invariant before, 708 of
708 after.** `contact_graph:424-425` emits arcs only for `words[i]` against `words[j > i]`, so
`left != right` on every arc and the 0/708 is certain from source without re-running.

**`LeaderCochain::SpanLength` names two different quantities in two organs.** `ride_circuit:528` is
`BigInt::from(stem.len())` — letters in the occurrence. `declare_cochain:623` is
`BigInt::from(face.len())` — face cardinality. Same variant, two quantities, one name. The doc now
states both readings per organ; no behaviour changed.

**And the repair is not guarded by the suite.** I read the regression test at
`contact_gluing.rs:915-940`. It asserts `through.first() == through.last()`,
`reflected == vec![false, true]`, `series.len() == 2`, `series[1] < series[0]`, and
`series.last() == holonomy`. **Every one of those passes verbatim under the pre-repair hardcoded
return**, because the test calls with `("exactcarrier", "exactcarry")` — canonical order. The
repair's only guard is the driver's frame-1 control, which does not run under `cargo test`. That is
§1's defect once more, in the guard rather than in the driver.

---

## 5 · What is bookkeeping, and says so

**`placement-caller`'s class-side join returns nothing `place_substitutions` had not already
returned.** Verified from source: `supported_realizers.rs:135` is
`free_obstruction() = class_extent.saturating_sub(supported_rank)`, `supported_rank` is `rank(M)`,
and `placement.rs` computes `RealizerSupport` **before** the join runs. So
`induced_placement(M) = (rank, |C| − rank, 0)` is `(supported_rank, free_obstruction(), 0)` on all
material, and the module's own header already convicts the third as tautological: *"No incidence
whatsoever could make it come out otherwise."*

What the join is, honestly: a **conformance oracle** — a rational symmetric elimination reproducing a
rank that a Smith normal form over ℤ already returned, through four pivot orders and three apertures
— plus a docstring repair, plus **one artifact that is genuinely new**:

```
  ker(MMᵀ) — REALIZER combinations that land on nothing (nullity 3):
     1  +1·[fill the rim 012]   -1·[fill the rim 013]
     2  +2·[fill the rim 012]   -1·[fill the skeleton with BOTH at once]
     3  +1·[unfill 012: withdraw the triangle again]
```

That is absent from `RealizerSupport` entirely — and it comes from `induced_placement(Mᵀ)` plus the
driver's own hand-rolled null space, not from the class-side call the join was named for.

**The docstring repair is the join's most durable content.** `induced_placement`'s documentation and
`blueprint/THE_ROADMAP.md` both said *"the null directions are exactly the realizer combinations that
land on nothing."* `incidence()` is `IntegerMatrix::zeros(realizations.len(), class_extent)`
(`supported_realizers.rs:151`), so `MᵀM` is **class**-indexed and its kernel is a combination of
*classes* no declared move can separate. The realizer combinations are `ker(MMᵀ)`. Measured 7 and 3
on one shared rank of 4. **Both are Gram matrices, so both return `negative == 0` and a positivity
check cannot tell them apart** — which is why the error survived in prose for as long as it did.

Two further findings from that join stand and are not bookkeeping:

- **The split is blind to this module's own integral content.** A family reaching a class singly and
  a family reaching it only as `2·c` return the **identical** inertia `(1, 10, 0)` while their
  invariant factors are `[1]` and `[2]`. The `ℤ/2` lives only in `torsion_obstruction`. A rational
  split is not an integral obstruction, and `induced_placement` alone cannot close the Hodge-facing
  question the module header states — which is §3 of `CLAUDE.md`'s Kollár reading, arriving from the
  code side.
- **Half the class-space nullity is not new information.** Four of seven null directions are unit
  vectors on unreached classes — the free obstruction restated. The content is the other three:
  `[v3] − [e02 e03]`, `[v3] − [e12 e13]`, `[f023] − [f123]` — pairs of classes the *receivers*
  distinguish and the *move population* cannot.

**A mis-measured absence claim, corrected.** The builder justified a hand-rolled rational null space
with *"No public exact null-space owner exists"*, evidenced by
`grep -rn "null_space\|nullspace\|kernel_basis"`. That is a name-shaped grep of exactly the species
`CLAUDE.md` §5 convicts (`fn without_stem`, which `fn remove|fn prune|fn ablate` could not match).
`inverse_transport::ExactAffineVersionFiber` is public, and `quantity.rs:1045-1082 eliminate` already
reads a rational kernel basis off it with the **identical** free-column read-off, with
`quantity.rs:74-88` naming it in prose as *"the one that is both public enough and shaped right."*
The conclusion survives for a reason never checked: `ExactAffineVersionFiber::admit` is
**`pub(crate)`** (`inverse_transport.rs:260`), so an `examples/` driver cannot feed it rows. The
honest deposit is *the kernel carrier exists and a live module documents it as the right one; its
mouth is `pub(crate)`, so it has no external mouth* — a carrier-with-no-mouth, which is itself a cut.

---

## 6 · The ratchet's first act was to convict the wave that turned it on

`bash tools/gates.sh` at `d3dc9c3`+dirty, run by this session, 2026-08-10T18:18:29-07:00:

```
PASS  tests              2015 passed, 0 failed, 14 ignored over 42 result lines
PASS  authored-levels    0 failures; 207 authored numeric levels in library code
PASS  named-paths        FAILURES: 0; 1360 path tokens
FAIL  output-manifest    recorded 28 drivers, present 33: 0 departed, 1 moved, 5 unrecorded
FAIL  closure-manifest   24 closure(s) moved; producing crates: crates/holonic-engine soma/life
PASS  boundary-artifacts 3 artifact(s) bound
PASS  typst              10/10 roots compile
FAIL  architecture-lint  17 new ownership/materialization occurrences
5 passed, 3 failed
```

**All 17 rejected occurrences are this wave's own uncommitted edits** — `conditioned_derivation.rs`
`.clone()` 76 against 53, `spine_cut.rs` `BTreeSet` 20 against 15, `contact_gluing.rs` `Vec` 70
against 67, `matroid_chow.rs` `Vec` 123 against 119, `winding_inertia.rs` `Vec` 57 against 53,
`conditioned_rest.rs` `.clone()` 40 against 31. That is the ratchet doing its job on the first tree
it was ever pointed at, and the tree it was pointed at was the one that repaired it.

The three red gates were **deliberately not made green.** Regenerating `output_manifest` or
`closure_manifest` would content-address several parallel sessions' half-finished work and go stale
within the minute; `0 departed` throughout, so nothing is lost. `closure-manifest`'s 24 rows are one
edit reported twenty-three times, because a closure covers a whole crate's `src/**.rs`.

**A control the builder declared impossible was possible.** `boundary-artifacts` was reported
`NOT EXERCISED` on the grounds that reddening it means corrupting a tracked binary in a tree three
sessions compile against. The verifier flipped one octet at offset 64 of `soma/kernel/soma.spv`
**inside the detached worktree the builder had already built for the baseline** — green → red →
green, zero risk. The instrument was in hand and was not used. Recorded because "cannot be
controlled" is an absence claim and decays like one.

### Three document defects the wave deposited, all verified here

1. **A figure two governing documents carry that the tool does not return.**
   `CONSTRUCTION_STATE.md:491` and `canon/THE_DOCUMENT_LAW.md:727` both say **18,225 inherited
   occurrences**. The baseline's own arithmetic, summed by me over its 193 non-comment rows, is
   **18,203**, and that is what the tool prints. 18,225 is neither the inherited sum nor the
   dirty-tree census. Correct form: *193 files, 18,203 inherited occurrences at `d3dc9c3`.*
2. **Seven gates where the script has eight.** `bash tools/gates.sh --list` prints eight.
   `CONSTRUCTION_STATE.md:464` says *"Seven gates in order"* and `:496` *"Two of the seven gates"*;
   `CLAUDE.md:23-27` enumerates seven and **omits `boundary-artifacts`** — the eighth gate the same
   session added and highlighted in its own report.
3. **Three live documents still assert the ratchet is broken.** `blueprint/THE_MACHINE.md:200`
   (heading: *"The ownership ratchet does not run, and the cause is one missing file"*), `:202`
   (*"is not invoked by anything"*); `canon/THE_QUOTE_NETWORK.md:1928` (*"it is non-functional in
   this layout"*) and `:2219` (*"broken"*); `blueprint/THE_ROADMAP.md:212` (*"nothing runs
   `output_manifest.py` or `holonic-architecture-lint`"*). None is archive-bannered.
   `resolve_named_paths.py` cannot catch this class — every path in those sentences resolves.
   Sharper: `THE_QUOTE_NETWORK.md:1926-1933` recorded **both** frames in more detail than any other
   document, naming all three `src/soma/` roots and concluding *"the ownership ratchet covers none of
   `soma/`"* — and it is the one document the sweep left saying "broken".

**And `CLAUDE.md` §5 is now stale by this wave's own work.** The paragraph beginning *"And there is
one live boundary on it"* states that an ablated morphology cannot round-trip that seam, that
`conditioned_rest.rs` refuses such a body at the seal with a negative control, and that lifting it
needs `from_founded_stems`. The lift is done (§3.1); the refusal now fires on populations no
founding could have produced, and the negative control is those.

---

## 7 · Joins that could not be made, with their exact obstruction

These are the findings. Each is a cut that stayed open, and each names *why* rather than reporting a
count.

| join not made | exact obstruction |
|---|---|
| **`generate_currents` executor twin** | It crosses **no Swing event at all.** Independently verified without consulting the record: `awk 'NR>=701 && NR<=931' soma/life/src/morphological_language/ecology.rs \| grep -n "receive_with\|ResonanceEcology\|LiveCurrentMachine\|Executor"` returns only `witness.materialize()`, a pure host struct method. Mounting a card on the generation **frontier** is not a threading problem — it requires changing what a state-expansion *is*, plus an interchange proof for the material. |
| **`condition_route_partition` executor twin** | It is the body of a `std::thread::scope` spawn (`causal_language.rs:760-763`); N concurrent spawns cannot share one `&mut dyn LiveCurrentExecutor`. Lawful, because the executor-crossing twin exists one level up at `condition_route_receivers_with_executor:803`. |
| **a library consumer for `spine_cut`** | `grep -rn "spine_cut\|read_the_chain\|name_the_cut" --include='*.rs' crates/ soma/`, excluding the module and its driver, returns **one line**: `crates/holonic-engine/src/lib.rs:275: pub mod spine_cut;`. No library module calls the classifier. The organ has a mouth and a driver and no downstream. Building one would be a new organ. |
| **a circulation longer than a bigon** | `ride_circuit`'s holonomy is exactly `w(out) − w(back)`; a two-arc loop carries nothing the two arc weights do not already carry. A circulation returning something neither arc carries needs a cycle of length ≥ 3, and **no organ rides one** — `contact_triangles` reads triangles but nothing integrates around them. A general circuit over a declared vertex sequence is a new organ. |
| **a library caller for `induced_placement`** | Still none. And by §5 the class-side call returns `RealizerSupport`'s own numbers, so a caller would need to want `ker(MMᵀ)`, which requires a public exact null-space mouth — see the `pub(crate)` finding in §5. |
| **the Fano point sub-form** | Deliberately not wired, and the reason is the finding. Extracting the 7×7 point sub-form *is* circulant — but it is `−2·I`, circulant under **every** ordering, so its acceptance would be tautological under §8. The builder reported the reason instead of counting the matroid. That is the correct call and is recorded as one. |
| **`returned_reading.rs:354 carried_into`** | The same renumbering species as §3.1's `receive_whole`: it rebuilds a standing morphology through `from_founded_words`, so it would close an ablated body's gap. It is on a conduct path (`:1075`, `condition_again`). **Not a live defect today** — `grep -rn "ConditionedAgain" --include="*.rs" crates soma \| grep -v returned_reading.rs` returns **zero output, exit 1**, and nothing seals a `carried` morphology. But `canon/THE_HOLOBROCHOS_SPINE.md:346` names routing `returned_reading` through the seal as owed, and doing that makes this reachable. Lifting it needs the same shape as the `receive_whole` rewrite. |
| **green `output-manifest` / `closure-manifest`** | Both would go green in one command; both would content-address parallel sessions' half-finished work. Refused deliberately, with `0 departed` recorded. Not an obstruction in the code — an obstruction in the tree. |
| **a tracked `meta/HOLONIC_DSA_BASELINE.tsv`** | Untracked, so `architecture-lint` does not yet reproduce from a fresh clone. Required by "do not commit", not a defect. |

Two further limits belong here, both stated by their own builders:

- **`MorphologyNotRefoundable` is now a regression guard, not a live gate.** `from_founded_stems`
  returns the population verbatim or refuses, so no *material* reaches that comparison — its material
  is the constructor. The live refusal moved to `NotAFoundedMorphology`, whose material is the wire
  and the serde mouth, and both are driven. Labelled rather than deleted or pretended live.
- **`from_founded_stems`'s headline is looser than its evidence.** It reads *"every population no
  founding could have produced is refused"*, evidenced by 4 of 4 forged wires. The verifier admitted
  a 3-stem population with `id = u64::MAX` and correct chain parents — no founding could produce
  that. Not a code defect: requiring identity-magnitude reachability means requiring contiguity,
  which is the exact thing that had to be relaxed. Honest headline: *every population that is not a
  founded chain is refused by its own name.*

---

## 8 · Owners

Everything below was read at the line, with its file's `#[cfg(test)]` boundary located, before it was
graded.

| owner | what it carries | conduct path |
|---|---|---|
| `crates/holonic-engine/src/spine_cut.rs:239` | `read_the_chain`; residual computed at `:270`, not a parameter | yes, `#[cfg(test)]` at `:341` |
| `crates/holonic-engine/src/supported_realizers.rs:326` | `induced_placement`; docstring corrected to name the class space | yes, `#[cfg(test)]` at `:332` |
| `crates/holonic-engine/src/matroid_chow.rs:1377` | `cyclic_generator_receiver` | yes, `#[cfg(test)]` at `:1859` |
| `crates/holonic-engine/src/winding_inertia.rs` | `CyclicReading`, `read_cyclically:297`, `cyclic_receiver_of_form:813`, `extend_cyclic_reading:851`, five named refusals | yes, `#[cfg(test)]` at `:1665` |
| `crates/holonic-engine/src/contact_gluing.rs:546-608` | `ride_circuit`'s return read off the traversal | yes, `#[cfg(test)]` at `:641` |
| `crates/holonic-engine/src/conditioned_derivation.rs:313, :332` | `from_founded_stems`, `refoundable`, `FoundedMorphologyRefusal` (11 variants) | yes, `#[cfg(test)]` at `:2010` |
| `soma/life/src/conditioned_rest.rs:172, :252-262, :303, :349, :430` | `refound` through the new seam; `seal` gates twice on two views; `receive_whole` no longer renumbers | yes, `#[cfg(test)]` at `:717` |
| `soma/life/src/agentic_language/ecology.rs:775, :810, :1026` | three executor twins | yes |
| `soma/life/src/agentic_language/answer_continuation.rs:493` | `prepare_answer_with_executor`; the non-executor wrapper deleted | yes |
| `crates/holonic-architecture-lint/src/lib.rs:23, :36, :203` | `BASELINE_PATH`, rebased `PROTECTED_ROOTS`, `unresolved_protected_roots` | yes |
| `tools/gates.sh` | eight gates, one summary line each, `--control` fails each on purpose | shell |

**Drivers, all re-run by this session at `d3dc9c3`+dirty, all exit 0:**
`crates/holonic-engine/examples/the_cut_is_named_on_real_material.rs`,
`…/the_realizer_places_itself.rs`, `…/the_matroid_names_its_windings.rs`,
`…/the_circuit_closes_and_the_face_superposes.rs`,
`soma/life/examples/the_answer_crosses_the_mounted_carrier.rs`,
`soma/life/examples/the_ablated_body_rests_and_remounts.rs`.

**Gates, re-taken by this session and carrying their tree state.** The working tree is
`d3dc9c3` **plus this wave's uncommitted work** across 18 modified and 8 untracked files, so none of
these figures is a property of a commit and none may be cited as one:

```
cargo test --workspace -j 2   2015 passed, 0 failed, 14 ignored, summed over all 42 `test result:` lines, exit 0
tools/authored_levels.py      0 failures; 207 authored numeric levels (ABI 194, APERTURE 6, MATERIAL 7)
tools/resolve_named_paths.py  0 failures; 43 documents; 1360 path tokens, 1118 live
tools/gates.sh                5 passed, 3 failed (output-manifest, closure-manifest, architecture-lint)
```

---

## 9 · What this does not establish

- **It does not establish that the wave made the machine faster, or that any join changed a
  return a caller can measure.** §3.2 is explicit: the answer is required to be bit-identical.
  §3.4 is explicit: the split provably cannot move. §5 is explicit: the class-side call returns
  numbers already owned. **Two of the six conducting joins moved a return no organ could produce
  before** — §3.1 (an ablated body can be sealed at all) and §3.3 (the ratchet covers 77 `soma/`
  files it covered zero of). The rest made a passage *expressible* or made a defect *visible*.
- **It does not establish that the cut classifier distinguishes five species in the material.** §2
  shows each cut is contributed by exactly one driver-built family and two of the five are forced by
  construction. What is established is that the accumulation rule is a live gauge over 516 named
  loops.
- **It does not establish that the `-57` residual corresponds to `CLAUDE.md` §0c's `residual 57`.**
  That correspondence is asserted by prose and computed by nothing.
- **It does not establish scale.** Every driver runs on one frame of material. The contact-gluing
  driver's three frames are on the *walk* — argument order, direction, cochain — not on the corpus.
  `spine_cut` ran on one production; `induced_placement` on eleven conduct classes over four
  vertices. §11 of `CLAUDE.md`'s far-population demand is untouched.
- **It does not establish that `winding_inertia`'s searched cyclic reading is a lawful receiver.**
  It establishes that the split is invariant under it because the transport goes through
  `congruence`. Whether a receiver discovered by backtracking search is a receiver is a question
  this record poses and does not answer.
- **It does not license carrying `2015` as a capability figure.** It is one dirty tree at one
  clock time, and `CLAUDE.md` §0 forbids carrying a gate figure without its clock. Contributions
  are attributable per-session at most to the tests each added.
- **It does not repair the three document defects in §6.** They are named with their line numbers
  and left for the deposit that owns those files.
