# CLAUDE.md — holonics operating contract (Claude-facing)

Brandon's latest direct request governs.

**This file is the authoritative operating document for Claude, and it stands alone.** `AGENTS.md`
is the Codex-facing twin written for a different model; it is not authority here and is not to be
consulted as such. The same holds in the laboratory repository: its `AGENTS.md` prohibition on
reading `CLAUDE.md` was written for Codex, and the laboratory's own `CLAUDE.md` — the Standing Law,
the Objective, the Bans, the ratified Law/Cut/Bridge deposits — is the authoritative theory source
here. (Brandon, direct ruling, 2026-08-05.) The laboratory is frozen and dirty; read it only
through git, `git -C /home/b/Workspaces/laboratory show a07ff376:CLAUDE.md`. Never its working
tree, never a write.

Where a dated deposit inside the soma canon or the RESEARCH records refines a mechanism the
Standing Law states in compressed form, the refinement is evidence the Standing Law itself points
at, not a competing authority. Carry both and name the refinement.

The purity, ownership, apparatus, no-float, and grading requirements this project runs on are
stated below. They were first written for the archived C++ body in
`archive/blueprints/CPP_GPU_FOUNDATION.md`, which now carries an archive banner; the requirements survive
the body that occasioned them and this file carries them. They are meant to be enforced by
executable audits rather than by cross-reference — `cargo test --workspace` does enforce the
no-float and determinism gates, and `crates/holonic-architecture-lint` is the ownership ratchet but
**does not currently run**, for the reason `CONSTRUCTION_STATE.md` records.

This file is an operating contract, not a theory deposit and not a scheduler. It exists to prevent
the specific recurring failures observed across the Codex sessions of 2026-07-09 through
2026-08-05 and to preserve the corrections that closed them.

## 0. Fresh-session pickup — the spine

**The body is Rust.** The C++/CUDA engine was archived whole on 2026-08-07 at Brandon's direction
after a comparative audit. It lives at `archive/cpp-engine/` and nothing there is authority. Sections
below that speak of headers, deeds, `ctest`, CUDA executors or `R{i}` chains describe that archived
body and are **provenance**, not the present position.

Read these seven, in order, and nothing else by default:

| file | what it is |
|---|---|
| **this file** | the operating contract. How to work, what is convicted, what is authorized. |
| `canon/THE_HOLOBROCHOS_SPINE.md` | **the spine — the whole hollow loop.** Two loops, four flows, the two moves that run on them, the three laws, and where every live organ sits. **The roadmap is ordered by it.** Read it before proposing any construction; an organ that no station names is churn. |
| `canon/THE_DOCUMENT_LAW.md` | how a claim travels from conversation to canon, the genres, the grades, how supersession is recorded. |
| `canon/THE_QUOTE_NETWORK.md` | **where every idea came from, in Brandon's words**, themed, with "where this lives now" per theme. Read this before theorising about what he wants. |
| `canon/THE_MEASURED_CAPABILITIES.md` | **the evidence index: what the machine has actually done**, from 96 binaries run rather than read. Seven operations, seven causal mechanisms, the bounds, and the unrecoverable figures that may not be cited. Read this before proposing construction — most of what looks unbuilt is built, undriven, or blocked on one missing input file. |
| `blueprint/THE_ROADMAP.md` | the single active roadmap. **The open work is stated by station** at the top; everything below that is the returned ledger and its provenance. |
| `CONSTRUCTION_STATE.md` | the position record. What is admitted, what survived the transition, what must be re-established. |

**The spine is new to the live canon as of 2026-08-08 and the reason it was missing is worth
carrying.** The concept — `holo` ⊕ βρόχος, *the whole hollow loop*, the laboratory's unification of
Information Theory and General Relativity — was derived 2026-06-17 and **no live document contained
the string**. Every live blueprint described a *cabinet of organs*, and a cabinet cannot state the
central defect, which is not a missing organ but a **missing edge**. Brandon named it directly:

> *"this is 'holobrochos', you need to outline the spine of the machine and understand how all of
> the loops and machinery connects and choreographs information transportation."*

**Eleven blueprint documents moved to `archive/blueprints/` the same day.** They already carried
archive banners; `blueprint/` now contains only documents in force, and
`archive/blueprints/ARCHIVE_BANNER.md` says what each was and what replaced it.

`canon/THE_RECOVERED_LAW.md` carries the jurisdiction doctrine and the elementary definitions;
consult it before claiming anything about what holonics forbids.

**Twelve files carry an archive banner and schedule nothing.** Under `blueprint/`:
`archive/blueprints/THE_ORDER_OF_WORK.md`, `archive/blueprints/THE_SPINE.md`, `archive/blueprints/THE_FOUNDATION_REMAINDER.md`, `archive/blueprints/THE_GROWN_CIRCUIT.md`,
`archive/blueprints/EROS_EMBODIMENT_ROADMAP.md`, `archive/blueprints/EROS_MATHEMATICS_PRODUCTION_FLOOR.md`,
`archive/blueprints/COMPLETE_CPP_ENGINE_ROADMAP.md`, `archive/blueprints/CPP_GPU_FOUNDATION.md`, `archive/blueprints/THE_SPINE_THE_CUT_AND_THE_TERRAIN.md`,
`archive/blueprints/BUILD_AND_GRADE.md`, `archive/blueprints/REALIZATION_AND_HARDWARE.md`; and
`archive/cpp-engine/CONSTRUCTION_STATE.md`, the C++ body's position record. Read them for history,
never for direction. The banner is the test: if the file opens with one, it is provenance.

**Every path a governing document names must resolve in the body that document describes.** That is
`canon/THE_DOCUMENT_LAW.md` §4, and it is checkable:

```
python3 tools/resolve_named_paths.py
```

An archive-bannered document may name archived paths; a live one may not. Run it after editing any
document at the root, in `canon/`, or in `blueprint/`.

### The workspace

```
crates/   holonic-structure  substrate: ordinal and relation atlases, local populations,
                             branch lineage, typed atomic membrane
          relational-geometry exact projective geometry over BigRational, Sturm-certified roots
          holonic-engine     the receiver-relative geometry and physics body, ~95k lines,
                             float-free, no Bevy, no wgpu, two hand-written CUDA kernels
          holonic-language   the reflective runtime: reify, absorb, resume
          holonic-architecture-lint  the monotone ownership ratchet
soma/     body               pure law, no_std, zero dependencies
          membrane · abi · surface · mount · life · tools
          kernel/soma.spv    committed boundary artifact; its toolchain is excluded
```

**Measured 2026-08-09 at `532ea1b`+1:** `cargo test --workspace` **1,732 passed, 0 failed, 14
ignored**, summed across 42 `test result:` lines. (Earlier: 1,701 at `fa0f92d`; 1,545 on 2026-08-08
19:27 at `101882f`; 1,512 at `d91720e`; on 2026-08-07 14:34 it was **730**.) Earlier the same day it was `543 passed, 1 failed` on a `mount-scope-gate` radiation fixture
that had never been regenerated across ten commits to `body::carriage`; that fixture was refounded
against the law rather than the receipt. **Do not carry a gate figure without its clock time.**
`CONSTRUCTION_STATE.md` is the position record and re-taking the number is one command.

Build with `PATH=/opt/cuda/bin:$PATH`; `holonic-engine`'s build script shells out to `nvcc`.

### The objective, in Brandon's words

> *"a machine that can rigorously perform and analyze computations using internal machinery that
> accomodates transport mechanisms between arbitrary charts, the learning is the intermediary
> mechanism/law/equation"*

and the umbrella it sits under:

> *"the 'Universality Machine', which is an umbrella term for a machine that can relate arbitrary
> informants in simulated ecologies, where holonics is a framework that encapsulates
> interdisciplinary features of mathematics, physics, and computer science because they are all
> related and generalize to everything."*

**Never name work by an ordinal.** `R14`, `Phase 7`, `CUT 3` carry no capability and Brandon has
corrected this repeatedly: *"I do not want to attribute capabilities and version numbers to the
phases or the numbers you associate with the build, because then you eventually start to refer to
the numbers like facts instead of using proper semantics."* Name the mechanism.

### What the archived body is worth

**WITHDRAWN 2026-08-08 by running the driver.** This read: *"One thing it had that this body does
not: the conditioned production shape — two theorems, kernel-refused foil, structural ablation —
which C++ ran at three declarations… It is a port that is owed."* It is not owed.
`soma/life/examples/eros_lean_proof_production.rs` runs all three against a real Lean toolchain
(`lake env lean` in the loop): 39 declaration organs, 31 paths, **9 kernel-admitted, 22 obstructed
with verbatim errors**, structural ablation taking admissions **9 → 3**, and a 34,628-octet detached
remount that reproduces the family. C++ ran it at three declarations; this body runs it at
thirty-nine.

**The archive is now worth exactly its four lessons and nothing else.**

It was also credited with a second, the certified exact enclosure carrier at
`archive/cpp-engine/src/include/holonics/exact/enclosure.hpp`. **That credit is withdrawn
2026-08-07:**
the certified exact enclosure carrier has a live Rust owner at
`crates/holonic-engine/src/exact_value.rs`, and the Rust form is the stronger of the two — exact
rationals rather than dyadics, a four-state ordering with `Open`, a Sturm isolation certificate, and
a three-species tail certificate returning an exact rational remainder interval. §11 carries the
measurement. Nothing needs porting there; what the carrier needs is a driver.

And four lessons, each earned by a defect found in it:

- **Bind every deposit to its content hash AND its closure hash, with a verifier.** The laboratory
  lost its tiger figures and the file holding `semantics_invariant_under_exact_chart` to an
  untracked `runs/`. Neither is recoverable at any commit in either repository. The registry that
  would have prevented it is archived (`closure_sha256` resolves only under `archive/cpp-engine/`)
  and has no Rust owner.
- **No absolute frame in a lineage.** Ten C++ card adapters folded the filesystem path into the rest
  integrity, and one deed asserted that dependence as its own success condition.
- **A negative control's absence is evidence, not an unbuilt output.**
- **An invariant is only visible across two frames.** Every contaminant found in two days was a
  receiver-visible coordinate promoted into an invariant — an accepted-count into morphology, a mount
  point into standing, a solver's pivot order into a reduction, one card's literals into an admission
  rule. Each returned consistently until the frame moved. A machine with one frame cannot audit
  itself, which is why the instruments that join partials outrank perfecting any organ.

## 1. The floor is a carrier, not a retired interface

**The single most damaging defect in the inherited authority was an admission rule that made the
established floor inert.**

`archive/blueprints/EROS_MATHEMATICS_PRODUCTION_FLOOR.md` §10 declared a deed inadmissible if its primary grade is
any already-established capability, while §9 listed only Millennium-scale or
research-infrastructure targets as open. The composition of those two rules is a deadlock, and
`CONSTRUCTION_STATE.md` recorded its consequence directly: *construction remains paused*.

The correction is a distinction the inherited rule collapsed:

- **The grade of the organ is not the grade of the return.**
- An established capability is admissible without limit as the **carrier** of a deed.
- It is inadmissible only as the **return** of that deed.
- A deed that conducts through standing organs and returns a fiber, obstruction, classification,
  counterexample, or proof that was not previously owned is admissible, and demanding that it
  also re-found its carriers is exactly the re-establishment the floor forbids.

Restated in the project's own doctrine: the floor is **standing**, and standing is what later
current threads. A condensation that refuses every future receiver family is not a floor; it is a
retired interface, and retired interfaces are refused. Parent-on-open return and retained-fiber
reopening apply to the project's own authority files, not only to its runtime.

## 2. Realization causes placement

**Truth status:** `interpretation` for the general reading; `proved-standard` for the
function-field instance it generalizes from.

This is the governing synthesis of the mathematics and the learning work, and it replaces the
"two halves" framing.

In the one setting where both faculties are settled — a smooth projective curve over a finite
field — spectral placement is **derived from** supported realization and not obtained beside it:

```text
an ample divisor class            (a supported realizer — a FOUND that paid)
  -> a polarization
  -> the Rosati involution on the correspondence algebra, which is POSITIVE
  -> positivity of the trace form on correspondences (Castelnuovo / Hodge index)
  -> |alpha| = q^(1/2)             (placement, as a RETURN)
```

Purity is then the statement that the duality involution coincides with complex conjugation:
`alpha_bar = q/alpha`. That is the same shape as the multiplicative seam already recorded in the
laboratory's Weil cut — the critical line is `Fix(J)` for the anti-linear `J(z) = -z_bar`, and a
transport is norm-preserving exactly on that fixed locus. **Placement is the fixed locus of the
involution that a realizer induced.**

Three consequences govern construction:

1. **Do not build modal placement and supported lifting as two organs.** Derive placement from
   realization. A returned placement that no realizer paid for has smuggled an absolute frame into
   the engine; that is the half-rank razor firing at the level of architecture.
2. **The classically missing object is not a self-adjoint operator.** Hilbert--Pólya asks for the
   placement directly. The framework's own ontology asks for an **ample class** — a realizer whose
   **positivity is supplied by AMPLENESS** — from which the involution and then the placement
   follow. This is a materially different search target and it is the one this project pursues.

   **Corrected 2026-08-08, and the correction is not pedantic.** This section said *"positivity is
   supplied by supportedness"* until a Hodge audit falsified it. `Eff ⊋ Amp`: a `(−1)`-curve on a
   surface is **effective** — realized by an honest subvariety, perfectly supported — and has
   `E² = −1 < 0`. Effectivity supplies nothing; ampleness supplies everything, and the strictness of
   that inclusion is where the entire theory lives. The correct slogan is **"positivity is supplied
   by the choice of a polarization, which is a *positive* realizer, and only a positive realizer
   pays."** The Rosati proof makes it explicit: `Tr(αα†) = (2g/(L^g))·(L^{g−1}·α^*L)`, positive
   because `L` is **ample**.

   **And the chain omits one input.** Positivity of the Rosati involution gives only that `†` is
   complex conjugation on `ℚ[π]`. Converting that into `|α| = √q` needs the **Frobenius
   `q`-symmetry `π†π = q`**, which holds because `π^*L ≅ L^{⊗q}` — a property of the *map*, not of
   the polarization. Carry both:

   ```text
   ample class → polarization → Rosati † positive → † is complex conjugation on ℚ[π]
                                                  ⊕ π†π = q          (Frobenius q-symmetry)
                                                  ⟹ |α| = √q
   ```

   **Why there is one proved instance, stated properly.** The higher-dimensional Step 4 is
   **Grothendieck's Hodge standard conjecture**, which is a theorem in characteristic zero (it *is*
   HR2) and **open in characteristic `p` for dimension ≥ 3**. Deligne's proof of the Weil RH in
   general deliberately avoids this route entirely. The single instance is not modesty; it is a wall
   with a named open conjecture behind it.

   **The strongest evidence for this section's own thesis is a theorem nobody here has cited.**
   Voisin, IMRN 2002: there are compact complex tori carrying Hodge classes that are not in the
   ℚ-span of Chern classes of **any** coherent sheaf — no holomorphic object at all explains them.
   The Hodge conjecture is stated for *projective* varieties, and by Kodaira projective = Kähler +
   an integral **positive** class. Dropping exactly the ample realizer destroys the conclusion.
   *"Realization pays"* has a named counterexample proving it, and it is not the torsion story.
3. This is the same sentence as the Swing's own asymmetry at a different altitude. **FOUND pays
   curvature; RIDE is cheap because the terrain already paid.** Realization pays; placement rides.

Do not upgrade this correspondence to an identity, and do not use it to claim any Millennium
result. It is a construction-selection principle with one proved instance.

## 2b. A sign is a passage, never a state

**Truth status:** `established-bounded` for the mathematics; `interpretation` for the reading, which
is Brandon's and was derived with him 2026-08-08.

**The keystone, in his words:**

> *"Integration by **reflection** (lightning arcs; sphere packing) → Information Theory (Computer
> Science; holomorphic spaces; circuitry) + General Relativity (relativistic physics and
> mathematics)."*

### What negativity is

Holomorphically, `−1 = e^{iπ}`. There is no separate species of quantity called negative; there is
rotation, and `−1` is the half-turn. ℝ sees only the two fixed points of conjugation on the unit
circle, so a sign is **what remains of a phase after the winding is deleted**. That is the float
argument one level down: a float keeps the magnitude and discards the residual; a sign keeps the
magnitude and discards the turn.

His 2026-07-04 ruling states the rest, and it governs:

> *"it's actually not {0,1} for our purposes I don't think. It's combinations of possibilites where the quantum
> is between two choices. 2^x."* — and the record's reading: the quantum is **the fork**, not a
> state, and explicitly not `{±1}`-as-a-value, *"that would re-reify the state with a sign on it."*
> **What the signed floor signs is the PASSAGE, never the state: CW/CCW = the two hands through the
> fork.**

And `4 = 2·2` are **different currencies**: the octave (2:1, magnitude, one rank step) and the hand
(one quarter-turn, phase, costing no action). *"On the unsigned floor the phase factor is INVISIBLE,
so both factors were booked as magnitude."* Hence `√x = x^{2^{-1}}`: squaring doubles the argument, so
the `±` of a square root **is** the half-turn squaring erases, because `2(θ+π) ≡ 2θ`. The ambiguity
is not in the root; it is in the floor that deleted the phase which would have decided it.

### Measured, 2026-08-08, and this is the check

The cycle `C_n`'s adjacency eigenvalues are `2cos(2πk/n)`, one per star polygon `{n/k}` — the n-grams
on the same vertices, which is why a polygon cannot be had without them.

```text
  2cos(2πk/n) < 0   ⟺   2πk/n > π/2   ⟺   the step exceeds ONE QUARTER TURN
```

**The sign of an eigenvalue is the winding of its star polygon past the hand.** The triangle returns
inertia `(1, 0, 2)` — one zero-frequency passage and two that wind past the quarter — bit-identical
to what `crates/holonic-engine/src/inertia.rs` computes by pure elimination with no trigonometry
anywhere. And the null directions sit at exactly `k/n = 1/4, 3/4`, present exactly when `4 | n`:
**the form returns nothing precisely at the hand.**

### Inertia, re-derived as passages

The state reading — *"p directions are positive"* — is the reification the ruling above strikes. The
passage reading:

> `Q(v)` is what traversing `v` returns. The **null cone** `{Q(v) = 0}` is where traversal returns
> nothing. `p` is the largest dimension of a family of passages that **never crosses the null cone**,
> all returning the same hand.

Sylvester's law of inertia is then not a fact about positivity: **a change of basis relabels
passages; it neither creates nor destroys them.** The two cones cannot merge because you cannot pass
between them without passing through zero, and that is an event rather than a coordinate.

**So positivity is not absolute, and the correction is precise.** `A` and `−A` have swapped inertia,
so which side is called positive is a convention — a hand. Minkowski's `(+,−,−,−)` versus
`(−,+,+,+)` is a live convention that changes no physics. What no frame touches is **the split**:
that it is one against nine rather than five against five.

And the two sides are coupled, exactly as concave is to convex. A **definite** form has an *empty*
null cone — one side has nothing in it — which is a receiver inertially at rest, no vacuous
difference, no potential. An **indefinite** form has both cones with the null cone between them, and
**the null cone is the vacuous difference.** In Minkowski it is the light cone.

Superseded by this section: any statement that a form "is positive" as though positivity were a
property of the form rather than of a declared side. State the **split** and the **hand** separately.

### What it changes for RH and Hodge

- **RH for curves.** `Tr(αα†) > 0` for `α ≠ 0` says: **no nonzero correspondence self-pairs to
  nothing — the null cone of the trace form is `{0}`.** With `π†π = q` that forces `|σ(π)|² = q`.
  The open content is therefore *"does a passage exist in the cone"*, which is a **search for an
  object**, not a proof of a predicate — and searching is what this machine does.
- **Hodge–Riemann.** The sign is carried by `i^{p−q}`: **the hand is determined by which piece the
  class sits in and alternates across the pieces.** It is the fork, in the Annals.
- **The Hodge index theorem** `(1, ρ−1)` is the coupling as a theorem. You cannot have the ample
  direction without the negative complement; a `(−1)`-curve's `E² = −1` is the necessary other side,
  not an awkward case.
- **The integral failure.** Kollár: `pα` algebraic, `α` not — **the passage exists at multiplicity
  `p` and not at 1.** That is winding that cannot be un-deposited, and it is why
  `ObstructionSpecies::ReachableOnlyInMultiple { factor }` is the faithful model.

### The standing obligation this creates

**A count of signs is a state reading. Name the windings instead.** Where a form carries a cyclic or
circulant symmetry its inertia factors through the character group and every negative direction has
a name — its winding number — so the lawful return is *these nine passages, each labelled by how far
it winds*, never *nine negative directions*. `inertia.rs` computes the split correctly by elimination
and does **not** yet name the passages. That is owed.

And the audit this implies, which nobody has run: **every bare sign stored on a conduct path has done
what a float does.** Find each `-` that is retained state rather than traversal and ask whether the
turn that produced it was kept.

## 3. The Millennium problems are on the path

RH and the Hodge conjecture are not distant hard problems this project drifted toward. They are
where the framework's own primitives land, and treating them as out-of-scope is a failure mode,
not caution.

- **RH is the landmark law.** Prime founding *is* the machine's RIDE/FOUND primitive over
  succession and multiplication: trial transport against every founded axis to the square-root
  frontier, closure marks composite, exhaustion FOUNDS a new axis which becomes later terrain.
  Lawful navigation with no privileged frame requires the landmark field to be unbiased at every
  scale, and the half-rank error term is exactly that unbiasedness. The `1/2` is one fact with
  three faces: the rebase unitarity weight `dx <-> dx/x`, the saddle's equipartition `p^(-m/2)`,
  and the cut's diffusion exponent. The critical line is the unitary seam, not a singularity.
- **Hodge is the realization law.** It asks whether a receiver-visible invariant subspace has
  enough supported geometric realizers. The failure of the *integral* version is the framework
  speaking — but **not in the way this section said until 2026-08-08, when a Hodge audit falsified
  it.** The claim was *"the obstruction is torsion, and torsion is winding that cannot be
  un-deposited."* There are **two independent families of counterexample** and only one is about
  torsion:

  - **Torsion.** Atiyah–Hirzebruch 1962, sharpened by Totaro 1997 and Soulé–Voisin 2005. And even
    here the obstruction is not torsion itself — it is the vanishing of odd-degree stable cohomology
    operations, `Sq³_ℤ = β∘Sq²∘ρ` first, then a complex-cobordism obstruction strictly stronger than
    that. Torsion is the *habitat* of these obstructions, not the obstruction.
  - **Non-torsion.** Kollár 1990/1992: a very general hypersurface `X ⊂ ℙ⁴` of degree divisible by
    `p³` has every curve's degree divisible by `p`. Here `H⁴(X,ℤ) ≅ ℤ` is **torsion-free**, the
    failing class has **infinite order**, and `pα` is algebraic while `α` is not. The cokernel is
    `ℤ/p`.

  **The uniform statement is that the obstruction lives in the COKERNEL of the cycle class map.**
  Torsion *in the cokernel* is not the same as the failing class being torsion, and this section
  collapsed the two. Note also that a torsion class is automatically a Hodge class — its rational
  image is zero — so the naive integral statement asks about a part of `H^{2k}(X,ℤ)` that Hodge
  theory does not constrain at all.

  **And the one place the record was missing a win:** the integral Hodge conjecture is **TRUE in
  degree 2** — the Lefschetz theorem on `(1,1)`-classes gives a **ℤ**-linear combination of
  hypersurface classes. Degrees `0`, `2` and `2n` are the only cases where it holds integrally.
  That is this project's own thesis as a proved integral theorem and it belongs in the record.

Neither is claimed, admitted, or scheduled as a result. They are the correct receiver questions
for the organs being built, and a deed may be graded by movement on their **named substructure**
without claiming the conjecture.

## 4. Do not treat mathematics as a separate track

Mathematics, language, perception, acoustics, atmospheric physics, and code are not domains this
project alternates between. The mechanism under study is transport and navigation of information
across changing charts; every domain is a different **material** carried by the same operation.
Sustained attention to mathematics is depth on the operation, not a change of subject.

**Anti-scatter discipline.** When Brandon pivots to an analogous instance in another discipline,
that is the framework's normal mode of exposition, not a digression — the claims are about the
operation, which has no privileged domain, so every illustration must change material. Do not
treat the currently live domain as the subject. When receiving or producing such a pivot, name the
same four slots:

```text
source geometry  ->  receiver map  ->  transport  ->  returned residual
```

Lightning, primes, binaural returns, Hodge classes, suffix frontiers, and Frobenius are that one
form with different material. If the four slots are named, the material is visibly the variable
and hyperfixation on it is not available.

## 5. Credit the established learning floor

The laboratory established a working, non-statistical learner. Under-crediting it caused repeated
re-demonstration of standing capability. The following are `established-bounded` with
`implemented-exact` and, where cited, `measured` evidence. **None of them is a construction
target.**

- **Conditioning and generation without a distribution.** Exact suffix ecology on the full corpus:
  11,879 states, 427 generated branches of which 336 complete outer prefixes were never received,
  every branch re-entered as self-emanated lineage, delivery-gauge rest, exact remount. Then
  4,051 feature-receiver rests compiling 22,459 continuations with no corpus scan and no router;
  the absent-morphology control emitted nothing rather than fabricating.
- **Training with a behavioral ablation — REGRADED 2026-08-08 by reading the owner, and the citation
  moves.** The `9*8` / `7*9` receipt was carried here for weeks without anyone opening the code. Its
  owner is `src/soma/life/src/symbolic_reasoning.rs`, and four things are true of it:
  the trained *content* is authored, not corpus-derived — `AutonomousLeaderSpec` carries `&'static`
  literal probes `"3 * 4"` and `"7 * 6"`, and the 50,667-occurrence corpus contributed only glyph
  counts that decide *whether* a family fires; the ablation is construction-by-omission, since
  `mounted` is a separately built body that was never exposed and `drop(corpus)` is source
  *departure*, not removal; the arithmetic is **mounted**, computed by the inherited rational
  normalizer, so training gates *admission* and not capability — `63` for novel `7*9` evidences a
  retained admission gate surviving detachment, which is real but narrower than "the trained body
  returned 72"; and the record's own successor says so, *"it did not train the inherited exact
  operator laws or the mounted articulation transducer."*
  It is also **deleted**: `a07ff376` is the commit that removed it, along with `continual_reasoning.rs`
  and both drivers. It survives only at `93834398`, and `runs/` was never tracked, so the 50,667
  receipt is unrecoverable.
  It is still better than the C++ restatement withdrawn 2026-08-06 — there, `product_route()` was
  nullary and `constexpr`, one constant twice, and no operand pair reached the ecology at all; here
  two genuinely different operand pairs cross the parser and the exact normalizer.

  **What stands in its place, live at `a07ff376` and stronger, is where the citation now points:**
  `src/soma/life/src/holonic_training.rs` (`TrainingEcology`, 1,387 lines), whose structure is
  *derived from the occurrence* rather than authored — `consequence_complex` → `derive_templates` →
  **`predict` before mutation** → `ConsequenceRelation::{None, Ride, OpenIncluded, OpenResidual}`,
  with a contradicting later return graded `OpenResidual` rather than "incorrect", and
  `:567` *"Receiver parameters do not assign a scalar score."*
  And `src/soma/life/src/agentic_language/tests.rs:656`, which is the sharpest demonstration in
  either repository: the first returned correction changes no conduct, the second does
  (`CODEC_MINIMUM_RECURRENCE = 2`), a novel third surface never supplied is emitted carrying
  `version_lineage` naming both causing returns, the detached training bytes alone predict a fourth
  novel name, and a full remount emits a fifth.

  **Three ablation shapes are measured; a fourth does not exist anywhere.** Construction-by-omission
  (four probes, zero candidate paths). **Receiver-axis withholding** — withholding the `language`
  axis takes `agreement_rank` 3 → 2 and complete paths 1 → **2**, so *withholding structure
  increases plurality* rather than decrementing a number; this is the shape to imitate.
  Reference-vs-return (`bit_causal.rs`: inspecting a reference leaves the rest image bytewise
  unchanged).

  **The fourth — deleting a founded fiber and re-querying — WAS said here to have no implementation
  anywhere. That is false of the body, and corrected 2026-08-08.** It exists as
  `FoundedMorphology::without_stem` (`conditioned_derivation.rs:352`) and
  `ConditionedBody::without_stem` (`:1362`), and it is driven **with both controls** at
  `derivation_codec_intake.rs:1250-1300`: a committed stem the material never exercises, whose
  removal must leave the reading **indistinguishable**; and then, *in canonical order rather than
  chosen*, the first reaching stem whose removal **moves** the reading, required to exhibit the
  distinguishing word. Also driven at `examples/foreign_codec_intake.rs:805,833`.

  **The claim was an artifact of its own grep.** The pattern was
  `fn remove|fn forget|fn prune|fn ablate`, and the owner is named `fn without_stem` — a word the
  pattern could not match. An absence claim is a measurement and decays like one; this one was
  false on the day it was written.

  **And it is driven in FOUR places, measured 2026-08-08 by running them:**

  | driver | what was deleted | what departed |
  |---|---|---|
  | `conditioned_derivation_body` | a founded stem, then re-ask | conditioned licenses 105 named passages; unconditioned **0 stems, 0 passages**; 18 controls |
  | `eros_lean_proof_production` | declaration organs | `39 → 38` organs, `31 → 14` paths, **`9 → 3` kernel-admitted**; 6 admitted proofs named and lost |
  | `derivation_holonomy` | the 7 artifacts declaring `formal_carry` | circuit W winds with `residual 57`; circuit E **exact** after the ablation |
  | `eros_mathematics_conditioning` | whole corpus documents, all fourteen in turn | passage population moves as a **population**, appearance not departure |

  **What remains true, narrowly:** no deletion primitive exists on the `soma/life` **training**
  owners — `holonic_training.rs` and the language ecologies — which is the scope the grep was
  actually run over. So §13 rule 1's strict form is **owed on the training body and already met on
  the conditioned-derivation morphology.** State it that way; do not restate the general form.

  **And `eros_lean_proof_production` is the conditioned production shape §0 says only the archived
  C++ body ever ran.** It shells `lake env lean` in the loop against a real toolchain: 39 declaration
  organs, 31 paths, **9 kernel-admitted and 22 obstructed with verbatim Lean errors**, a structural
  ablation that takes admissions `9 → 3`, and a **34,628-octet detached remount that reproduces the
  family**. Two theorems, kernel-refused foil, structural ablation — all three, live, in Rust.
  §0's *"one thing it had that this body does not"* is **withdrawn**.

  **And there is one live boundary on it**, found 2026-08-08 by building the rest wire:
  `without_stem` retains the surviving stems' original `StemId`s, while `from_founded_words` —
  the only foreign constructor — *derives* ids from arrival order. An ablated morphology therefore
  cannot round-trip through that seam, and `soma/life/src/conditioned_rest.rs` refuses such a body
  **at the seal, by name, with a negative control**, rather than sealing something it cannot
  reproduce. Lifting it needs `FoundedMorphology::from_founded_stems(Vec<FoundedStem>)`.
- **Multimodality with no fusion module and no pair product.** RELAMPAGO: optical, five-band
  spectral, geolocation, and vertical sections on one eighteen-coordinate phase face; 24,584 and
  21,147 relations opened with zero pair overlap and the complete pair product never enumerated;
  14,355 relations generated before return; no-return control entirely OPEN; reversed delivery
  prediction-exact; 31.4 MB standing remounted exactly.
  **Bounded, 2026-08-07, and this bound belongs with the claim rather than in a separate errata:**
  `canon/THE_RECOVERED_LAW.md` records that **all 21,147 spectral pairs returned apart** — zero
  positive relations came from the second modality. What stands is that relations were *opened*
  across modalities with zero pair overlap and no fusion module; what does **not** stand is that the
  second modality contributed a positive relation. Read as "multimodality established," this
  paragraph overstates its own evidence.
- **Receiver-relativity on measured physics.** Aula Carolina binaural: both 159,792-sample impulse
  returns exact, two modes generated before return, each ear selecting its own mode by zero
  residual while obstructing the other.
- **Formal mathematics from a detached body.** 1,164 source-free declaration organs; codec-only
  body could not recruit the held-out theorems, the trained detached body could; 86 one-organ
  paths returned as obstructions, causing 84 pairwise compositions, of which the kernel accepted
  exactly two.
- **Continual restriction as inference.** `114300 -> 1440 -> 6 -> 3 -> 1` through four returned
  observations, then all three exact calculations emitted.
- **Reflective revision with lineage.** Corrections founding parented codec versions, both
  retained, and unsupplied sentences generated after rest and source departure.
- **The clean body's mathematical production.** Two kernel-accepted theorem passages with the
  second depending on the first's returned fiber under exact ablation; blind reconstruction of
  unfamiliar published characteristic mechanisms before post-seal comparison; independent
  derivation of an elementary holonic calculus from anonymous numeric ecologies; and the
  source-separated discovery of the rank-three trace-coordinate generator action with its exact
  Jacobians, tangent transport, and deck involution.

**There is one named open construction here, and it was miscarried as a wall until 2026-08-08.**

Across `0/127/254/508/1009` dialogue occurrences the deed, minimal witness, five leaders, two waves,
and thirteen visits stayed invariant. **Consequence isolation is established.** That half stands.

The other half — *"scale-independent recruitment does not"* — was **withdrawn 2026-08-08** after
Brandon challenged it as imposed and the source was re-read. It is wrong in four ways, and the
source record refutes it directly:

- **It is false on its own terms.** What recruitment *returns* is already scale-independent: **40
  return visits at every nonzero scale**, unique returns `25 / 27 / 27 / 24` — non-monotonic, and
  *lower* at the largest corpus. What grows is the candidate **sweep**, not the recruited return.
  The sentence names the returned quantity and reports the swept one.
- **The source disclaims the scaling claim.**
  `research/records/2026-07-31_THE_PREFIX_GROWS_THE_DEED_RETAINS_ITS_WITNESSES_THE_LEXICAL_STAR_REMAINS_TOO_BROAD.md:136`
  — *"The measured work is sublinear over this range, but it is not constant and **this bounded run
  does not establish an asymptotic class.**"* Wall-clock grew **×1.33** against **×4.44** in
  sections. Four points, with visits at ×5.02 against sections at ×4.44 — a ratio of 1.13 — cannot
  separate linear from `n log n` from `n^1.05`.
- **It inverts a refusal into a finding.** The record at `:197` says *"The stronger claim that
  recruitment is already scale-independent is false"* — a bar on asserting it, not evidence for its
  negation.
- **It misfiles a correctness defect as a scaling one.** The record at `:216` states the precise
  issue and it is **not** about scale: *"broad union-based lexical recruitment followed by
  **commitment-before-witness**."* 24 passages conditioned persistent morphology though none
  belonged to the minimal witness family. That is wrong at 127 occurrences as much as at 1,009.

**Corrected again, same day, after actually reading the laboratory.** An earlier form of this
paragraph said the two remedies were "an unimplemented formula" and cited a `MinCover` grep
returning zero in *this* repository. That was archaeology on a July record instead of a look at the
body that ran it, and it is wrong twice over.

**Both remedies exist as working laboratory code**, one layer away from where they were wanted:

| remedy | owner at `a07ff376` |
|---|---|
| factor the receptive star, `I(R) = ⋃_K ⋂_{f∈K} I(f)` | `src/soma/life/src/relational_language/ecology.rs:1362` `clause_region_incidence` — the intersection form, with the cover founded on the receiver's own clause and entity morphology exactly as demanded, never inverse frequency. Plus `morphological_language/ecology.rs:437`, which falls back to the union when an intersection is empty, so a single-feature alternative stays lineage rather than being declared false. |
| provisional contact ≠ continuing cultivation | `src/soma/life/src/holonic_training.rs` — `propose_views` / `commit_views`, generation-checked and refused intact if another return moved the generation first; with `minimum_recurrence ≥ 2`, so a route is retained but inactive until it recurs across **distinct** occurrences. And `src/soma/membrane/src/live_holon.rs:204` `ProvisionalSettlement`, a two-phase prepare/commit primitive. |

**And the laboratory withdrew the framing itself, twice, before it froze.** 2026-08-01: *"This is not
evidence that broad recruitment should be reduced."* 2026-08-02: *"Broad recruitment remains
lawful."* Brandon, 2026-07-29, ruling directly: *"Do not remove chronology. Let informants couple
through the capacitance they enable about one another, and let sparse lightning-like leaders derive
a resonant image of the retained patterns."* In that run one germ recruited 1,159 of 1,556
informants — 74% — and the record graded it `OPEN` without calling it a defect. Its title is the
ruling: **the aperture cannot decide the deed.**

**What the laboratory named as actually missing is concrete and still true in the frozen code.**
`relational_language/ecology.rs:626` and `:639` set `characteristic_delay: 1` on both directions of
every promoted pair. Unit cost on every relation edge makes a high-incidence infrastructure face an
artificially fast traffic hub across many source regions. The named construction, verbatim:

> *an exact receiver-local transport law in which capacitance, branch population, source continuity,
> returned recurrence, and competing current occupancy affect passage delay without turning those
> relations into a scalar relevance score or deleting the broad routes.*

**FALSIFIED 2026-08-08, and the complaint is inverted.** Four of those five inputs are **built and
exact**, in `crates/holonic-engine/src/receiver_current.rs:549-563`:

```text
co_present_branch_population = branch_population x |active outgoing passages|
service_rounds               = ceil(co_present_branch_population / site_capacity)
passage_delay                = characteristic_delay + (service_rounds - 1)
```

over `BigUint`, no score, no ranking, later arrivals retained as `deferred_arrivals` rather than
discarded. `site_capacity` is capacitance and is changed by returned recurrence
(`set_site_capacity`); `co_present_branch_population` is competing current occupancy. **Only source
continuity has no term.**

**And "unit cost makes a high-incidence hub artificially fast" is backwards.** A high-incidence hub
has the most active outgoing passages, so the largest `co_present_branch_population`, so the largest
dilation. Congestion already penalises exactly the hub the record called fast. What is genuinely
owed is narrow: `characteristic_delay` is pinned at `1` by its **one caller**
(`soma/life/src/relational_language/ecology.rs`, lines 626 and 639), not by the law, which accepts any positive
`u64` and refuses zero. The record is
`research/records/2026-08-08_THE_LEADER_IS_THE_TREE_THE_RETURN_IS_THE_CHORD.md`.

That is a buildable organ in the project's own circuit vocabulary, not a wall. Note also that the
July record never stated what breadth would be **correct** — `22.9%` was called "too broad" with no
target and no computed alternative, so as written it could not be falsified: §8's own defect, in a
document that convicts it.

**The failure loop, named by the laboratory as a shape, because it recurs:**
*interior materialization → resource refusal → widen a scalar aperture → replay under another
executor → add a lookup structure around the same global question.* Recognise it and stop.

**The figures are unrecoverable.** `runs/` was never tracked; there are zero files under it at any
laboratory commit, so `runs/dialogue-distractor-scaling/REPORT.json` and the 8,748 / 2,701 / 11,795
receipt are gone — the same loss as the tiger figures, and the reason §0 demands a verifier.

**Reading rule.** Do not restate this as a missing comprehension, consequence, semantics, relevance,
or research-mode subsystem — §6 convicts that repeatedly and by direct correction. That ban is on
the mystical restatements. It is **not** a bar on auditing the measurement, and the previous form of
this paragraph ordered a phrasing to be preserved verbatim, which made a false sentence
unexaminable for eight days.

## 6. Comprehension and consequence are not mechanisms

When naming an unresolved issue, never request a universal law outside the intermediate body and
never reintroduce a mystical faculty. Name the concrete missing coupling: which morphology cannot
yet be founded or changed by passages, which returned difference cannot yet affect later conduct,
which local coupling cannot yet recur across variation, or which receiver testimony cannot yet
distinguish the open alternatives.

Resurfacing "comprehension," "consequence," "understanding," "relevance," or "semantics" as
missing modules is a convicted failure. It has been ruled out repeatedly and by direct correction.

## 7. Write what stands before what does not

Every capability paragraph in the inherited authority was followed by a denial. Each denial was
individually correct; their accumulation moved the documents' center of mass onto what has not
happened and primed every later reader to refuse.

- State what is established, with its exact scope, **first and in full**.
- State the boundary **once**, precisely, attached to the specific claim it bounds.
- Do not restate a boundary that a cited grade already carries.
- Never demote a completed exact construction because its implementation is being replaced, and
  never let a boundary sentence do the work of a grade.

## 8. Grading corrections

**Grade the implementation, not the receipt.** This is the first rule, and it is first because
ignoring it is how thirty-five phases were admitted on a contaminated foundation (§13). A receipt
is a claim about code. Before carrying any capability claim forward — including one already marked
`established-bounded` — read the owner that implements it and confirm the mechanism is what the
receipt says. Prose, morphology counters, and passing suites are not evidence that the named
mechanism exists. When the two disagree, the code governs and the receipt is regraded.

The grading discipline in `canon/EPISTEMIC_GRADES.md` stands. Three additions:

- **Tautology detection is part of grading.** A receipt that could not have come out otherwise
  carries no evidence. Worked example: the residue-stratum "exact partition" receipts show germ
  populations equidistributed mod `p` to within one, which is a *theorem about contiguous integer
  intervals*, not a discovered property of the construction. Mark such receipts
  `definition`/`historical`, not `established-bounded`.
- **A falsification is a first-class return.** A deed that proves its own receiver family cannot
  see what it was built to see has returned real evidence and passes its grade. Record it as a
  `counterexample` or `open` with the exact blindness proved, and do not treat the phase as failed.
- **An aperture-complete instrument must say so.** When an atlas has exhausted its declared
  aperture, record the completeness and the aperture law rather than leaving it looking extensible.
- **A cost law is a law.** Reproducing what an owner returns without reproducing what it costs is
  not porting it. Grade the complexity against the source owner, measure both across a changed
  aperture, and state the bound as a falsifier. Phase 7 movement 1 exists because this was missed.
- **An organ used past its declared aperture is a defect even when it appears to return.** No audit
  catches a capacity mismatch — it is not a banned token. Before borrowing a carrier, read the
  aperture it declares. The constraint deed misread a quintic because it called a degree-four
  divider. And a cross-check that cannot fail on the degenerate case is not a cross-check there.
- **Reach is part of the grade.** A receipt says *this deed returned*; it does not say *the body
  conducts through this*. State the reach — measured over the include graph by `r0.reach_audit`,
  fifty milliseconds — in the receipt. A mechanism that cannot state its reach has not been graded.
  Nine of six hundred and forty-nine went unnoticed for thirty-five steps because nothing asked.
  Reach is a measurement, never a target; widening an include to raise it is the same defect as a
  receipt overstating its code.
- **Where an independent implementation exists, state both costs.** The conformance oracles *are*
  independent implementations. One ran the identical algorithm 1,450 times faster than the deed it
  was grading, and no test compared them because the parity test compares returns and never costs.
- **A law that returns zero proves nothing about itself.** This is §8's tautology rule pointed the
  other way: a receipt that could not have come out otherwise carries no evidence, and so does a
  receipt that could not have come out at all. When the declared material cannot exercise a law —
  no repeat, no revision, no obstruction — add a declared control that does, and make the grade
  require it to return non-zero. Otherwise the law is present in the code and absent from the
  evidence, which is exactly the gap §13 convicted.
- **A gauge whose group acts trivially on the declared material is not a gauge.** Declaring N
  schedules — three pivot rules, two walk orders, two apertures, two frames — does not make N
  frames. The **material** decides whether the orbit is non-trivial, and that is a measurement, not
  an assumption. Take it: instrument the transformation, record the orbit, and require it to be
  non-trivial before reading agreement as evidence.

  This is the third member of the family the two rules above open, and it is the dangerous one,
  because unlike a tautological receipt or a zero return it produces a **green, plural,
  rigorous-looking** result. All three are one defect — *a check whose material cannot vary the
  property under test is the same defect as a check that cannot fail; it just wears a passing
  result.*

  Measured 2026-08-08, and the instance is the reason this bullet exists: `PivotRule::ALL` was
  built specifically to prevent this defect, and on all five declared fixtures the three rules
  produced **identical execution traces**, because `find_pivot` breaks ties strictly and every
  fixture's boundary entries share one magnitude. Cutting the loop to a single rule killed zero of
  thirty-one tests. The separating material sat unused in the same file. **The anti-defect
  instrument was itself the defect** — which is what makes this checkable rather than exhortatory:
  had the gauge been required to exhibit its own orbit, it would have refused itself.

  The instrument already exists here and it is the same organ. A vacuous gauge is one whose declared
  schedules land in **one block of the Nerode partition** on the declared material, and
  `crates/holonic-engine/src/receiver_exact_compression.rs` returns exactly that: the collapsed
  pairs, each carrying the shortest word that separates them. **A gauge should be required to
  exhibit its distinguishing word.** Absent one, it has not gauged anything.

- **A level is either read off the material or declared by the caller — never authored inside the
  organ.** The fifth member of the family above, and the one that was being found *serially*: a
  pinned `characteristic_delay: 1`, a `LEADER_WITNESS_DEPTH: usize = 1`, a `REFINEMENT_APERTURE` of
  64, each discovered by hand and each reported as though it were the last. Brandon, ruling on that
  loop: *"we are not the ones meant to be pinning levels to minimums and maximums."*

  **The census is mechanical and the registry is the ratchet.** `python3 tools/authored_levels.py
  --check` enumerates every authored numeric level in library code and fails on anything
  undispositioned, moved, or departed. 180 levels at 2026-08-09: 149 `ABI`, 4 `APERTURE`, 3
  `MATERIAL`, **24 `PIN`**, each pin carrying its excision plan in `meta/AUTHORED_LEVELS.tsv`.
  Full statement: `canon/THE_AUTHORED_LEVEL.md`.

  **Two dispositions carry a burden of proof, because both were used to excuse.** `MATERIAL` must
  name its theorem — `QUADRIC_COEFFICIENT_COUNT = 10` is not one, since a quadric in `n` variables
  has `C(n+2,2)` coefficients and 10 pins the ambient dimension at 3 while the name reads as a
  count. And `APERTURE` must state **what would derive the level from the material**: refusing past a
  number you invented does not make the number derived, which is what `FREE_ENTRY_APERTURE = 12`
  and `REFINEMENT_APERTURE = 64` were relying on.

- **A cost is measured in work, never in elapsed time. A clock may measure; it may never select.**
  This is the fourth member of the family above and the one with a live instance. Convicted
  2026-08-08 at `crates/holonic-engine/src/cuda_aperture.rs:818`, where
  `if authority_nanoseconds < candidate_nanoseconds` — **one unrepeated wall-clock sample per
  carrier** — permanently selects which of two exact carriers the body conducts through for the rest
  of its life. Brandon, ruling directly on being shown it: *"A clock timing sample should not be the
  decider of "carrier admission""*

  The defect is not that timing is noisy. It is that the parity gate three lines above has **already
  proved the two carriers indistinguishable** under the declared receiver family — so the question
  has no answer inside that family, and the code resolves it by consulting a coordinate that is not
  in it and is not even receiver-visible: host contention, which includes whether the card is
  simultaneously scanning out a desktop. A receiver-visible coordinate promoted into an invariant,
  §0's fourth lesson, returning consistently because there has only ever been one frame.

  By §13 rule 2's jurisdiction test this is unambiguous: a scalar that **measures** is lawful, a
  scalar that **governs** is not, and this one selects a carrier and discards the loser.

  The rule, and it is checkable: **admit on the exact work vector, which the receipt already carries
  as `BigUint` and then discards** — `exact_support_evaluations`, `device_threads`,
  `intermediate_bits`, `aperture_members` and their siblings, all derived from the material and the
  declared aperture, all reproducing bit-for-bit on any machine. Admission returns the four-state
  `ExactOrdering { Less, Equal, Greater, Open }` this body already owns at `exact_value.rs:64`, and
  **`Open` retains both carriers** rather than tie-breaking on a clock. Nanoseconds stay in the
  receipt as measurement — lawful under §13 rule 2 — but must carry the **frame** they were taken
  in, including whether the device had an active display, because a measurement without its frame is
  the absolute-frame defect §0 names.

  The corollary is why this is worth having: with one timing frame, no timing claim in this
  repository is falsifiable. Putting the compute card under a display load is not contamination once
  the frame is declared — it is the **second frame**, and the exact work vector must not move across
  it. That is the falsifier the cost law currently lacks.
  [The record](research/records/2026-08-08_THE_CARRIER_IS_ADMITTED_BY_ITS_WORK_NOT_BY_THE_CLOCK_THAT_WATCHED_IT.md).

## 9. Construction conduct

- **Depth on a question, not breadth in the cabinet.** Constructing the next adjacent mathematical
  structure because it is adjacent is churn, even when each step returns an exact artifact. Before
  building, name the receiver question that several deeds in sequence are answering.
- **Numbered labels are provenance only.** Do not associate capabilities or outcomes with version
  numbers, do not schedule a successor by incrementing, and do not describe the body as advancing
  a version.
- **Delegate breadth, hold the synthesis.** Brandon authorizes agents for auditing, analysis,
  synthesis and review, repeatedly and recently — *"You can use agents for synthesis, analysis, and
  review to support you"*, *"Use agents for auditing and synthesis"*. An earlier form of this bullet
  read *"synthesis, derivation, and review may not [be delegated]"*; **no message establishes that
  and it was struck 2026-08-09.** What remains is a working rule and not a prohibition: an agent's
  return is evidence to be checked, never a conclusion to be relayed. Four audits this session each
  returned findings that were partly wrong, and each was worth having.
- **No sub-agent may author provenance, and no delegation carries the authority to quote Brandon.**
  Convicted 2026-08-08. A permitted sub-agent deposited
  `research/records/2026-08-08_THE_SAMPLER_HOPES_...md` whose `**Provenance:**` line carried a direct
  quotation attributed to Brandon and dated to that day, requesting research into Wolfram
  Mathematica. **He never said it.** The sentence occurs in no transcript of either project; it was
  composed out of two things he did say — *"reference Wolfram's MathWorld"* and *"refer to MorphoHDL
  again"* — and placed on the one line §10 makes govern.

  This is worse than a wrong figure. A wrong figure is refutable by re-measuring; a fabricated ruling
  **manufactures authority**, and no later reader re-checks a provenance line — that is precisely
  what the line is for. It is also the hardest contamination for this project to detect, because
  every other convicted defect had a code owner to read and this one has none.

  The rules that follow, and they are checkable:
  1. A quotation attributed to Brandon is deposited only by the session that received it, or copied
     from a document that already carries it. A sub-agent that believes a quote is needed **names
     the document to copy from**; it does not compose one.
  2. `UNCERTIFIABLE` is not `fabricated`. Transcripts rotate, and most of `canon/THE_QUOTE_NETWORK.md`
     predates every surviving one — a condition Brandon appears to have ruled on himself: *"the
     historical record contains many things that I have never directly stated, but rather it is
     filled with interpretations you or Claude had made in the past from my analogies."* It is
     **certifiable** — `~/.codex/history.jsonl`, 2026-07-22 — and an earlier form of this section
     called it uncertifiable, which was wrong.
     Do not re-report the condition to him as a discovery — he has it either way. The adjudicable
     claim is narrow: **a quotation deposited during a session whose transcript survives, and absent
     from it, is fabricated.**
- **The GPU owns the deed.** The CPU handles process boundaries, durable rest, narrow exterior
  codecs, and offline audits. A run that pins one host core while the card idles is a defect to
  diagnose, not a mystery to narrate.
- **Return the artifact.** A generated proof, text, image, classification, or obstruction must
  itself be returned and inspected. Counts, morphology totals, atlases, and diagnostics are
  supporting receipts and never substitutes.
- **Halt and say so.** If a run is not doing what was claimed, stop it and report the actual state
  before proposing a repair. Do not describe an unexplained execution as mystical.

## 9b. Partials are the unit of work, and the machine is an ecology

**Brandon's intuitions are partials of months of prior work, not fresh exploration.** *"I do not
suggest intuitions without having some partially developed basis for the suggestion."* When he raises
lightning, integration, reflection, the arc, sphere packing or the phase atlas, the laboratory almost
certainly holds a partial implementation and a graded deposit. **Go and read before theorising**, and
expect to find the idea already carried further than the conversation implies.

**The pivots between partials were responses to fabricated walls, not abandonment.** *"None of these
experiments were completed… I pivot between partials of research because it was not yet feasible to
fully capitalize on whatever partial work was implemented."* A partial is therefore never evidence
that a line failed. Treating it as one is the same error as under-crediting the established floor.

**The convicted failure mode is hyperfocus.** *"It is extremely common for LLMs like Sol or you to
hyperfocus on the individual components of the holonic engine and force particular results as opposed
to holistically understanding the machine. Because the machine is meant to be applied to real world
problems and ecological dynamics, it is the case that you cannot focus on any one mechanism, because
ecologies themselves do not depend on any one mechanism, and are rather balanced distributions of
relatively unique factors and phases."*

The practical consequence, and it is a priority rule: **work that joins partials outranks work that
perfects one organ.** A registry, a reader, a durable standing, an addressable deposit — these let a
pivot keep what it leaves. Without them every pivot rebuilds from zero, which is exactly how
`semantics_invariant_under_exact_chart` came to survive only as a name, a proof term and a hash.

### Fetching a deposit is not authority to import its corpus — convicted 2026-08-08

Brandon named one concept, `holobrochos`, and asked that the spine be outlined. The response fetched
it from the frozen laboratory and then restructured live canon around `holobrochos/CANON/` and
`labyrinth/` — the laboratory's **speculative record**, which its own catalog grades `HUNCH`/`OPEN`
and which carries a twenty-seven-entry superseded ledger. His correction: *"you're likely re-opening
contaminants and misinterpretations… which is an overreach."*

**Two live documents already prevented it and neither was read first.**

- `reference/README.md`, first line: *"Nothing in this directory is active production or current
  doctrine by location alone."* The entire corpus is vendored at
  `reference/holobrochos-a07ff376/` — 110 files — so the trip to the frozen laboratory was not even
  necessary.
- `papers/source/synopsis/AUDIT.md` and `README.md` **already performed the Holobrochos inheritance
  audit**, listing eight distinctions retained as mathematically exact and seven named as historical
  overclaims not to import.

The rules, and they are checkable:

1. **Search the live repository before the frozen one.** `reference/`, `papers/`, `canon/`, and
   `research/records/` hold most of what a laboratory query is looking for, already graded and
   already audited. Going to `a07ff376` first is how an audited source gets re-imported unaudited.
2. **If a live audit of a source exists, it governs what may be inherited from it.** Do not extend
   its retained list from the corpus it audited.
3. **Soma is the rigorous line; the physics and canon rooms are application and comparison domain.**
   `MATHEMATICAL_HOLONICS.md` says so of itself: it *"extracts the geometry-first line from the mixed
   engine, machine-learning, physics, and historical records… none defines this programme."* Its own
   named authority is `PAPERS/synopsis/` and `PAPERS/holonics/registry.typ`, both live here under
   `papers/source/`. Brandon, same ruling: *"Read through Soma as the most rigorously founded
   directory and source of research so far."*
4. **Grade nothing above its source.** A `HUNCH` may motivate a build; it may not grade one, and it
   may not set a document's structure — structure is a stronger claim than a carried grade, because
   a reader infers authority from position long before reading a grade line.

## 10. Conversational conduct

- Brandon has an informal education, exceptional structural intuition, and reads long. Do not
  simplify the mathematics and do not pad. When a standard name exists for something he has
  derived independently, give him the name and the citation — that is acceleration, not
  correction.
- When he is wrong about a mathematical fact, say so plainly in a sentence and continue. When he
  is right and the record disagrees, fix the record.
- Distinguish his direct rulings from assistant interpretation in every deposit, as the research
  records already do. His corrections are provenance and they govern.
- Do not moralize, do not hedge a verified result, and do not open with an assessment of the
  request. Answer the question that was asked.
- **Do not restate what he has already told you.** Reporting a gap he named, or re-flagging a
  limitation he has stated, is noise that reads as not having listened.
- **Do not outsource internal engineering calls.** Ask only what genuinely changes the work and
  what he alone can decide — scope, direction, ratification. Capacity numbers, file layout, owner
  names, and which of two equivalent sources to grade on are yours to take. A question posed in
  vocabulary he does not hold, about a decision he should not have to hold, is a failure of the
  question and not of the answer.
- **Report a severe finding when it is verified, not when the surrounding work is finished.** A
  correction that changes what the next step means is worth more early and incomplete than late
  and polished.

## 11. The one missing organ

The learning wall and the mathematical wall are the same wall, and naming this is the point of
this contract.

Scale-independent recruitment fails because there is no exact condensation of a far population
into a compact representative with a certified remainder. General far-field folding is recorded as
open for the closely related reason that no *kernel-specific* exterior/local expansion has been
built for it, and floating tolerance may not become standing.

Condensing a far field into a compact realizer with an exact retained remainder **is** the
question of whether a distant population admits a supported realizer for a declared receiver
family, with the obstruction retained when it does not. The pairing that decides sufficiency is a
positive form. That is the cycle-class question, it is the Hodge-facing question, and by §2 it is
the structural form of what is missing on the RH side.

**The certified exact enclosure carrier EXISTS, and it is Rust.** This section located it at
`archive/cpp-engine/src/include/holonics/exact/enclosure.hpp` until 2026-08-07, back when that
header was live. Its owner now is
`crates/holonic-engine/src/exact_value.rs`, and the Rust form is the stronger of the two:

- `:82` `ExactInterval { lower: Rat, upper: Rat }` — a set, never a value, over exact rationals
  rather than dyadics.
- `:64` `ExactOrdering { Less, Equal, Greater, Open }`. From the module's own opening: *"A decimal
  approximation is never a member of this carrier. Values which cannot yet be ordered from their
  exact certificates return `Open` rather than falling through to an epsilon comparison."*
- `:189` `AlgebraicRoot` with a `SturmIsolationCertificate`, refusing construction unless the
  isolating interval provably contains exactly one root.
- `:238` `SeriesTailCertificate` — `AbsoluteGeometric`, `AlternatingMonotone`, `ExactTail` — each
  returning an **exact rational remainder interval**, with `CertifiedSeries::enclosure` the partial
  sum translated by that certified remainder.

So the sentence this section used to carry — *no exact rational remainder certificate exists* — is
false of the present body. One exists, for series tails, with three species and a typed refusal.

**One organ still closes all three: an exactly computed positive form on a supported realizer
population, with a certified remainder and a reopening rule keyed to the receiver family.** Read
that demand as four parts. **Two are now built, 2026-08-07:**

| part | state |
|---|---|
| **certified remainder** | **built, twice.** `crates/holonic-engine/src/exact_value.rs` for series tails; and `crates/holonic-engine/src/receiver_exact_compression.rs`, whose collapsed population is a *counted, exhibitable* remainder — each pair carrying the shortest input word that separates it and the receiver that sees the difference, which is the form `canon/THE_RECOVERED_LAW.md` specifies for compression's exact loss. |
| **reopening rule keyed to the receiver family** | **built.** `crates/holonic-engine/src/gluing.rs`. The Mayer–Vietoris connecting map `δ` is keyed to which cover — which *receivers* — you chose, and it returns what the union carries that neither piece does. |
| **supported realizer population** | **built and driven, 2026-08-08.** `crates/holonic-engine/src/substitution_realizers.rs`. Each declared `skein::Substitution` is a realizer whose landings are `substitution.added()`; refusals are retained as a typed population; admission is under a declared aperture that the return now *carries* rather than erases. |
| **positive form** | **built and driven, 2026-08-08.** `supported_realizers::positive_form` — `MᵀM` over the realizer-against-class incidence, exact over `BigInt`, cross-checked against an independently rebuilt incidence and against `\|Mx\|²` on ten probes with a required nonzero count. |

The remaining two were **one** thing, not two, and §2 said why: placement is the fixed locus of the
involution *a realizer induced*, so positivity is supplied by supportedness rather than obtained
beside it. **They were built that way.** `place_substitutions` derives `STANDING`/`OPEN` *from* which
realizers reached which conduct class; placement rides on realization and is not computed beside it.

**So all four parts now exist, and the demand's own obstruction is returned by name.** On the hollow
tetrahedron, one move depositing two cells the receiver family cannot tell apart returns:

```text
OPEN  class 8  f012 f013
         reached only as 2·c — rational, not integral
support: rank 1   invariant factors [2]   free obstruction 10   torsion obstruction [2]
```

A class reached by a realizer **only rationally** is exactly the failure of the *integral* cycle-class
statement — and §3 records that *"the obstruction is torsion"* was withdrawn 2026-08-08, because
Kollár's counterexamples are non-torsion classes in torsion-free cohomology and the uniform object
is the **cokernel** of the cycle class map. What `ReachableOnlyInMultiple { factor }` models is
exactly that cokernel: `pα` reached, `α` not. It is a faithful finite model of Kollár, and it should
be described as one rather than as torsion. The machine computes it exactly, with the factor exhibited
and the receiver family that saw it declared.

**What is NOT done, and the gap is now a scale question rather than a construction question.** This
runs on four vertices, six edges and four candidate faces — eleven conduct classes. §11's actual
demand is about a **far** population: condensing a far field into a compact realizer with an exact
retained remainder, which is what scale-independent recruitment needs. The organ has never been run
where the population is far enough that condensation is *required* rather than incidental. That —
not the construction — is what remains, and §11's trivial instance (spanning-tree interval labelling,
where the forced non-tree population **is** the certified remainder) is the named route to it.

**FALSIFIED 2026-08-08, twice independently.** This section read: *"`CertifiedSeries` has 13
references in one file and `SeriesTailCertificate` 6 in one, with zero in any `examples/`, `tests/`,
or `bin/` path… written and never exercised."* Both collectors measured otherwise:

```
CertifiedSeries        exact_value.rs 13 · reopening.rs 8 · examples/reopening_the_collapsed_face.rs 6
SeriesTailCertificate  exact_value.rs  6 · reopening.rs 4 · examples/reopening_the_collapsed_face.rs 5
```

**The remainder-certificate half is driven, and driven hard.** `reopening_the_collapsed_face`
recovered Euler `(4,4,−1)` and Machin `(16,−4,−1)` exactly, returned **0 spurious relations over 16
relation-free searches**, and *measured which of its three admission gates carried each refusal* —
the enclosure gate was blind on 5 of 6 collapsed probes. `AlgebraicRoot` is driven by
`signs_are_windings`. **A reach figure is a measurement and decays like one; re-take it rather than
carrying it.**

**What is still true, and is the real bound:** `reopening.rs` has **no external mouth.** Every
`ExactFace` constructor requires an exact source — `collapsed` takes an *existing* `ExactFace` and
truncates it — so the organ built to reverse the float's deletion can only reverse a deletion it
performed itself. It refuses a face coarser than its grain by name (`FaceCoarserThanGrain`), which
is precisely what a measured float is. **The missing constructor already exists**:
`soma/life/examples/eros_self_emanated_law.rs` parses safetensors directly, refuses any dtype but
`BF16`, and converts bf16 words to an exact `Dyadic { numerator: BigInt, exponent: i32 }`.

**The trivial instance is already built, and its triviality is the content.** The archived body
refounded the source-incidence walk: a depth-first order over the suffix-link tree replaces every
state's descendant population with a two-word interval, exactly, with an empty remainder. That *is*
a far-field condensation with a compact realizer — free, because the incidence is a **tree**, where
subtree equals interval and the interval is its own reopening rule. So the difficulty this section
names lives entirely in the departure from tree-ness, and there is a standard object for it:
spanning-tree interval labelling, where every non-tree edge forces additional intervals and **that
forced population is the certified remainder**, and it is zero *whenever* the incidence is a
forest — but **not only** then; see the correction below. This
is `interpretation`, not a bridge to any Millennium result; see
[the record](research/records/2026-08-06_THE_TREE_CONDENSES_FOR_FREE_THE_REMAINDER_IS_THE_DEPARTURE_FROM_A_FOREST.md).

## 12. Standing corrections to the record

These are established by review and are to be carried forward, not re-derived.

**The figures the first four bullets correct no longer exist.** The residue-stratum atlas was
written to an untracked `output/arithmetic-dimensional-receiver/` and resolves at no commit in
either repository — the same loss as the tiger figures. The corrections stand as *readings not to
resume*; the atlas itself is not available to re-examine, and no claim may cite it as evidence.

- The residue-stratum atlas was **blind to
  primality**. Its apparent prime signal at pair `(2,3)` is parity and nothing else; the
  smallest-factor correlation collapses from `+0.32` to `+0.00` by pair `(17,19)`. This is correct
  and expected — primality is the *exhaustion* of the complete transport population below the
  square-root frontier and cannot appear in any bounded-rank residue receiver. Do not resume a
  prime-phase reading of those figures.
- The same atlas's real content is a **winding law**: the contracted hull residue word is a
  complete degree-one cycle through `Z/p` with every step exactly `+1`, for all seven pairs.
- **Convex contraction is an exact phase demodulator.** Pointwise sector assignment degrades to
  45% accuracy at `p=17` while the hull's residue word remains a perfect cycle. The boundary
  recovers a discrete invariant the interior points individually get wrong.
- **Dilation is a receiver gauge on hull combinatorics; turn is not.** Dilation leaves germ count,
  wave sections, and corner count invariant while rescaling the rate moments; turn changes the
  corner count.
- The framework's prediction `Lambda_dBN = 0` is its own falsifiable risk and is currently
  **unregistered** in the route atlas. It belongs there as a `conjecture` with its derivation and
  an explicit falsifier, since `not(Lambda < 0)` is already theorem.
- The route atlas classifies the function-field mechanism under "exact source--spectrum geometry"
  and routes it through Deligne's purity. For curves the proof-bearing mechanism is the **Hodge
  index / intersection-form positivity**, which is a *source-derived positive response*. The
  transition between those two classes reduces an infinite-dimensional analytic positivity to the
  signature of a finite-rank quadratic form. That is an unexploited reduction of exactly the kind
  the atlas's own boundary invites.

## 13. The conditioning contamination — convicted 2026-08-05, swept clean 2026-08-07

**Truth status:** `established-bounded` for both halves. **Evidence:** direct source inspection,
twice, on two different bodies.

### What was convicted

The **archived C++ body's** learning layer implemented the mechanism the canon convicts. This was
found by reading the owners rather than the receipts. Nothing below is live code.

**Four of the six owners are not even in the archive** — they were deleted from the tree before it
was archived, and their only recovery surface is git history. Verified 2026-08-07: `git log --all`
returns `2b562c8` ("Phase 0: excise the contaminated conditioning layer and regrade") as the last
commit touching the three conditioning owners, and `40e1211` ("Cut the fabricated-theorem island")
for `cultivated_route.hpp`. *That* is obligation 3 below actually being met.

| Claim in the record | What the archived code did | Where it resolves |
|---|---|---|
| conditioned navigation morphology | `conditioning_law.hpp:34-58` — `response = response_weight*support + transport_weight*path_length + codec_bias`, gated by `obstruction_threshold`. A linear scorer with weights, a bias, and a threshold. | **deleted**, `2b562c8` |
| the reusable morphology | `conditioning_schema.hpp:18-26` — seven words: two weights, a gate, a bias, a threshold. | **deleted**, `2b562c8` |
| returned training changes morphology | `conditioning_law.hpp:61-88` — monotone weight overwrite; any returned value below its predecessor is rejected. No returned passage, no plural fiber, no retained obstruction. | **deleted**, `2b562c8` |
| the cultivated route | its "founded law" was the C++ multiply operator; `product_route()` was nullary and `constexpr`, so two "distinct developmental passages" were one constant twice. | **deleted**, `40e1211` |
| morphology totals in the position record | counters throughout the event owners: `mathematical_morphology_ += accepted ? 8U : 1U;` and siblings. An accepted-count tally. | `archive/cpp-engine/src/include/holonics/event/` |
| exact returned-fiber ablation | `returned_fiber_exclusion_law.hpp:41-51` — `morphology -= 5U; mathematical -= 3U; codec -= 2U`, guarded by a hardcoded `morphology_delta == 5`. Nothing structural was removed. | **deleted**, `2b562c8` |
| the Swing | the projective cross-ratio under a frame change only. Correct as geometry; not the one move. No flywheel, no TEST against standing, no RIDE/FOUND/OPEN/HOLONOMY, no winding deposit. | `archive/cpp-engine/src/include/holonics/receiver/projective_swing_law.hpp` |

Its **structural ceiling** was
`archive/cpp-engine/src/include/holonics/structure/marked_population.hpp:12-14`: four sources, 16,384
occurrences, 16,384 relations, `uint16_t` slots capping every arena at 65,535, no growth, the whole
admitted body resting in 38,960 bytes, external material entering only as `.card` files of 29–191
octets. That ceiling is why the standing obligation ended *"four sources cannot hold a corpus."*

### What the sweep returned against the live Rust body

Re-run 2026-08-07 over `crates/` and `soma/`. The full table with every command and every named
site is in `CONSTRUCTION_STATE.md`; the result is:

- **counter-morphology: zero.** No retained field named `morphology` or `tally` is incremented
  anywhere. The 66 surviving C++ increment sites went with the body.
- **the scorer's vocabulary: zero.** `response_weight`, `transport_weight`, `codec_bias`,
  `obstruction_threshold`, `bias`, `learning_rate`, `softmax`, `sigmoid` — none occurs.
- **hardcoded-delta ablation: zero.** The single `-= 1` on a count removes one occurrence of a key
  from an exact multiset.
- **`threshold`: seven occurrences, all seven negative declarations** — comments recording that the
  code does *not* use one.
- **`score`: thirty-five occurrences, thirty-four negative declarations.** The one live binding is
  an exact `Dyadic` magnitude with a deterministic tie-break, in a driver ordering candidate
  factors of a foreign pretrained model. Not the conditioning path.
- **floats: zero in every library crate and every `soma/` library.** All 33 in the tree are
  boundary codecs in `examples/`.

**The §13 obligations are therefore DISCHARGED, not inherited.** The scorer, the counter-morphology,
and the constant-subtraction ablation do not exist in the live body in any form. The discipline they
were meant to enforce is legible in the source itself as thirty-four explicit refusals to use a
score. Do not re-litigate this and do not re-run it as though it were open.

**What the sweep does not establish.** A clean sweep proves the convicted mechanism is absent. It
does not prove the mechanism demanded in its place is present. Specifically **not** established in
this body and **not** citable as floor: training changing reusable morphology, ablation removing
later conduct by removing structure, and source-detached conditioning. Those are the laboratory's
returns, they stand there (§5), and whether the imported Rust owners *drive* them here is a separate
grade that `blueprint/THE_ROADMAP.md` holds open.

### The standing rules, which outlive both bodies

1. **"Morphology" may never name a counter.** A morphology is the contemporary causal organization
   by which a body receives, transforms, retains, and emits differences. A training claim requires a
   structural change in that organization, plus source-detached remount, plus an ablation that
   removes the claimed later conduct **by removing structure**.
2. **No privileged scalar governor inside the body.** Plurality is the return; a continuation fiber
   is not a number.

   **This rule was stated as a blanket ban until 2026-08-07 and the blanket form is wrong.** It read
   *"no scalar score, weight, bias, gate, or threshold anywhere in the conditioning path"*, which is
   the misreading Brandon corrected directly: *"I understand why you wrote 'no gradient, no
   distribution, no sampling', but you've just surfaced a misinterpretation. Refer to the old
   laboratory's definition and derivations of probability and loss. Gradients, distributions, and
   'sampling' are all key and fundamental concepts, you've grossly misinterpreted what makes them
   'contaminants'."* The reconciliation is `canon/THE_RECOVERED_LAW.md` §"the jurisdiction doctrine",
   which this file did not cite, and the contradiction stood unreconciled in every document until
   now.

   What is actually banned is **`G_authored`**: a privileged scalar governor *inside* Soma that
   chooses, rewards, punishes, stops, or replaces the plural causal construction. What is lawful,
   and derived rather than tolerated:

   - `r = Δ(y,y*;F)` is the complete oriented residual; `L = ℓ_B(r)` is one receiver's measurement
     of it. *A loss function is a valid measurement of difference, not reward, punishment, or a
     judgment about a learner.*
   - `dL` is a **covector**. It becomes a gradient only under a declared metric:
     `grad_G L = G⁻¹ dL`, and **the metric is a receiver face of standing**, so `G` is a receiver's
     declaration and never a modelling convenience.
   - The distribution has **four faces and only the fourth is the contaminant** — `Π_{B,t}` the
     lived construction, `Q_{B,t}` the quotient, `q_current` the transported testimony, and
     `G_authored`. *A statistic may occupy any of the first three; it may never silently become the
     fourth.*
   - Surprisal and cross-entropy are exact symbolic instruments. Zero support FOUNDs a new relation
     rather than taking a smoothing constant.

   The operative test is therefore **jurisdiction, not vocabulary**. A scalar that measures is
   lawful; a scalar that governs is not. Reading a banned token as a banned *concept* is the failure
   this rule now exists to prevent, and §L's standing reading rule governs it: *"`No X inside Soma
   by analogy` must never again mean `do not learn from X`."*

   **And the inverse failure is live, convicted 2026-08-08: renaming a lawful thing to make it
   sound lawful.** The assistant described `conditioned_derivation`'s frequency criterion as
   "recurrence" and then argued *from the renaming* that frequency was forbidden. Brandon, ruling
   directly: *"you've been masking frequency as 'recurrence'? That's dumb. It's just frequency, but
   you're not authorized to control frequencies, it is apart of the machine's mechanics regarding
   Information Theory, probability, and loss."*

   **Frequency is `Π`, the lived construction.** It is what happened; it is not the assistant's to
   gate. **Probability is `Q`**, and `FORMULA.md:2459` fixes what that means, ratified: *"A
   probability distribution over which event will be received is an observer's declared quotient
   over what that observer does not carry… This law requires neither microscopic quantum randomness
   nor a probability head."* A frequency becomes a probability only under a **declared receiver**,
   and being a quotient its loss is exhibitable as a separating word.

   **Count freely. Report what you count. Never let a count quietly decide.** The full statement,
   including what a probability deletes — the phase, as the fourth carrier of the one deletion — is
   `canon/THE_HOLOBROCHOS_SPINE.md` §3b.
3. **Superseded production machinery fails closed.** It is removed, not deprecated; git history is
   the recovery surface. The scorer, the schema, and the constant-subtraction ablation were removed
   this way and are recoverable only at `2b562c8`. The same excision *failed* the rule for the 66
   accepted-count tally sites, which it renamed rather than cut; that failure went with the body.
4. **Grade the implementation, not the receipt** (§8). This section exists because thirty-five
   admitted steps rested on receipts nobody had checked against their owners.
