# The contract's provenance — what CLAUDE.md corrected, and what it used to say

**Genre:** canon. **Truth status:** `historical` throughout — every block here is the provenance of a
rule that lives in `CLAUDE.md`, not a rule itself. **Nothing here schedules anything.**

**Occasion.** `CLAUDE.md` reached 197,124 characters on 2026-08-15, and a behavioural audit that day
found its bulk was not law but the *litigation of law*: worked instances, withdrawn readings, and the
dated narrative of each correction. Those are what makes the contract trustworthy and they are also
what makes it too long to hold. **The rule stays in the contract; the argument that produced it moves
here**, which is the same division `docs/canon/THE_TIMELINE.md` already makes for behaviour.

**This file is never the authority.** Where a block here and `CLAUDE.md` disagree, the contract
governs and this file is the thing to fix. Read it when you want to know *why* a rule says what it
says, or when you are about to re-derive something the contract already settled.

---

## 0c. The implementation wave of 2026-08-10, and the four defects it found

**Every item of the assessment's ordered list was attempted. The findings outrank the completions.**

### The tower: the blocker was misdiagnosed, and correcting it produced the connection

The assessment said `Corner::sine: Option<Rat>` → `AlgebraicRoot`. **That is wrong.**
`exact_value::AlgebraicRoot` has no arithmetic — no `Add`, no `Mul` — it is a *comparison* carrier
with Sturm ordering. Substituting it would let the tower represent a sine and still not compose a
turn.

The right carrier is `crates/holonic-engine/src/multiquadratic.rs`: `sin C = √d` with
`d = 1 − cos² ∈ ℚ`, so three corners land in `ℚ(√d₁,√d₂,√d₃)` — **multiquadratic**, degree ≤ 2³,
carried as the **twisted group algebra of `(ℤ/2)ⁿ` over ℚ**, graded by symmetric difference with
structure constant `∏_{i∈S∩T} kᵢ`. Exact, closed, no float, no angle.

**Its grading group is the fork.** The `2ⁿ` basis monomials are exactly `H.0150`'s membership words;
multiplying two turns is symmetric difference of their crossing words; each generator's sign
ambiguity is §2b's half turn. **The crossing-word algebra and the turn-composition algebra are one
algebra.** Measured on real material: 75 irrational corners over generators `{3, 7, 1463}`, every one
of which was `None` before.

**And then the driver refused the rung.** `coarse_grain` composes all three corners of a triangle,
and a planar triangle's angles sum to `π`, so the product is `e^{iπ} = (−1,0)` **identically** —
measured, **25 of 25 realizable triangles**. That was left as a declared open falsifier.

**ANSWERED 2026-08-10, and the falsifier was pointed at the wrong object.** `Σθ = π` per planar
triangle is **Regge calculus' founding hypothesis** — every simplex is flat and all curvature is
concentrated on the codimension-two **hinges between** them — so the `(−1,0)` receipt is
`definition`-grade and could not have come out otherwise. The rung is the **hinge deficit**
`2π − Σ_{t ⊇ h} θ_h(t)`, which is what Brandon's own `THE_MANIFOLD.md` §III said in 2026-07:
*"a founding is a deficit angle at a triangular hinge."* Built as `contact_gluing::hinge_deficits`
with `multiquadratic::sign_in_principal_embedding` supplying the declared hand a winding needs.
Measured: `1 → 5` distinct turns, `flat 5 · positive 3 · negative 3`, six hinges moving under a
non-similar metric and zero under a similarity. **`interior 0 of 11` — every link is singular — which
is not a wall: `2026-07-20_THE_HINGE_CARRIES_THE_FRAME…` §V rules that plural branches and
disconnected links are FOUND seams and that the carrier is never required to be a manifold.**

**And that record specified three more necessities, all resolved 2026-08-10.** Its §III hinge law
`delta_e = a_R|e − G(a_L|e)` is built with all four branches against a **solved orientation** — the
raw canonical hands are a chart, and reading a gluing off them was §0's fourth lesson caught by a
failing test. Its §V grain-relativity is built: **25 of 25** rank-0 two-cells are rank-1 curvature
hinges, which is the tower's upward map. And the curvature flow's coefficient is solved:
`Σ K' = (1 − 2c) Σ K`, so the module's derived `c = 1` is the **reflection** and `c = 1/2` the unique
annihilator — **`I − P` against `I − 2P`, the half turn arriving from the curvature side.**
`docs/canon/TABLET_THE_TURN.md` §§11.5–11.6 and
`research/records/2026-08-10_THE_MANIFOLD_IS_THE_INVARIANT_OF_THE_CURRENTS…`.

### `kelvin.rs`: the closure argument is a two-junction accident

The spine's own `j ≠ 0` cut organ had zero callers and zero drivers. Driving it found that its
`carried()` doc's explanation — `1ᵀ(Uᵀ)⁻¹c = 1ᵀc` because `U·1 = 1`, *"the material loop stays closed
because the flow is incompressible"* — preserves the covector's **total sum**, and total-sum equals
closedness **only when `|V| = 2`**. On a three-junction incidence all three declared closed covectors
break closure: **9 of 9 junction readings non-zero while every total sum is still exactly 0**, and
`CarriedLoopNotClosed` fires on all three. The code is right; the doc's reason is narrower than it
reads, and the module's own tests only ever used the theta graph. Sharper still: on that incidence
`⟨c,v⟩` is *still* conserved — that identity does not consult the incidence — **but the carried
covector is no longer a loop, so what is conserved is not a circulation.**

### The seam, and what it confirmed about the front

Five `_with_executor` twins now thread one mounted executor through the generation path, with a
counting-executor test that a fake twin fails. **`generate_currents` was deliberately given no twin
because it crosses no Swing event at all** — zero `ResonanceEcology`, zero `receive_with`; it is pure
host suffix arithmetic. So mounting a card on the frontier is **not** a threading problem: it
requires changing what a state-expansion *is*.

### Unreachable refusals, reported not counted

`KelvinError::{LoopCollapsed, Linear}` and `RunningIntegralError::PairIsNotACycle` cannot be reached
through their public paths — in each case an upstream check already establishes the invariant the
guard asserts. And `found_potential`'s base is a **live gauge**: 3 distinct trees, 3 distinct chords,
4 distinct potentials over 4 bases, with `|residual|` the single invariant. The module's own tests
only ever called it from one base, so base-invariance had never been separated from base-blindness.

---



---

### The seven results this session established, in one place

1. **The limit is receiver-indexed.** *"the limit occurs when the mechanisms that transform
   information during transport can no longer contribute or experience potential differences about
   each other"* (2026-08-09). `H.0208`'s boundary had named its own admission condition — *"not a new
   limit operation until its topology or convergence receiver is specified"* — and this supplies it.
   It defines **no new limit operation**; the content is the index, which makes disagreement a
   theorem with a witness rather than a paradox.
2. **The tower is one identity.** `c² = |a − be^{iγ}|²` and `|α₁+α₂|² = |α₁|²+|α₂|²+2Re(α₁ᾱ₂)` are the
   same equation; Pythagoras is the tower with the relation switched off. His canonical definition,
   2026-06-14: *"the tower is a Feynman diagram that encapsulates the law of cosines."* The rungs are
   sum/cross/exponent = similar/orthogonal/diagonal.
3. **The squared modulus is the quotient, and the deletion is what makes it one.** `|α|² = αᾱ` is the
   quotient by the phase circle. His two rulings — that `|·|` collapses information (2026-06-28) and
   that the squared modulus is the offset from the central axes (2026-08-10) — are one statement.
4. **Why `1/2`.** No preferred measure ⟹ unitarity needs `√(Jacobian)` ⟹ the state is a
   **half-density** ⟹ the root's sign ambiguity is the half turn ⟹ resolved by a **double cover**,
   which `structure_group.rs::CentralDoubleCover` already computes. That is the fourth face of §3's
   `1/2` and it is the one that explains the other three. His own geometric reading is the triangle:
   *"you quite literally cannot have a rate of change without two axes, and that is ontologically
   what ½ is"* (2026-07-24).
5. **Crossing depth carries the hand.** `n` regions cut a face into `2^n` pieces, one per membership
   word — his `2^x` and the Venn count are the same object — and inclusion–exclusion's `(−1)^{k−1}`
   is the Möbius function of the Boolean lattice, i.e. a **reversion**.
6. **Flux locality is the parallelization license.** A computation over a partition decouples exactly
   to the extent that its terms are boundary fluxes; every term that is not a flux is a barrier.
   Kirchhoff is continuity with **no storage**, not a law. **It licenses a decomposition and never a
   schedule** — interchange must be proved for the material.
7. **Loss is non-commutation.** `ρ = ρ̄ ∘ q` *is* commutativity of the receiver square, so loss is its
   failure, witnessed by a collapsed pair; where the target subtracts, the residual is a holonomy and
   a scalar loss is one receiver's face of it. **Recovery adjoins a channel**: if `q` is not
   injective there is no left inverse at all, so recovery is always from `image ⊕ channel` and the
   channel is purchased. `receiver_exact_compression.rs` already returns the minimal one — the
   shortest distinguishing word.



---

## 12. Standing corrections to the record

These are established by review and are to be carried forward, not re-derived.

**CORRECTED 2026-08-14, and the correction is that this paragraph collapsed two different claims.**
It read: *"The figures the first four bullets correct no longer exist… the same loss as the tiger
figures… not available to re-examine, and no claim may cite it as evidence."* **The atlas is on disk,
viewable, and reproducible from a driver in this tree.**

- **The files exist.** `/home/b/Workspaces/laboratory/output/arithmetic-dimensional-receiver/morphology-atlas/`
  — 111 files, 66 MB. Brandon displayed two of the contact sheets on 2026-08-14.
- **What is true is narrower and is a fact about git, not about availability.** `/output/` is
  `.gitignore` line 3 in the laboratory, so `git ls-files` returns zero at all 1,726 commits. **No
  producing commit binds the bytes** — that is the recoverable claim, and it is why
  `tools/baselines/OUTPUT_MANIFEST.tsv` and `tools/baselines/CLOSURE_MANIFEST.tsv` exist. The `git ls-files` grep is the
  wrong instrument for asking whether a return survives.
- **It is not unported; it is UNRUN.** The producing driver
  `crates/holonic-engine/examples/arithmetic_dimensional_receiver.rs` is **byte-identical** between
  the laboratory at `a07ff376` and this tree (verified by `git hash-object`), with the
  `HOLONIC_MORPHOLOGY_SWEEP` gate at `:1070` and fifteen sweep-state literals at `:1073-1177`. One
  command reproduces the atlas. This repository's `output/` holds only a 2026-08-09 run *without* the
  sweep variable.
- **It is not the tiger loss.** Those have zero surviving bytes anywhere. `runs/` also survives at
  54 GB, including the `dialogue-distractor-scaling` report this file elsewhere calls gone.

So the corrections below stand as *readings not to resume*, and the atlas **may** be cited once
re-run under a recorded commit. The winding law is confirmed by direct reading of the artifacts:
coarse sides equal the smaller prime in every pair, and every contracted hull word is one complete
positively-oriented degree-one cycle through `ℤ/pℤ` with every step exactly `+1`. **Dilation leaves
germs and corners invariant — it is a gauge; turn moves the corner count — it is not.** The one file
worth porting is the laboratory's tracked renderer `scripts/render_arithmetic_residue_receipt.py`.

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



---

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



---

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
grade that `docs/plans/THE_ROADMAP.md` holds open.




---

## Moved from §5, §8 and §11 on 2026-08-15

  **And there is one live boundary on it**, found 2026-08-08 by building the rest wire:
  `without_stem` retains the surviving stems' original `StemId`s, while `from_founded_words` —
  the only foreign constructor — *derives* ids from arrival order. An ablated morphology therefore
  cannot round-trip through that seam, and `crates/holonic-life/src/conditioned_rest.rs` refuses such a body
  **at the seal, by name, with a negative control**, rather than sealing something it cannot
  reproduce. Lifting it needs `FoundedMorphology::from_founded_stems(Vec<FoundedStem>)`.
- **Multimodality with no fusion module and no pair product.** RELAMPAGO: optical, five-band
  spectral, geolocation, and vertical sections on one eighteen-coordinate phase face; 24,584 and
  21,147 relations opened with zero pair overlap and the complete pair product never enumerated;
  14,355 relations generated before return; no-return control entirely OPEN; reversed delivery
  prediction-exact; 31.4 MB standing remounted exactly.
  **Bounded, 2026-08-07, and this bound belongs with the claim rather than in a separate errata:**
  `docs/canon/THE_RECOVERED_LAW.md` records that **all 21,147 spectral pairs returned apart** — zero
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

---

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

---

**CORRECTED 2026-08-09: this paragraph carried a COMPOSITE quotation attributed to Brandon, and §9
convicts exactly that.** It read *"Do not remove chronology. Let informants couple through the
capacitance they enable about one another, and let sparse lightning-like leaders derive a resonant
image of the retained patterns."* That sentence occurs **nowhere** in 13,376 unique messages across
`~/.claude/history.jsonl`, `~/.codex/history.jsonl` and all 316 Codex rollouts. It was assembled out
of two real things. Both are restored here verbatim:

---

  **The check is one question asked before the receipt is written: which declared input, if I varied
  it across two members of the same returned class, would move them apart?** If the answer is "the
  one I set equal for both," the class is authored. Brandon stated the general form on 2026-08-12 at
  17:14 — *"it is absolutely foolish that you would establish the parameters of the experiment and
  then be surprised when you did not run an experiment that would invoke that kind of behavior"* —
  and §0g deposited it as *"an archetype does not define the experiment"* at 17:37. The next
  experiment carried the same shape at 18:36, which is why the abstract statement was not enough.
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

---

**CORRECTED 2026-08-10 by reading the owner: `reopening.rs` HAS an external mouth and is driven
through it.** This paragraph read *"`reopening.rs` has **no external mouth.** Every `ExactFace`
constructor requires an exact source"* and named a missing constructor. The constructor exists:
`ExactFace::from_binary_float` at `crates/holonic-engine/src/reopening.rs:492`, documented as the
mouth at `:109-117` — *"The mouth: where a real float enters… No float crosses into this file. The
mouth takes a `BinaryFloatDatum`, which is `BigUint` and a power of two"* — and driven by
`crates/holonic-engine/examples/a_float_is_a_dyadic_and_a_deleted_tail.rs`. The IEEE-754 codec it
consumes is `exact_value.rs:621`, the workspace's one declared floating-point exception, four
functions each a single `to_bits`/`from_bits` with no arithmetic on a machine float.

---

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
[the record](../../research/records/2026-08-06_THE_TREE_CONDENSES_FOR_FREE_THE_REMAINDER_IS_THE_DEPARTURE_FROM_A_FOREST.md).


---

## §11 · the `positive_form` misparse, in full

| **positive form** | **RE-CORRECTED 2026-08-13 by opening the file: `positive_form` is LIVE.** It is `crates/holonic-engine/src/supported_realizers.rs:311`, called from `induced_placement` at `:333`, and imported by three drivers — `substitution_realizer_placement.rs:47`, `derivation_moves.rs:54`, `the_realizer_places_itself.rs:82`. The 2026-08-11 row said it *"was REMOVED 2026-08-08"* and that was a **misparse of the module's own sentence**: the header reads *"A test asserting it was removed 2026-08-08"*, whose subject is **the test**, not the function. What was removed is the assertion that `MᵀM` is positive semi-definite — rightly, because `xᵀ(MᵀM)x = \|Mx\|² ≥ 0` for *every* integer matrix and *every* probe, a positivity that cannot fail, which the tautology rule convicts as a check whose material cannot vary the property under test. **What stands unchanged is the open item:** the module's honest content is rank and cokernel (`the_gram_nullity_is_the_corank_of_the_incidence`), `induced_placement` computes Gram rank/nullity, no spectral placement is induced, and **the demanded positive form — one whose positivity CAN fail — remains open.** The standing example of the right shape is `matroid_hodge_riemann`, whose outside-the-cone classes are *required to break* it and do. **Carry the misparse, not just the repair:** a correction that convicted a live organ, deposited in the file every session reads first, survived two days and would have caused the next session to rebuild what it already owns. |


---

## §5 · the recruitment-wall litigation, in full

**There is one named open construction here, and it was miscarried as a wall until 2026-08-08.**

Across `0/127/254/508/1009` dialogue occurrences the deed, minimal witness, five leaders, two waves,
and thirteen visits stayed invariant. **Consequence isolation is established.** That half stands.

The other half — *"scale-independent recruitment does not"* — was **withdrawn 2026-08-08** after
Brandon challenged it as imposed and the source was re-read. It is wrong in four ways, and the
source record refutes it directly:

- **It is false on its own terms.** What recruitment *returns* is already scale-independent — **40
  return visits at every nonzero scale**, unique returns `25 / 27 / 27 / 24`, *lower* at the largest
  corpus. What grows is the candidate **sweep**. The sentence named the returned quantity and
  reported the swept one. The four-point wall-clock series, and why it cannot separate linear from
  `n log n`, are in [`docs/canon/THE_CONTRACT_PROVENANCE.md`](THE_CONTRACT_PROVENANCE.md) §5.

**Corrected again, same day, after actually reading the laboratory.** An earlier form of this
paragraph said the two remedies were "an unimplemented formula" and cited a `MinCover` grep
returning zero in *this* repository. That was archaeology on a July record instead of a look at the
body that ran it, and it is wrong twice over.

**Both remedies exist as working laboratory code**, one layer away from where they were wanted:

| remedy | owner at `a07ff376` |
|---|---|
| factor the receptive star, `I(R) = ⋃_K ⋂_{f∈K} I(f)` | `crates/holonic-life/src/relational_language/ecology.rs:1501` `clause_region_incidence` — the intersection form, with the cover founded on the receiver's own clause and entity morphology exactly as demanded, never inverse frequency. Plus `morphological_language/ecology.rs:437`, which falls back to the union when an intersection is empty, so a single-feature alternative stays lineage rather than being declared false. |
| provisional contact ≠ continuing cultivation | `crates/holonic-life/src/holonic_training.rs` — `propose_views` / `commit_views`, generation-checked and refused intact if another return moved the generation first; with `minimum_recurrence ≥ 2`, so a route is retained but inactive until it recurs across **distinct** occurrences. And `src/crates/holonic-membrane/src/live_holon.rs:204` `ProvisionalSettlement`, a two-phase prepare/commit primitive. |

**And the laboratory withdrew the framing itself, twice, before it froze.** 2026-08-01: *"This is not
evidence that broad recruitment should be reduced."* 2026-08-02: *"Broad recruitment remains
lawful."*

**A composite quotation was carried here until 2026-08-09 and is struck.** *"Do not remove
chronology"* is his, confirmed by him directly; the capacitance/lightning-leader sentence is his
2026-07-29 Codex message, quoted in full in
[`docs/canon/THE_CONTRACT_PROVENANCE.md`](THE_CONTRACT_PROVENANCE.md) §5. The two were welded into
one sentence that occurs in no transcript. **A fabricated ruling manufactures authority and no later
reader re-checks a provenance line** — which is why this one sat in the operating contract itself.

> *"Do not remove chronology"* — his, and he confirmed it himself on 2026-08-09: *"The \"Do not remove
> chronology\" line is from me, I did write that quote, it comes from a Codex conversation."*

> *"you can emergently couple informants by letting dynamics unfold through the capacitance the
> informants enable about each other. We don't need perfect simulations and data, we just need to
> couple recurring patterns and let the machine efficiently explore with 'lightning leaders' in order
> to derive a resonant image of patterns in the information."*
> — 2026-07-29 19:12, `~/.codex/history.jsonl`

§9 is precise about why this is worse than a wrong figure: *"a fabricated ruling **manufactures
authority**, and no later reader re-checks a provenance line."* This one sat in the operating contract
itself, where every later session reads it as law.

In that run one germ recruited 1,159 of 1,556
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
(`set_site_capacity`); `co_present_branch_population` is competing current occupancy.

**CORRECTED 2026-08-09: the fifth input has a term too, and this paragraph said otherwise for a day.**
It read *"Only source continuity has no term."* `crates/holonic-engine/src/derivation_capacitance.rs:769`
carries `CharacteristicDelayLaw::SourceContinuity`, which sets

```text
characteristic_delay = 1 + (minimal line separation, over the artifacts founding the head,
                            between the theorem line and the nearest line naming the tail)
```

**and it is driven with its orbit exhibited**, at
`crates/holonic-engine/examples/the_terrain_dilates_the_passage.rs:707-745`: the passages the term
moved are named one by one, and the class count goes **down**, `Uniform → SourceContinuity`, because
separating arrivals by their source separation *de-congests* the interior site that a uniform delay
made superpose. The driver states the reading that keeps it honest — *"that is the coupling running
the other way and it is evidence the term is doing work, not evidence that source continuity improves
a reading. A capacitance reading is not a quantity to be maximised."* The deferred branches are
exhibited rather than lost.

**All five inputs are built.** What remains is narrow and is a *different material*: the soma caller
below still pins its clause-pair edges, and a clause pair has no source lines to separate, so it
needs its own continuity term rather than this one.

**And "unit cost makes a high-incidence hub artificially fast" is backwards.** A high-incidence hub
has the most active outgoing passages, so the largest `co_present_branch_population`, so the largest
dilation. Congestion already penalises exactly the hub the record called fast. What is genuinely
owed is narrow: `characteristic_delay` is pinned at `1` by its **one caller**
(`crates/holonic-life/src/relational_language/ecology.rs`, lines 626 and 639), not by the law, which accepts any positive
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



---

## Moved 2026-08-15 — §11 the enclosure enumeration

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



---

## §8 · the clock/carrier conviction, in full

  **Two measured findings, and the first changes what the rule can promise.** On real material the
  work vector **never orders the two carriers**: the candidate is
  `(host 0, device 2060, transfer 288)` against the authority's `(host 2060, device 0, transfer 0)`
  — one coordinate strictly less and two strictly greater, hence **incomparable, not tied**. The
  carriers trade host evaluations against device evaluations plus transferred octets, and *nothing
  in the material prices that exchange*. So a **declared receiver metric is load-bearing**, and the
  rule's honest form is: the work vector removes the clock, and where it returns `Open` a *declared
  metric* decides — never elapsed time. Second, `CarrierWork::of_host_authority` predicts 2060 host
  evaluations where the host law performs **649**, a 3.17× over-prediction whose *ordering* survives;
  the magnitude is refuted and returned as evidence. Neither figure was obtainable from a clock.

  **What was convicted, as provenance.** At `cuda_aperture.rs:818`, where
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
  [The record](../../research/records/2026-08-08_THE_CARRIER_IS_ADMITTED_BY_ITS_WORK_NOT_BY_THE_CLOCK_THAT_WATCHED_IT.md).

