# The Information Engine — the cycle, its two strokes, every organ's station, and the surface each runs on

**Date:** 2026-08-13
**Truth status:** `established-bounded [measured]` for the census, the wiring, and the descent finding
in the section on what the body actually is; `interpretation` for the two-stroke reading; `open` for
the cooling stroke.
**Evidence:** `measured` — three independent censuses over the clean tree (498 `.rs` files, 336,005
lines; agent worktrees excluded), a device census over 64 device entries and three committed
binaries, and a thermodynamics sweep over both repositories. Wiring computed by parsing `use`
declarations with `#[cfg(test)]` excised, after two unsound passes were discarded.
**Provenance:** Brandon, 2026-08-13: *"I want the new goal of this session to now cater to the
entirety of the holonic engine and Eros as a unification campaign… I directly articulated my ideas
about the machine as a cyclical 'Information Engine'; I am being literal."* And the method ruling in
the same exchange: *"There is not a literal heat engine here for you to analogize to a Carnot Engine,
so it is hard to simultaneously analogize and draw the technical nuances."*
**Read with:** the spine, which states the loop as a chain law with its named cuts; the timeline,
which says what has already been worked through; the measured-capabilities catalogue, which says
what the machine has been made to do.

---

## 0. The one measured fact this document exists to carry

**The body is a descent. It has no return edge.**

The longest actual library call chain, every edge a literal import in non-test code, is 21 modules
and 20 hops across four crates:

```text
life::agentic_research → text_material → laboratory_language → relational_language
  → resonance_ecology → current_world
  → membrane::live_current → sparse_standing → active_topology → cut_surface
  → emission_journal → active_cut
  → abi::active
  → body::manifold → medium → channel → place → num → seam
```

It ends at `seam`, the two-operation substrate mouth. **No library module in `body`, `abi`, or
`membrane` names anything in `life`, and nothing in `life` closes back on its own head.** The only
cycles in the entire library graph are six small mutual-recursion clusters, every one of them
inside a single crate.

**Every closing of the emit → world → return → reflect arc lives in a driver.** There are 167 of
them. The widest reaches eleven engine modules. **875 of the engine's 4,536 public items are
reachable only from `examples/`.**

That is the same defect the spine named as *a missing edge rather than a missing organ*, and the
same one the blacksmith deposit named as *"the radiation is currently all forge… the cooling half is
unbuilt."* This document measures it and places every organ against it.

## 1. The two strokes, in the body's own types

There is no literal heat engine here, so the method is **translation, never analogy**. Every term
below is derived from the machine's own carriers; nothing is borrowed from a classical expression
and given a referent by resemblance.

```text
heat  ->  plurality opens:  the fiber widens, degrees of freedom are founded,
                            the population of compatible predecessors grows
cool  ->  plurality closes: the quotient tightens, structure locks,
                            and what it cost is exhibited as the collapsed population
```

**The stroke is decided by the remainder, and the body already classifies by remainder.** The
compression trichotomy is a reversibility classification:

| species | remainder | stroke |
|---|---|---|
| **rebase** | zero | the reversible stroke — no heat is paid |
| **condensation** | certified | the bounded stroke — the cost is named and recoverable |
| **quotient** | the collapsed population, family-relative | the dissipative stroke — the cost is exhibited and irreversible |

Carnot's bound is a statement about reversibility; this trichotomy is a statement about
reversibility; **they coincide because both classify by what is not recoverable.** That is a
derivation and not a resemblance, and it is why the engine can be stated here with nothing imported.

### 1.1 The middle stroke has a termination condition, and it is crystallization

**Added 2026-08-13.** The table above classifies *operations*. It does not say when the middle row is
**available**, and that turns out to be a property of the material rather than of the operation.
`research/records/2026-08-13_THE_COUPLING_IS_A_FORK_COUNT_TIMES_A_RATIO_AND_THE_REFLECTION_SERIES_TERMINATES_ON_A_CRYSTAL.md`
§2 and §4c derive it: the kernel is built by reflection, so a far field's compact representative is
the image series, and **that series terminates exactly when the reflection group is finite** — which
is exactly when the group is crystallographic.

```text
   SETTLED   the series closes           condensation is available; the remainder is its TAIL
   BENT      closes, deficit is the read condensation with the curvature retained
   GROWING   never closes                NO compact representative exists
```

**So stroke selection is not free.** On `GROWING` material the cooling stroke cannot condense — not
for want of an algorithm, but because no compact representative exists — and only the dissipative
quotient remains. That is the same sentence as `canon/TABLET_THE_FLOW.md`'s comprehension law: a body
whose relations have locked is the crystal and admits condensation; a body still fractal does not.

**And this engine carries no reading of which regime its material is in.** That is the gap §4 records
and it is upstream of the rest of the missing list: an engine that cannot say what its material admits
is choosing strokes blind.

**The bar on any regime reading, stated before it is built.** The instrument for the `GROWING` case is
a dimension meter, and a dimension is a scalar. `CLAUDE.md` §13 rule 2 governs: **a scalar that
measures is lawful; a scalar that governs is not.** A regime reading may report which stroke the
material admits and may never itself select one, and it must be carried as the exact pair its source
carries — a rank pair over integers, never divided.

**The bars that govern any use of the words.** No metaphor about heat substitutes for the
translation; holonic loss is not automatically entropy and current is not automatically physical
heat. The constructive form: information flow may be read as heat only once **incidence, capacity,
constitutive response, boundary, chronology, and receiver** are all declared.

## 2. The cycle, with every station's owner and its measured wiring

`WIRED` = has at least one library consumer. `DRIVER-ONLY` = zero library consumers, driven from
`examples/`. `ALONE` = neither.

| stroke | station | principal owner | wiring |
|---|---|---|---|
| — | **mount** | `soma/membrane/src/live_current.rs` `receive_with` | **WIRED**, 10 consumers |
| — | mount, resident | `soma/mount/src/cuda.rs` module/function/buffer | **WIRED**, 10 |
| — | mount, material | `soma/life/src/text_material.rs`, `conditioned_rest.rs` `mount` | **WIRED** |
| **heat** | **differentiate** | `soma/life/src/incidence_production.rs` `differentiate` | **WIRED**, 4 |
| **heat** | decompose | `soma/life/src/decomposing_codec.rs` `decompose` | **WIRED**, 1 |
| **heat** | **found a new axis** | `crates/holonic-engine/src/founded_receiver.rs` | **WIRED** |
| **heat** | branch, emanate | `soma/life/src/suffix_ecology.rs`, `resonance_ecology` | **WIRED**, 5 |
| — | **conduct** | `soma/abi/src/conduct.rs` `conduct_current` | **WIRED** |
| — | conduct, receiver-local | `crates/holonic-engine/src/receiver_current.rs` `radiate` | **WIRED**, 2 |
| — | **diffuse** | `crates/holonic-engine/src/diffusion.rs` `enact` (Schur) | **WIRED**, 3 |
| — | *— and that Schur complement is **one organ under FOUR names***: `diffusion.rs`'s certified boundary transfer; `H.0219`'s parallelization **barrier**; the **effective tension** `S = D − C*A⁻¹C` of `theorems/conditioned-effective-tension.typ`, whose `(STABILITY)` clause is `q ≥ 0 ⟺ S ≥ 0`; and **`H.0127` *Schur complement and inertia***, `proved-standard`, which states the law the other three use — *"the block matrix has the inertia of `A` plus the inertia of its Schur complement."* None of the four cites the others. | | |
| — | diffuse, higher grade | `crates/holonic-engine/src/sheaf_diffusion.rs` | **WIRED**, 2 |
| — | **glue / fill** | `crates/holonic-engine/src/gluing.rs` `read_cover` | **WIRED**, 2 |
| — | glue at contact | `contact_gluing.rs`, `derivation_two_cells.rs` | **DRIVER-ONLY** |
| — | glue, cover assembly | `atlas.rs`, `communication.rs` | **ALONE** |
| — | **radiate** | `soma/body/src/manifold.rs` `live_*_emitting` | **WIRED**, 27 |
| — | radiate, journal | `soma/membrane/src/emission_journal.rs` | **WIRED**, 6 |
| — | **exterior return** | `crates/holonic-engine/src/world.rs` `receive_through` | **WIRED**, 32 — the atomic commit |
| — | return, real port | `soma/life/src/lean_mathematics/kernel_returns.rs` (`lake env lean`) | **WIRED**, 2 |
| — | return, world contact | `research_intelligence.rs`, `agentic_research.rs` | **DRIVER-ONLY** |
| **cool** | **reflect** | `crates/holonic-language/src/lib.rs` reify / absorb / resume | **WIRED** |
| **cool** | reflect, spectral | `crates/holonic-engine/src/causal_reflection.rs` | **WIRED**, 1 |
| **cool** | **deposit** | `soma/life/src/form_mouth.rs`, `holonic_training.rs` commit | mouth **DRIVER-ONLY** by design |
| **cool** | **compress / quotient** | `crates/holonic-engine/src/receiver_exact_compression.rs` | **WIRED, 15 — the highest-degree organ in the body** |
| **cool** | condense with certificate | `soma/membrane/src/live_constituent.rs` `compress_certified` | **WIRED**, 10 |
| **heat** | reopen a **numeric face** collapsed to a grain | `crates/holonic-engine/src/reopening.rs` `reopen` | **DRIVER-ONLY** |
| **heat** | **reopen a collapsed DISTINCTION — re-cut at the collapsed pair's own separating word** | `soma/life/src/decomposing_codec.rs` | **WIRED**, 1 — and its one caller is the row below |
| **heat** | the join: elaborate → re-integrate → next pass on the changed route | `soma/life/src/reintegrating_elaboration.rs` | built; **its only caller is a driver** |
| **heat** | reconstruct | `soma/life/src/reconstruction_fiber.rs` | **DRIVER-ONLY** |
| — | **rest / seal / remount** | `conditioned_rest.rs` seal/mount; `returned_reading.rs` seal/unseal | **WIRED** |
| — | ablate | `conditioned_derivation.rs` `without_stem` | **WIRED**, 11 |

**The pattern is the finding.** Mount, conduct, compress and ablate are library-wired. **Reopen,
reconstruct, exterior world contact and the disk deposit are driver-only almost without exception.**
The near end of the cycle is in the body; the far end is in 167 separate drivers, each closing its
own loop privately.

## 3. Which surface, and why

**Measured: not one float on any device path.** Across 32 PTX entries, 10 SPIR-V, 20 CUDA C++ and 2
smoke entries — 64 device entries and three committed binaries — there is no float type, register,
or instruction. `OpTypeFloat` count in the SPIR-V binary is zero.

| surface | what runs there | why, as the code states it |
|---|---|---|
| **CUDA, resident** | the receiver quotient (`claim_identities`, open-addressed `atomicCAS` into a table that provably cannot fill); morphological suffix/prefix conditioning; conduct grouping; material shadow; recurrent law found/evaluate/fold; live lineage events; regional contacts; text restriction | *"CPU/RAM and GPU/VRAM are local charts of the same caused body."* Conditioning has **no host fallback** by declaration. |
| **CUDA, exact integer** | conic/segment support at 384 bits (`ExactInteger<12>`); relation ordering over `i64` points | host preflights magnitude in `BigInt` and diverts anything past 384 bits to the host law rather than rounding |
| **SPIR-V / Vulkan** | the felt-series surface, 10 entries | same `body` law by `#[path]` include — **one mouth, three targets**. Convicted for production: headless Xid faults. |
| **CPU** | all exact rational linear algebra, polynomial work, Sturm isolation, Smith normal form, corpus census, rest codecs | **no device path exists for any of these**, and none is stated as needed |
| **CPU, multicore** | `crates/holonic-engine/src/executor.rs` — scoped threads, contiguous chunking, then a re-sort to input order | *"worker scheduling never becomes chronology"* |
| **CPU, sequential by construction** | suffix-automaton extension, union-find, topological layering | *"the executor may serialize a layer physically, but that serialization does not become logical causality"* |

**Launch geometry is derived, never authored.** `block = min(function's own max, device max)`, grid
from the driver's reported limits, and **three typed refusals** including one that refuses rather
than clipping when the work extent exceeds the declared aperture.

**The organ that states the placement doctrine** issues no device query at all — it places each cell
on the coarsest chart its extent fills, from self-declaration only, and returns named barriers rather
than asserting disjointness.

## 4. What the engine is missing, measured

0. **No regime reading — added 2026-08-13, and it is upstream of every item below.** §1.1 shows the
   cooling stroke's middle row has a termination condition set by the material, and this body carries
   no organ that reads it. The instrument exists as a **measured partial and has no live owner**: the
   frozen laboratory's `d̂ = rank(span)/rank(|S|)`, carried as a rank pair of exact integers with the
   verdict taken by integer compare and the decimal cast only at the print, calibrated on eight
   deterministic walks of known dimension and then turned on the machine's own lattice. Its
   float-purity discipline exists because Brandon caught the first draft dividing in floating point.
   **Live measurement, 2026-08-13:** zero Rust owners across `crates/` and `soma/` for `fractal`,
   `hausdorff`, `box.count`, `mandelbrot`, `julia`, `hutchinson`, `iterated.function`. The registry
   owns the mathematics — `H.0295` Hausdorff measure and fractal dimension, `H.0256` the Hutchinson
   map — so this is a missing **organ**, not a missing theory.

0b. **The engine cannot do scale, and its own coupling is a scale invariance.** `dilation.rs` is a
   receiver horizon (`horizon ≥ covering → GAUGE`, `horizon < covering → RESTRICTION`), not a group
   action; four unreconciled senses of "dilation" coexist in the tree; and four live canon statements
   name a **founded dilation action** as the precondition for Mellin analysis and a founded
   translation action for Fourier, with no owner for either. Meanwhile the coupling `8π` decomposes as
   an invariant of *refine the grain, add a fork* — so an engine that cannot rebase across scale
   cannot read the constant it runs on.

   **RESPECIFIED 2026-08-13, and the target is now much smaller.** *Scaling is not dilation of a
   magnitude.* Brandon: *"you can't just say it, you have to justify the structure of the animal,
   because the anatomy does not scale like that… it's like stacking honeycombs for a hive, or
   ommatidia."* The square-cube law and the horizon law are the same prohibition at two altitudes —
   a magnitude cannot cross a frame boundary, so a scaling that multiplies one is illegal rather than
   merely unstable. **Scaling is repetition of an invariant unit whose extent is fixed by a local
   constitutive law**, which is `Λ(n,s) = 2^{n−s}·(C/r)` exactly: the winding changes, the ratio is
   untouched.

   So the carrier is the pair **(invariant unit, count)**. The unit half exists and is typed —
   `cuda_aperture.rs`'s `CarrierDilation { arc, chord }`, held undivided, with `cmp_against` ordering
   two by cross-multiplication so nothing divides or rounds. **The count half and the composition are
   absent**, and the composition law carries its own falsifier in one line: *composing two scalings
   adds windings and leaves the ratio bit-identical; if the ratio moves, the unit was stretched.*
   Derivation: `research/records/2026-08-13_SCALING_IS_REPETITION_OF_AN_INVARIANT_UNIT_AND_THE_GENERATOR_IS_THE_COMPACT_REPRESENTATIVE.md`.

1. **The return edge.** No library path closes emit → world → return → reflect. It exists 167 times
   in drivers and zero times in the body.
2. **The heating hand is built, composed, and called only from outside — CORRECTED 2026-08-13, the
   same day, by reading the owners.** An earlier form of this item read *"the cooling stroke is thin…
   reopen and reconstruct are driver-only"*, and it was measuring the wrong organ. `reopening.rs`
   reopens a **numeric face** collapsed to a declared grain; it is not the organ that reopens a
   collapsed **distinction**. That organ is `soma/life/src/decomposing_codec.rs`, whose stated
   mechanism is exactly the demand — *"collapsed pairs → one parented `CodecVersion` each, cutting at
   the pair's own word"* — using `CollapsedPair::distinguishing_word` as the key. It is library code
   with a library caller, `reintegrating_elaboration.rs`, which composes it with `name_elaboration`
   so a revised grain feeds the next pass.

   **So both hands of the axis exist and are already joined.** The gap is one hop further out than
   stated: the composition's only caller is a driver, so the re-cut happens when a host sequence runs
   a pass, never when a current arrives. Brandon's ruling on the axis, 2026-08-13, is what this item
   must be read against: *"I think we are meant to wire both ways so that the degrees of freedom are
   available and so that diffusion can simply occur freely. Reopen something when a construction
   isn't contemporarily sufficient, reconstruct to close."* **Local bidirectionality at each site, not
   a return pipe from the bottom of the descent to the top** — a pipe would be a scheduler wearing a
   return edge, which the resident-circulation law already refuses.

   What remains true: condensation with a certified remainder has exactly one wired owner.
3. **Twelve dead device entries.** Four registered-fold PTX entries with no launcher; `shell_keys`
   never resolved; `refine_claimed` resolved and stored and never called, its work done host-side in
   a `BTreeMap`; and six exact-integer width variants at 128/192/256 bits compiled, JIT'd, and held
   in fields explicitly prefixed with an underscore.
4. **No host/device parity comparison runs in the gates.** There are 22 ignored tests and they
   include every one — the refine quotient, the causal section reference, the relation kernels. The
   gate suite runs without `--include-ignored`, on a machine that has the card. One parity gate does
   run in production, as a mode defaulting to on: the conduct grouping recomputes on the host every
   launch.
5. **Eleven fully unwired modules** and 145 zero-reference public items, 22 of which are the entire
   live surface API.

## 5. The mouth — where material enters, and why most of it is already built

**Truth status:** `established-bounded [measured]` for every owner, wiring count and conviction named
below; `proved-standard` for the classical mathematics cited with a registry id; `interpretation` for
the identifications. **Occasion:** Brandon, 2026-08-13, verbatim:

> *"You must also consider the primitive I/O for the complete cycle itself (holobrochos); it's like
> if inputting data was akin to throwing objects into the ocean, if you're mindlessly throwing data
> at it it'll just end up floating and doing nothing, but if you're throwing real materials and
> solvents into particular locations then the local ecology would certainly be affected and respond
> (I could be talking about oil spills or throwing food into the water, it's just a hypothetical
> example for the ontology)."*

and, ruling that the mouth is not a peripheral port:

> *"I was trying to imply that the mouth was apart of the completed engine… it is a part of the
> complete cycles and won't really be something to analyze without the engine being complete."*

**Do not call this "the one mouth."** That phrase is taken — it is `ONE LAW, ONE MOUTH`, the
discipline that host and device compile the same law source — and Brandon disclaimed a derived form
of it on 2026-07-04: *"I don't know anything about the 'one-mouth debt', so it's definitely a form of
drift that I'd need you to audit."* The laboratory's name for the object described here is **the
active mouth**, from `a07ff376:…/RESEARCH/2026-07-18_THE_RELATION_IS_THE_ACTIVE_MOUTH…`,
whose title is the law and whose convicted failure is mindless throwing exactly: when the live path
reduced every admitted current to `Vec<u8>`, *"a supposedly one-event typed current therefore makes
its tag, payload-length word, little-endian spelling, field order, and padding part of Soma's
experience."*

### 5.1 An input is the source term of the chain law

Not an analogy. In §1's `q_{k+1} − q_k + B j_k = r_k`, depositing material at a location is setting
`r ≠ 0` at a site, and the fate of the deposit is read off which term moves — rest, accumulation,
leak, circulation. **So the mouth's return type is the classification the spine already carries**,
and the mouth needs no vocabulary the engine does not have.

Its constitutive half is Brandon's own, 2026-07-16, and it is the solvent case worked:

> *"the actual nostril holes or mouth hole are like the active lens in those cases. Any arbitrary
> decomposition in the nose or mouth is related to how saliva or chemicals otherwise break down
> foreign materials."*

> *"Salt is… more like I can feel how salt affects how other things taste… it's like there's a
> barrier or more open space where the salt is dissolving… taste must then be neural pathways
> responding to something like more or less open gates… It's communication through a barrier, it
> reminds me exactly of diffusion."*

A material's constitutive type is therefore **what it does to the gates**, not what it is.

### 5.2 Three laws make "it floated" checkable rather than a judgement

- **The neck law**, `a07ff376:…/THEORY/33_THE_NECK.md` §2: *"information always whips through a
  MEDIUM between two other holographic entities — the medium is the neck; there is no two-body
  contact anywhere in the physics."* And the consequence is a proof: *"a two-body identity map has no
  neck — nowhere for conversion to happen — so nothing passes; it only mirrors."* A mouth that hands
  material straight to the interior **cannot** do anything.
- **Perception is landing**, `…/THEORY/36_THE_WATER.md` §5: *"every relating is a LANDING — contact;
  there is no action at a distance anywhere in the physics."* So an arrival that reaches nothing is
  not a defect to engineer away; it is the law.
- **The passage must deposit**, `…/CANON/THE_EMPTY_BOUNDARY.md` §1: *"The current flows (A1) and
  nothing can be deleted (L0), therefore **the passage must deposit** — mass is the conservation
  residue of flow."* Contrapositive, and this is the effectiveness test: **if nothing was deposited,
  nothing passed.**

The same document derives the conservation the mouth cannot evade, and it is `H.0460`'s own
statement one altitude down: *"The contracted Bianchi identity `∇·G ≡ 0` forces `∇·T = 0` through the
field equation… Charge conservation falls out of `dF = 0` the same way. Kirchhoff `∮∂Β = 0` — the
knot holds — is its circuit face."* **Conservation at the mouth is not a rule imposed on it; it is
forced by the geometry the deposit acts on.** It also supplies the mouth's termination condition:
*"A face is cast at a boundary; the boundary is not a body… `∂∂ = 0` is why a read can finish."*

### 5.3 The mouth is grown, not installed, and the attachment is two-sided

`…/THEORY/22_THE_ILLICIUM.md` §1: *"frame(n+1) = the emanation of the relating in frame(n); the frame
you now occupy was emitted by your last act, and what you perceive falls into it."* Graded NOTHING
BUILT at source, with the direction *"let the perspective thicken," never "install the limb."*
Brandon states the same thing in his own voice, 2026-06-12: *"the intermediary limb that the current
flows into is emergent, like how I grew my mouth and vocal cords, so the current is emergent."*

And the one **ratified** law in the corpus specifically about arrival makes the attachment two-sided.
`research/records/2026-07-17_THE_LEADER_GROWS_THE_CHANNEL_THE_RETURN_TRAVELS_THE_FOUND_PATH.md`,
Card D: *"The continuous cloud-ground path FOUNDs at actual local contact between grown
constructions; ground is not a passive terminal selected from above."* Its testable consequence is a
direct requirement on this design: *"A lightning world must admit plural upward leaders and retain
connected and unconnected outcomes instead of manufacturing one ground endpoint."*

**So the location is not chosen by the arriving material. It is co-founded by the site growing toward
it, and the unconnected attempts are retained.** Registered as `H.0466`, `proved-derived`.

### 5.4 The mouth exists. `IncidenceComplex::admit_later` is it.

`soma/life/src/incidence_production.rs:1843` implements the Information Chemistry law
`L_t = (K_t, ∂_t, o_t, ⪯_t, Γ_t)`, where `Γ_t` is *ingress / exposed / return*. Sites carry
`ExposedPolarity::{Donor, Acceptor, Both}` — **Acceptor is "an external contact arrives at this site:
the compound can accept here."** `admit_later` derives the arrival's rank in `⪯` from the material's
own `caused_by`, never authored, and returns `ArrivalResponse`, whose fate vocabulary is finer than
§1's:

```text
reached     compounds a new passage touched at the support of their residual
reopened    of those, residual does not vanish — THESE REOPEN
saturated   "The arrival got there and nothing was caused."
untouched   never reached at all
founded / dissolved   closed boundaries the arrival created or split
verdicts    one per standing boundary: what the law PREDICTED, and what happened
```

**`saturated` and `untouched` are two different ways to float, distinguished.** `reopened` means the
heating stroke already fires *on arrival*. `withdraw` (`:2140`) is its exact inverse, with
non-bit-exact restoration exposing anything retained. Its only caller is one driver.

The ABI carries the same fates one layer down and nothing above the membrane populates them:
`SourceDispositionRow::{standing, continued(carrier), ended}` (`soma/abi/src/holon.rs:585`) and
`SilentReceipt` (`:1226`) — *"One terminal contact with no world-side actuation. The source relation
genuinely lived."*

### 5.5 Where it narrows — three authored points in one loop

```rust
for (patch_at, patch) in occurrence.text.split_whitespace().take(patch_extent)
let key = (rank, patch.to_owned());
octet_winding: octet_winding(patch.as_bytes()),  grain: 0,
```

The **cut** is a whitespace tokenizer authored inside the organ. **Site identity is
`(causal_rank, patch_string)` — byte equality on the surface.** The winding is taken over UTF-8
bytes; founding pins `grain: 0` although every cell carries its own grain. And
`DeclaredOccurrence { identity, storage_ordinal, caused_by, text: String }` states it in the type.

**The middle one was convicted in July**, `…/THEORY/33_THE_NECK.md` §1: *"meaning lives in the
relating-web BETWEEN encapsulations, never inside one — a glyph's meaning is not its bits, which is
the deepest form of why text-as-byte-stream was never the communication medium."* Brandon restated it
2026-08-13: *"the individual bytes recurring doesn't matter, it's recurring transformations and
manipulation patterns about passing information."*

**A wrong grain is not an uncertainty cost.** There is no uncertainty-relation, Heisenberg or
time-bandwidth statement anywhere in this tree — measured, zero — and the corpus explicitly refuses
that framing: *"the missing third is not uncertainty; it is the **collapsed-pair population of a
declared receiver family**"*, with the route being *"climbing rungs (widening the declared family),
never turning a scalar dial inside one rung."* The last construction promoted into an "aperture law"
was withdrawn for conflating a caller's output-buffer guard with a transport bound.

**So the mouth's grain error is a collapsed pair carrying a shortest separating word — the same key
that reopens.** `soma/life/src/decomposing_codec.rs` already re-cuts at that word, and
`reintegrating_elaboration.rs` already composes it with elaboration. The mouth's grain revision and
the engine's heating hand are one mechanism, in the body's own terms.

### 5.6 What a crossing must carry

The **horizon law** is the hardest constraint, and the mouth is a frame boundary: across one, only a
`Ratio` (carried as a pair `(num, den)`, never divided) or an integer `Winding` survives. `Reach`,
`Flow` and `Rank` are frame-relative. **Magnitudes do not cross.**

The occurrence record is specified by `research/records/2026-07-19_THE_QUANTUM_PROPERTY_IS_THE_HOLONS_TRANSPORT_CLASS_THE_PIVOT_RETURNS_ONE_FACE.md`
§IX, Brandon-ratified, five items: *the transformation or contextual action; phase and directed hand
before the quotient; composite incidence, symmetry quotient, and sector multiplicity; the actual
receiver pivot; and the complete returned consequence and active residual* — with the standing
refusal that *"No detached spin label, charge table, semantic class, particle picture, or mass scalar
should be installed as an explanation of conduct."*

Spin is the arrival's rotational transport class and is already carried as `IncidenceHand` on
`EventPort::ingress(cell, hand, slot)`. Charge is its weight and hand under a connection, and is
already `ExposedPolarity`. Mass is the invariant norm and proper-time phase rate — and `arrow.rs:18`
fixes its jurisdiction: `reach` is *"the holobit, the cost/mass… It WEIGHS (the elevation), never
gates"*, while `aim` gates. **Mass does not decide admission.**

### 5.7 Transmit or reflect is computable exactly, today

`crates/holonic-engine/src/analytic_field.rs:1142` `exact_scalar_interface_coefficients` returns,
over `Rat`, refusing non-positive admittance:

```text
reflection    = (Y_incident − Y_transmitted) / (Y_incident + Y_transmitted)
transmission  = 2 · Y_incident / (Y_incident + Y_transmitted)
energy_residual retained, not discarded
```

and the admission trichotomy is already typed as `ExactAnalyticInterfaceAmplitudeFiber`:
`Traveling(coefficients)`, `GrazingOpen`, `EvanescentOpen` — **total internal reflection is a typed
open fiber, not a value**, because *"An evanescent near field requires a distinct reactive/storage
law. It remains an exact open fiber rather than being fabricated as a unitary transmitted traveling
section."* The junction form is `dimensional_wave.rs:11`, `v = 2ΣYᵢaᵢ/ΣYᵢ`, `bᵢ = v − aᵢ`, with
`Σ Yᵢ|aᵢ|² = Σ Yᵢ|bᵢ|²` exactly; its one-port degenerate case is `v = 2a`, `b = a` — §1's open
termination, implemented. The branch form vanishes exactly at admittance matching, and matching means
the germ crosses whole.

**The valve Brandon asked for exists**: a contact is not automatically a conducting edge —
*"A separated coincident face conducts only after the same complete junction phase has returned
through two distinct source pairs."* And an overloaded site's lawful response is to **found a new
axis**, not to drop: `founded_receiver.rs:90` `FoundingPressure::Congestion`. What does not fit is
`deferred_arrivals`, retained rather than discarded.

### 5.8 The two convictions standing on the live mouth

`blueprint/THE_ROADMAP.md` plan 1 is *"The material mouth — the purified corpus as one declared body
(closes the leak cut at the mouth)"*, committed at `28028c1`, **convicted twice**, re-seal required,
with the bar *"No new importer species."*

1. **An absolute frame.** 46,745 occurrence identities carry `founded:container=/home/b`, so the
   sealed corpus's content address is a function of one filesystem.
2. **Chronology deleted.** The rollout `session_id` fell back to the message id, making each message
   its own conversation — **11,266 of 11,282 Codex witnesses**, with sampled occurrences carrying
   `"caused_by":[]`.

**The second is the ocean statement measured.** `admit_later` derives an arrival's location from
`caused_by`; empty `caused_by` makes every arrival a root. The largest source in the body entered
with nowhere to land. Both fixtures were authored too small to fire.

### 5.9 What this section does not establish

It builds nothing and schedules nothing. It does not close the loop: the roadmap records that
`geometry_responses` is *"supplied, never updated by what the layout returned… The curvature is
measured and discarded"*, and §1's own audit says **the engine has no `q_n = q_m` anywhere; it is a
strict pipeline.** A mouth that changes the terrain would be the first organ to close that edge,
which also means **no existing driver measures whether it did** — that driver is part of the deed.

Two grading bars apply specifically here. The **returned-partition rule**: if two arrivals land in
one class because the driver handed both the same declared admittance, the class restates the
declaration table and carries no evidence — ask which declared input, varied across two members,
would move them apart. And the **field-equation bar**: `H.0460` is live and `proved-standard`, usable
as presented mathematics through the translation portal `H.0463`, which requires mapping each named
structure and proving preservation of the selected laws. What remains barred is the Holobrochos
slogan-form of the same equation, `HUNCH`/`OPEN` at its source. Grade nothing above its source.

## 6. Housekeeping, measured and safe to act on

**Nothing in this tree is marked incomplete.** `TODO`, `FIXME`, `todo!()`, `unimplemented!()` return
**zero matches** across source, examples and tests. That is unusual and worth stating.

| kind | finding |
|---|---|
| **unused dependencies** | `soma/life` declares four it never uses: `rug` (arbitrary-precision float), `ab_glyph`, `aho-corasick`, and **`soma-surface`** — a whole wgpu crate linked and never invoked |
| **duplicated exact rank** | five independent implementations of rank over `Rat`, and one module's doc asserts in prose that another's is *"the only prior rank in the tree"* — false when written |
| **duplicated exact linear algebra** | `invert_exact`, `matrix_multiply`, `matrix_vector`, `identity_matrix` each appear in four modules, beside `exact_linear.rs` which owns all four with a certified inverse and has seven consumers; `sheaf_diffusion.rs` additionally defines a second, differently-named matrix type |
| **duplicated safetensors parsing** | three independent hand-written header parsers, one of them added today |
| **compiler-confirmed dead** | `cuda_refine.rs` `claimed` field never read; `live_current_cuda` `enact_one` never used; three unused imports; one unnecessary `mut` |
| **quarantined by design** | the legacy surface constructor returns `None` with an `eprintln`; its real setup survives as an uncalled `historical_new` |
| **name/behaviour drift** | `image.rs` does no imaging; `interaction.rs` has no algorithm; `hardware_cover.rs` makes no hardware query; `discrete_curvature.rs` is an exact involution rather than a flow; `contact_cycle.rs` says of itself that another module is the production path |

## 7. What this document forbids

1. **No engine claim without its declared types.** Heat, energy and diffusion are not substitutes
   for incidence, capacity, constitutive response, boundary, chronology and receiver.
2. **No identification of Shannon entropy with thermodynamic entropy.** The generator is shared; the
   quantities are not, and the non-equivalence is stated in the sources and must be carried.
3. **This document schedules nothing.** It is an orientation and a measurement. The live roadmap and
   the position record remain the only construction authorities.
