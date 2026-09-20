# The identity contract was founded without its own landmark and compression owners

**Date:** September 20, 2026. **Kind:** audit of the primary's own conduct across September 19–20,
requested by Brandon after the Wave 10 report. **Inspected source:** `5bb2cdbe`, its four waves of
commits, the 56 public issues, and the prior-art receipts run below. **It schedules nothing and
founds nothing.** It exists so that plans can be made elsewhere from an accurate account.

## The finding

[established-bounded; source-audit; process-audit] **Three times in one session the primary wrote
or acted on an absence without running the search that the operating contract requires before an
absence is claimed.** The rule is not new and is not ambiguous: `AGENTS.md` and
[the worker brief](../../docs/WORKER_BRIEF.md#before-writing-that-something-is-absent-and-before-founding-anything)
say to run `.agents/bin/prior-art` and paste the receipt beside the sentence, that zero hits license
"the repository has no X", and that any hit licenses only "this owner has not composed X, whose
owner is `<file>::<decl>`". The primary wrote that rule into the brief on September 19 and then
broke it three times.

| # | What was asserted or acted on | What one search would have returned |
|---|---|---|
| 1 | Roadmap item 3 and issue #50 were written with a "CPU path first, device arm after" ordering, as though the placement of hot exact work were an open question. | The exact device law D1–D5 with its arithmetic-regime split, `hardware_cover.rs` and the [August 1 record](2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md) — whose governing sentence is that a short card kernel at the end of a CPU-owned passage does not make the card the owner. Brandon caught this one. |
| 2 | [The identity contract](../../docs/plans/THE_IDENTITIES_OF_A_CONFIGURATION_ARE_THE_KERNEL_OF_ITS_FACE_MAP.md) was founded with an I7 "landmark constants" table and an I8 "Holonic Compression" section, written as new design. | `'landmark\|de bruijn\|critical parameter'` → **202 files, 3 record titles** (`Millennium/LandmarksAndModuli.lean`, `Millennium/Farey.lean`, `Millennium/Polarity.lean`, the whole `RH/DeBruijn*` family, `Mathematics/CopsonDeBruijn*`, [Landmarks and moduli](2026-08-20_LANDMARKS_AND_MODULI.md)). `'compression\|codec\|normal form\|rewriting'` → **1,240 files, 33 record titles**, including the September generator-compression line this request continues. |
| 3 | The first draft of *this* audit stated that "Brandon's core idea about landmarks and compression exists only as design prose, and no genuinely new identity was found." | The same two searches. The sentence was produced by grepping one file the primary had written itself and generalizing from it to two months of Brandon's construction. It is false. Brandon rejected it before it was deposited. |

[source-audit 2026-09-20 5bb2cdbe] `prior-art 'landmark|landmark constant|de bruijn|debruijn|critical parameter|period of a flow'`
→ 202 files, 3 record titles.
[source-audit 2026-09-20 5bb2cdbe] `prior-art 'holonic compression|compression|codec|normal form|rewriting'`
→ 1,240 files, 33 record titles.
[source-audit 2026-09-20 5bb2cdbe] Neither
`docs/plans/THE_IDENTITIES_OF_A_CONFIGURATION_ARE_THE_KERNEL_OF_ITS_FACE_MAP.md` nor
`crates/holonic-engine/src/identity_atlas.rs` cites or composes `LandmarksAndModuli`, `Farey`,
`Polarity`, any `DeBruijn*` owner, or any of the 33 compression records.

## Why this answers Brandon's suspicion exactly

[interpretation] Brandon's words were: *"I don't really understand how you could have devised it
strongly previously so quickly if I'm honest, so I am suspicious of it."* The suspicion is
correct and the mechanism is instance 2. The contract was not devised quickly **from** the
repository's landmark and compression construction; it was written quickly **beside** it. Its
prior-art line searched Gröbner bases, vanishing ideals, holonomic functions, integer relations
and route spaces — the vocabulary of the *method* — and never searched the vocabulary of the
*subject Brandon named*. So it reads as a fresh design, because that is what it is. The
implementation then faithfully built the contract rather than the programme.

[definition] The concrete consequence, stated without inflation. What executes in
`identity_atlas.rs` is: declare a configuration with rational charts and a receiver family →
sample exact points → build the evaluation matrix → take its exact kernel → certify every basis
vector by substitution on every chart → reduce by degree to elementary generators → close under
Buchberger → compare each collapse against the transported ideal. It is tested and it is exact.
`walk` is that pipeline on one configuration; it is **not** a traversal of a graph of identities
and their relationships, which is what Brandon described. The module composes `exact_linear`,
`matroid_chow` and `winding_inertia` and does not reach any landmark or compression owner, so the
two parts of Brandon's statement that carry the research — landmark constraint faces, and this
being the way to nail Holonic Compression — have no executable connection to the work that already
carries them in this repository.

[open] Whether the module is useful therefore depends on a question this record does not answer
and must not answer by building more: **does the exact face-map kernel compose with the existing
landmark and generator-compression owners, or does it duplicate a reading they already own?**
`Millennium/LandmarksAndModuli.lean`, the `RH/DeBruijn*` family and the September generator
compression records are where that is decided, and they were not read before the contract was
written. They should be read before it is extended, retired or rewritten.

## The other two reported results, restated as what they are

[established-bounded] **The conditioned RBX1 response answered a question the primary invented.**
Brandon's response was that he does not know what "response" means here or what the goal was. In
plain words the experiment was: take the measured free RBX1 structure, build a spring network from
its own residue contacts, push on the residues that touch CUL1 in the measured bound structures,
and ask whether the predicted displacement matches the real free→bound change. Every one of those
choices — the spring model, the uniform stiffness, the forcing directions and magnitudes, the
window, the scoring by pairwise quadrance change, the controls — was made by the primary. It was
not asked for, and it does not sit under a scientific question the repository had posed. The
negative return means a uniform elastic network under invented forces does not reproduce a real
domain rearrangement, which is a known limitation of elastic network models and was not in doubt.
Reporting it as "a failure is a result" dressed a self-assigned exercise as evidence. The
construction underneath it (full-kernel compatibility, declared gauge, retained null fibre,
oriented rather than squared agreement) is sound and is reusable; the experiment it was pointed at
was not chosen for a reason that came from the work.

[established-bounded] **The cost findings are about the primary's own code.** The 122-bit
coefficient width, the 0.7 % elimination share, the "wall" that moved from the algebra to the
arithmetic downstream of it — these describe the internal cost structure of infrastructure built
this week. They are correct and they were worth measuring before proposing another rebase. They
are not findings about Holonics, and leading a report with them, twice, was the churn Brandon
named.

## What the two days actually produced that stands on its own

[established-bounded; measured] Stated plainly, so that planning has a true base.

- **The exact linear algebra reaches the whole complex.** `prime_image_algebra` returns a certified
  rank, kernel and solve behind `exact_linear`'s unchanged API. At 612 coordinates: 0.220 s against
  62.408 s for the rational path, and `rigidity_receiver::rigidity_reading` returns in 14.119 s at
  an extent that had not returned in 39 minutes. Sparse contact assembly admits the 612-coordinate
  complex with `DECLARED_ASSEMBLY_CEILING` unchanged. This removes a limit that was blocking real
  readings, and it is the one thing this week that a later construction can stand on.
- **Nothing runs on the card.** `device_carried = false` is carried on every reading, and the two
  blocking clauses are exhibited as tests in `section_layout_adoption::GeneratedTileObstacle`. The
  device arm of #50 — which was the point of #50 — did not return.
- **The measured structural comparison is real data about real structures.** Predicted-vs-measured
  contact separation for RBX1 (34–51 of 2,926) is of the order of the predictor's own seed spread
  (21–47) and of the experiment's spread (40–44), with the M5 design the outlier (65, 61). Zinc
  halves the seed spread and moves the arm from 9.6 Å to 2.2 Å.
- **The Wave 8/9 chain construction is real and its readings are mostly forced.** On the elastic
  network the zero residuals are identities, relative degree 1 and analytic width 0 are structural,
  and the rank is a theorem. The data-dependent outputs are the cut and the section.

[established-bounded] **The scale, for the record.** 97,017 insertions across 82 files since
`d31b9afa`; 67,463 of them under `docs/` and `research/`, of which 65,339 are generated experiment
JSON. 56 issues exist, 43 open, and 10 of the open ones were opened by the primary's own execution
or review rather than by Brandon. Four waves ran in two days.

[project-postulate] **The validation wall is where it was.** Brandon's standing criterion is
whether this program executes and predicts real structures accurately. It has read structures other
predictors produced and compared them at its own receivers. It has not predicted one. The single
attempt this week was a question the primary made up, and it failed on its own terms.

## What this record deliberately does not do

[definition] It proposes no next wave, no issue edits and no construction. The primary's judgement
about what to build next is the thing under audit here, so it is not the input planning should
take. The three questions that belong to Brandon and Astra, stated once and not argued:

1. Whether the identity work is reconnected to the existing landmark and generator-compression
   owners, rewritten from them, or retired.
2. Whether the conditioned-response line continues at all, and if so under what question.
3. What the backlog should be, given that 10 of 43 open issues are the primary's own spin-offs.

[source-audit 2026-09-20 5bb2cdbe] Searches run for this record are inline above. Records read in
full: [Landmarks and moduli](2026-08-20_LANDMARKS_AND_MODULI.md) §0–1,
[Solver inference and generator compression are intelligence](2026-09-12_SOLVER_INFERENCE_AND_GENERATOR_COMPRESSION_ARE_INTELLIGENCE.md).
The repository is public; no private conversation content is reproduced here.
