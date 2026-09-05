# The mathematics tablet

**Status:** under construction, 2026-08-08. This file is the authoritative synopsis Brandon asked
for: *"a thorough holonic synopsis that acts as an authoritative mathematics tablet… an extremely
important foundation to our ontology and research."* Sections land as they are grounded; a section
with no owner named is a section not yet written, and says so.

[project-postulate] Brandon's 2026-09-04 scope ruling: Holonics is a mathematical framework and
ontology for causal composition, information transport and physical realization. HNA is one
executable architecture within it. Mathematical research develops reusable methods of explaining
and constructing systems, including physical, biological and learning systems. A research attempt
toward a Millennium problem is not a promise that its proposed route succeeds. Its actual
derivations, counterexamples and unresolved relations determine the next construction.

**Truth status is per claim.** Standard mathematics is marked `proved-standard` with its citation.
Holonic readings of it are `interpretation` and are marked. Anything the repository implements is
`implemented-exact` with its owner. **Nothing here is a Millennium claim.**

**Quotation convention, and it is load-bearing.** A `>` blockquote is **verbatim source text**, and
the sentence introducing it **names the source**. Where the source is Brandon it is his words exactly,
his typos included, because a silently corrected quotation is a composed one. Where it is a laboratory
or canon document it says so. **Nothing attributed to Brandon here is anything but a real message of
his**, and that is the property `CLAUDE.md` §9 protects — this file is exactly the kind of document a
later reader mines for rulings.

*This convention was stated more narrowly on 2026-08-08 — "a blockquote is Brandon and nothing else" —
and then broken by the sections added the same day, which blockquote laboratory documents. Widened here
rather than by silently converting the quotes, because the narrow rule was the wrong rule: the property
worth enforcing is that an attribution is true, not that only one person may be quoted.*

Every Brandon quotation below was certified before deposit against `~/.claude/history.jsonl`, this
session's transcript, the Codex session rollouts, and the laboratory's `conv_chord` corpus at
`a07ff376`.
Certification is per-corpus and `UNCERTIFIABLE` is not `fabricated` — the surviving transcript record
begins well after much of this material was said.

**Reading rule.** Every section names the same four slots, because the framework's claims are about
the operation and not about the material (`CLAUDE.md` §4):

```text
source geometry  ->  receiver map  ->  transport  ->  returned residual
```

---

## 1. One deletion, three carriers

The project's three hardest-won laws are the same law about three different carriers. Each is a
carrier that **kept a magnitude and threw away what oriented it**, and in each case the lawful form
retains both and offers the collapse as a *reading*.

| carrier | keeps | deletes | the deleted thing is | lawful form, and its owner |
|---|---|---|---|---|
| **float** | the magnitude | the tail | the residual of the expansion | `CertifiedSeries` + `SeriesTailCertificate`, `holonic-engine/src/exact_value.rs:361` |
| **sign** | the magnitude | the turn | the winding, `−1 = e^{iπ}` | `OrientedWinding` `crates/holonic-body/src/channel.rs:111`; `RayCrossings` `relational-geometry/src/exact_analysis.rs` |
| **reduced coefficient** | the difference | the passages | which hands were actually taken | `ComparativeMultiplicity`, `holonic-engine/src/algebraic.rs`, repaired 2026-08-08 |

Brandon's sentence is the one that unifies the first row, and it is sharper than the usual argument
against floats:

> *"Floats are not real numbers, they are series expansions of ratios."*

That is exactly right and it is worth stating precisely. `C/d` is a ratio. A float is not a bad
approximation *of* that ratio — it is the ratio's **series expansion in base two, truncated, with the
remainder discarded**: `x = Σ b_i 2^{−i}`, cut at 53 bits, tail deleted with no record that a tail
existed. So the no-float law is not *"do not expand."* It is:

**You may take the expansion. You may not discard the tail.**

Which is precisely what `SeriesTailCertificate` implements — a partial sum plus an **exact rational
remainder interval**, so the returned object is a *set that provably contains the value* rather than a
point that provably is not it. §2b's sentence about signs is the same sentence one carrier over: *a
float keeps the magnitude and discards the residual; a sign keeps the magnitude and discards the
turn.*

**The laboratory deposited this law first and carried it further, 2026-06-21.**
`src/eros/um/THEORY_AND_EQUATIONS.md` §32 states it whole — *"a float is a truncated series"*, and
`0.1f ≢ 0.1_real` as two different objects rather than one object with error. It also carries the
part this section did not have, which is the **stopping rule**:

> *"you traverse the series until the provable tail can no longer change the outcome of the relating.
> For a decaying series the tail is bounded, so you know when it cannot straddle the decision. This
> is more exact than a fixed-precision float, not less."*

That is the operational form of `SeriesTailCertificate` and it predates the carrier. §43 of the same
file adds the clause that keeps the ban from becoming a ban on mathematics: *"every algorithm that
would normally output a floating point number is actually a relativistic series"* — `exp`, `ln`,
`sqrt`, `sin`, the cross-ratio are all kept; what stops is the **collapse**. Reachable only through
`git -C /home/b/Workspaces/laboratory show a07ff376:src/eros/um/THEORY_AND_EQUATIONS.md`.

**And today's coefficient repair is the third instance**, which is why it belongs in this table and
not only in a defect record. `ComparativeMultiplicity` held two arms and destroyed them at
construction, keeping only their difference. `(1,1)` and `(0,0)` share a difference and are not the
same thing: the first is two passages, once each hand — a loop edge attached to its vertex twice —
and the second is no passage. Deleting the common population kept the magnitude and discarded the
turn, in the type every chain in the engine is built out of.

**The generalization, and it is checkable rather than exhortatory:**

A carrier that reduces on construction has decided, for every consumer it will ever have, which
distinctions are invisible. No downstream check can recover one. Where a carrier holds two arms and
offers a reading that joins them, the reduction belongs in the **reading** and never in the
**constructor** — and the test for whether that line was crossed is whether any consumer reads the
carrier's support as a **relation** rather than as a domain.

---

## 2. The finite archetype claim, and where it is already checkable

Brandon, 2026-08-08, posing this document:

> *"if you consider all of the most prominent methodologies and form-factors of how mathematics is
> represented computationally, there is a finite and clear set of representations & implementation
> patterns. The word "patterns" is key there, because there is actually an infinitely large set of
> specific implementations, like expressions for pi, but it is the case that like expressions of pi,
> the forumals and implementations vary in archetype and transport classes, and the specific symbols
> that identify a unique member of the infinite set are constrained by a finite set of rules
> (codec)."*

**π is the right worked example and the claim survives it.** There are unboundedly many series for π.
They fall into a small set of archetypes, and what separates the archetypes is not the value — every
one returns π — but **the shape of the tail**, which is to say the codec that certifies a member:

| archetype | example | what bounds the tail | admitted by the built carrier? |
|---|---|---|---|
| alternating, monotone magnitudes | Leibniz `4Σ(−1)^k/(2k+1)` | the first omitted term, by Leibniz's criterion | **yes** — `AlternatingMonotone` |
| linearly convergent, ratio-bounded | Machin-like arctangents | `first/(1−ratio)` | **yes** — `AbsoluteGeometric` |
| hypergeometric | Ramanujan, Chudnovsky | consecutive-term ratio is a rational function of `k`, eventually ratio-bounded | **yes**, via the geometric bound, wastefully |
| closed remainder | any identity that folds the tail exactly | the remainder itself | **yes** — `ExactTail` |
| quadratically convergent | Gauss AGM / Salamin–Brent | error `~ε^{2^k}` — not a fixed ratio | **admissible but crudely**; the certificate cannot express the doubling |
| digit-extraction | BBP base-16 | a positional identity, not a tail bound at all | **no** — different question |
| **asymptotic, divergent** | Stirling; saddle-point expansions | optimal truncation at the smallest term; **there is no convergent tail** | **no, and this is the real aperture** |

So the archetype claim is **true, implemented for one domain, and its aperture is nameable**: the
built carrier admits three species, and all three presuppose convergence. A divergent asymptotic
series has no convergent tail to certify and is refused. That matters beyond bookkeeping — §3 of the
contract records that the `1/2` has a face as *"the saddle's equipartition `p^(−m/2)`"*, and
saddle-point expansions are exactly the divergent-asymptotic class. **The series carrier cannot
currently admit the expansions the RH-facing reading is written in.** That is an owed construction
with a name: an optimal-truncation certificate, where the remainder bound is the smallest term and
the certificate must carry *where* the truncation was taken.

**The carrier had no drivers, and now it has one — corrected 2026-08-08.** Measured 2026-08-07:
`CertifiedSeries` 13 references in one file, `SeriesTailCertificate` 6 in one, **zero in any
`examples/`, `tests/`, or `bin/` path**. Re-measured 2026-08-08 after the reopening organ landed: **26
and 15 references across three files each, one of them a driver** —
`crates/holonic-engine/examples/reopening_the_collapsed_face.rs`, which prints the tail certificate's
species and its first omitted term rather than only consuming them.

That matters beyond bookkeeping, because **the driver is what proved the tail is load-bearing.**
Fold the arctangent to 4 terms instead of 128 and the certified tail ceiling drops to `2⁻¹⁰`; asking
for `2⁻¹¹` is then refused by name, and at the finest grain the starved tail allows the search
returns **nothing**. Retain the tail — ceiling `2⁻²⁶³` — and the same basis returns `(16, −4, −1)`,
Machin's identity, as exact integers. *You may take the expansion; you may not discard the tail* is
no longer only a law about honesty. It is the difference between recovering a theorem and recovering
nothing.

---

---

## 3. Where the rest of the tablet is

**The tablet is split by mechanism, not extended.** `docs/canon/THE_DOCUMENT_LAW.md` §1.2: a canon file
past roughly six hundred lines is split, because §6.2's convicted defect is *a file no one can
hold*. This file is the spine — the one deletion at its carriers, the archetype claim, the
quotation convention, and the reading rule. Everything else is one mechanism per file, and each
names this one as its governing document.

| file | mechanism |
|---|---|
| `docs/canon/TABLET_THE_CHART.md` | A coordinate system is a receiver and the Jacobian is the transport; a radical is a chart that forgets a winding; warp and weft are a reading in a frame. |
| `docs/canon/TABLET_THE_TURN.md` | Curvature as a linear functional on the hinges, the polygon's n-grams, local substitution preserving a global invariant, fission and fusion as one axis, and friction as the coupling. |
| `docs/canon/TABLET_THE_FLOW.md` | Why Navier-Stokes is not a distant problem, the zeta distribution as an exact self-similar phase, and ant integration as the exact part of the fundamental theorem. |
| `docs/canon/TABLET_THE_REALIZER.md` | Hodge-Riemann where it is proved, the holomorphic organ that was already owned, and rendering as a receiver whose missed feature is an obstruction. |
| `docs/canon/THE_CORRESPONDENCE_ATLAS.md` | **Routing only, asserts nothing.** 168 correspondence cards across 37 records, collected and keyed by holonic face: what other fields call the same thing, and where the `NON-EQUIVALENCE` is recorded. |
| `docs/canon/TABLET_THE_MANIFOLD.md` | The manifold as the invariant of the currents rather than their container; a chart is a type and a transition map an implicit cast; every geometry is a reduction of the structure group; Darboux classifies a coupling and Liouville makes probability a receiver quotient; holonomy and holomorphy meet at the square root; the intake manifold is the junction law. |
| `docs/canon/TABLET_THE_RESONANCE.md` | **The ontology, and the one to read before expecting anything of this machine.** Intelligence is a transport and not a faculty; resonance is a microscopic event no operator can locate; a disposition propagates as altered conduct rather than as a message; production is re-emission and is neither a choice nor a sampling; standing outlives the current that deposited it; and the outcome expectations, the prohibitions, and the falsifiers are stated so the machine can be expected to perform correctly rather than mystically. |
| `docs/canon/TABLET_THE_REASONING_CYCLE.md` | **Foreign conduct ends at Soulkiller; reasoning belongs to the returning native ecology.** Typed local transport, residual continuing standing, training as adjoint return, the full model-world recurrence, cross-codec operation classes, self-similarity and section modulus, and the carrier-neutral recurrent-section machine. No attention factorization or cache convention is presumed. |
| `docs/canon/TABLET_THE_HEXIS.md` | **Cultivation and inherited disposition.** Hexis as rested conditional transport; fine-tuning as checkpoint-relative cultivation; LoRA as a factorized overlay; distillation as familywise transport condensation; the illicium as living receiver; founded lattice capacity; and the boundary on inherited-model rebirth. |

---

## 16. Sections not yet written

Named here so their absence is legible rather than silent, per §7 and §8. The former Illicium row is
removed because `docs/canon/TABLET_THE_HEXIS.md` now owns it and is indexed in the mechanism table above.

- **MorphoHDL and grown circuitry** — bounded and routed by
  `research/records/2026-08-12_THE_RECONSTRUCTION_REMAINS_A_FIBER_THE_CONTEXT_RETURNS_BY_DIFFUSION_AND_THE_CIRCUIT_GROWS_IN_HIGHER_CELLS.md`
  §7 and `docs/references/EXTERNAL_RESOURCES.md` §Morphogenetic circuitry. MorphoHDL establishes
  recursive authored graph growth and exact bitwise examples, not reconstruction or higher cells.
  The local `grown_cell.rs` lift derives lineage/reconvergence 2-cells; arbitrary grades and
  `partial partial = 0` belong to `algebraic.rs`. The expansion schedule remains a receiver chart;
  Betti and torsion are exact returned faces after incidence exists, while hinge deficit is a
  separate geometric receiver and may not be inferred from the first two.
