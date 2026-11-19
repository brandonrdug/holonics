# The atlas rows graded formal-checked were read against their Lean statements: 243 of 2,501 claimed more, and each repaired row states its owners with the rest in scope

November 19, 2026, 00:48 UTC. Refs #410 and #147. The grade `formal-checked` says that a named proof kernel accepted the declared
formal statement ([the grades](../../docs/canon/EPISTEMIC_GRADES.md)). A row carries it rightly only when its owners' statements,
taken together, state its expr under its scope. This record reads that for every row so graded, repairs each row that claimed more,
and repairs the guides and Lean headers that still called tonight's proofs owed. It is a reading of the atlas against the Lean, not a
review of any proof: every owner below builds, and no proof is in question.

## 1. What a mechanical check reads

`tools/link_check.py atlas` resolved an `L:` owner when its name appeared anywhere in the file, comments included. From this change it
resolves a name only when a line outside comments declares it (a declaration head, a constructor `| name` or a field `name :`), and
names the other cases: used but declared nowhere, in a comment only, absent (`lean_declared`; three planted cases in
`tools/test_link_check.py`, which the old reader passed). A `formal-checked` row with no `L:` owner is now a `BROKEN_GRADE` (a planted
row in the controls). At `cfa64e74` every owner resolved under the stricter reading, and six rows had no Lean owner:

- the five `hodge.cm-actual-*` rows, whose Lean stands only in the frozen source of a receipt
  (`receipts/2026-10-09-cm-overlap-gluing/v9/source-v9/`, 117 provider files) that no target of the package builds: regraded
  `proved-derived`, the grade the receipt's own acceptance supports;
- `compression.fold-tautology-not-standing`, whose module had not been ported at the reset: `Foundation/FoldStanding` ports it from
  `13f8c734` (`ElementaryHolonics/Transport/ContactAmplitudeState.lean`), the statements and proofs the same, read against the live
  `StandingLaw` and `transportWord`, and the row names its theorems.

## 2. The reading

An extractor (`decls.py`, in the receipts) read every declaration of the package from the text: its name, kind, line and statement
(the text from its name to `:=`). `join.py` joined each `formal-checked` row to its owners' statements, 2,501 rows in all, cut into 19
chunks. Nine readers read every row against its owners' statements, opening the definitions a statement depends on (`READ_BRIEF.md`),
and listed the rows whose expr claims more than the owners state.

| Class | Findings |
|---|---|
| the owners state less (an unlisted conjunct, a converse, a general law read from one instance, a bound with a dropped term) | 206 |
| a hypothesis the scope does not name, carrying the claim's content | 11 |
| a routine hypothesis the scope does not name | 9 |
| the owners state another quantity | 6 |
| undecided by the reader | 11 |
| **in all, on 243 rows** | **243** |

The readers were not given planted mismatches, so a row with no finding is one reader's reading and no certificate (rule 11); the
findings are receipts of a first reading and were each read again before any repair (§3).

## 3. The repair

Each finding was read again against the Lean (`FIX_BRIEF.md`) and decided in this order: no repair where the owners state the claim;
the sibling declaration that states the missing clause added as an owner, after reading its statement; otherwise the expr narrowed to
what the owners state, with every clause they do not state kept in scope as `not in Lean:` (a count by a run as `measured:` with its
record, a table by enumeration as `not in Lean, by enumeration:`); a hypothesis the scope lacks added to it. Nothing a row said is
dropped: it stands under the status it has. No grade was lowered by the repair beyond §1, because in every repaired row some owner
states the central claim. `apply.py` replaces whole fields by id, only where the field at the head equals the field the repair was
read from, and keeps every existing owner in order.

Applied in this change: **176 rows** (174 repaired, 2 needing none), 380 field lines, 93 rows gaining owners, 106 clauses moved under
`not in Lean`; with the five CM rows of §1 and the two repaired first (the gamma segment, the finite nonboundary
reduction), 183 of the 243. The 60 remaining findings, all on Navier–Stokes rows, follow in a
second change.

The findings that changed what a row reads, beyond its wording:

- **Hypotheses that carry the target's content, now in scope.** The BKM continuation is conditional on the logarithmic high-order
  law (`LifespanLogarithmicHighOrderLaw`, or the H³ comb or the uninhabited dyadic Hodge subset-mass return in its place) and on a
  restart supply; the cofinal work and adaptive matched bounds on the enstrophy strand receipt; the incoherent closure's
  `StatementB` on `CoherenceDefectControl`; the vorticity direction's growth law on the vorticity equation read along the direction
  field (assumed: `halign`, `hlap`, `hevol`); the Yang–Mills receiver's continuum gap on a `FiniteContinuumReconstruction` record
  whose fields carry the gap and which nothing here constructs; the finite nonboundary reduction on its `construct` hypothesis; the
  hazard ladder's adaptive bound on the pathwise rung bound `hrung`; the reflected pair's current on the partner being a simple zero.
- **A constant the row wrote apart from its owner.** The gamma segment reads `‖R‖ ≤ 402‖ζ‖³/‖w‖²` where the row wrote 37
  (`g_expansion`; the module's header now says 402); the cofinal and packing bounds gain their `½M_ω(a)²` term and the factor
  `1024/ν`, and square the sum where the row summed squares.
- **An identification the rows read and the Lean does not state.** The E₈ Gram form as a Mordell–Weil height, the rank-12 form as
  the Shioda height of the Mestre family, Tate's ledger at one (Kodaira types, `c_p`, `|Ш|`, `L(1)/Ω` cited): each row now states the
  Gram form or the arithmetic of its entries, and keeps the identification in scope.
- **A statement the row read as proved that its module names open.** The ζ(5) series identity (the module proves its convergence
  skeleton), Sturm's count (`TheReadingEqualsThePopulation`, named open), the hairy ball (Poincaré–Hopf is not formalized), the
  quartic form of the Yang–Mills energy along its direction (the proof's route, unstated).
- **A direction.** The theta row at one listed `≠ 0` where the row read `> 0`; `theCentralValueIsThePositiveThetaIntegral` states it
  and is added. Where an owner proves one direction of a row's `⇔`, the row states that direction and keeps the converse in scope.

Every changed row's owners resolve (`ATLAS_OWNERS … broken=0`), and `link_check` controls pass 10.

## 4. Text that tonight's proofs made stale

Forty-four boxes of #410 were ticked by #992 to #1006. Two readers searched the guides, the atlas and the Lean headers for text that
still called one of them owed, open, cited or "not in Lean", and opened the proving declaration before reporting (`stale/BRIEF.md`;
dated records under `research/records/2026-*` stay as their day wrote them). Sixteen sentences were repaired, each naming the module
that now states it: the moving metric's converse and the seam chart (RECEIVER_HOLARCHY), three distances (`Aeon/Clock/Lock`), the
Lorentz cover (`Geometry/Motion`), approximate recurrence and the many-cell contact flow (ELEMENTARY_OBJECTS), the real chart of a
`G`-self-adjoint rate (`Transport/HolonicInteraction`), necklace integrality (`Compression/Landmark`), many-cell diffusion
(`Physics/Thermal`), the held face's order (`Mathematics/CheapConvolution`), the Ihara Euler product (`Landmarks/IharaBass`), Kac for
an ergodic motion and four atlas scopes (the stable core's converse, a merge's fibres, a row's worth, the strands' readout). Where the
new Lean states less than the stale text's subject (the polar decomposition over an exact field, a torus of several clocks, the
rotating pump's subharmonic resonance), the text keeps that part.

`Landmarks/LandmarksAndModuli` named Lucas' congruence as a `Prop` "mathlib does not carry". Mathlib carries it
(`Choose.choose_modEq_choose_mod_mul_choose_div_nat`), and `lucasCongruence_holds` now reads it in `ZMod p` (atlas
`coupling.lucas-congruence`). The touched modules build in this container.

## Receipts

[`receipts/2026-11-19_atlas-lean-read/`](receipts/2026-11-19_atlas-lean-read/): the two briefs, the extractor and the join, the nine
findings files, the five applied fix files, `apply.py`, and the stale-text brief with its two findings files.
