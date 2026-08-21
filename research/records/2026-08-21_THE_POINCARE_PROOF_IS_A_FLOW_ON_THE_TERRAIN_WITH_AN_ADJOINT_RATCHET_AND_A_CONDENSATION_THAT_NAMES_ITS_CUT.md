# The Poincaré proof is a flow on the terrain, with an adjoint ratchet and a condensation that names its cut

**Date:** 2026-08-21
**Kind:** external-proof reading — the solved Millennium problem posed in pure holonics, at
Brandon's direction, as the paradigm the six open routes measure themselves against. **It
schedules nothing.** [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The Lean line does not couple to the engine, per Brandon's standing ruling; the only trees
written are `research/records/` and the regenerated claim index.
**Truth grades:** `proved-standard` for Perelman's results and every classical theorem named —
the proof is peer-verified and the Millennium award was conferred; `historical` for the
description of the proof's structure; `interpretation` for every holonic correspondence, each
marked; `open` for the revised-retention programme and every transfer target.
**Primary sources:** Perelman, arXiv `math.DG/0211159` (the entropy formula), `math.DG/0303109`
(Ricci flow with surgery), `math.DG/0307245` (finite extinction time); Hamilton 1982 for the flow;
the verified expositions of Kleiner–Lott, Morgan–Tian, and Cao–Zhu; Colding–Minicozzi for the
extinction alternative.

---

## 0. Provenance, and the correction that occasioned this

Brandon hypothesized that Perelman's diffusion and entropy were stochastic, which would have put
the proof on the other side of the determinism line from holonics. **The correction: the proof is
deterministic through and through.** Ricci flow `∂g/∂t = −2 Ric(g)` is a deterministic parabolic
equation — in harmonic coordinates a nonlinear heat equation for the metric itself — and
Perelman's "entropy" is a monotone functional along that deterministic flow, named by a
statistical-mechanics *analogy* he states explicitly and then never uses as machinery. The heat
kernel enters only in its analytic chart, as the fundamental solution of a deterministic
equation; its Brownian reading is one receiver face, unused. Brandon's response: pose the proof
in pure holonics, *"at the very least it would be insightful"* — and his standing hypothesis,
carried here as the open programme: a holonically revised Perelman, with the retention contract
tightened, might pivot toward the other problems.

## 1. The classical proof, in its own species

`historical`, compressed to the six mechanisms the reposition needs:

1. **The flow.** Hamilton's Ricci flow evolves the metric by its own curvature. Singularities
   form in finite time whenever the topology is nontrivial; the whole difficulty is what happens
   at them.
2. **The two monotone functionals.** Perelman's W-functional is monotone non-decreasing along the
   coupled system — the metric flowing forward, a scalar potential `f` flowing **backward** by
   the *conjugate* heat equation, the formal adjoint of the heat operator on the evolving
   manifold. The reduced volume, built from a distance functional on spacetime paths
   (L-geodesics), is a second monotone quantity.
3. **No local collapsing.** The entropy bound forces a lower bound on the volume of balls at the
   curvature scale — the flow cannot flatten extent below its own scale — which kills the cigar
   soliton as a blowup model.
4. **Canonical neighborhoods.** Every region of sufficiently high curvature is, after rescaling,
   ε-close to one of a **short list** of models: the shrinking round sphere, the round neck
   `S² × ℝ`, or a cap. A finite table of near-singular shapes, proved, not assumed.
5. **Surgery.** The flow is stopped just before a singularity; the manifold is **cut along
   recognized necks**, the pieces capped, the topological bookkeeping retained — the pre-surgery
   manifold is recovered as a connected sum of the post-surgery pieces with known summands — and
   the flow restarts. Surgery times do not accumulate.
6. **Termination.** For a simply connected manifold the flow with surgery becomes extinct in
   finite time (Perelman's third paper; alternatively Colding–Minicozzi's shrinking width), and
   the bookkeeping forces the original manifold to be the three-sphere. The full geometrization —
   long-time thick–thin decomposition into hyperbolic and graph pieces — was more work of the
   same kind.

## 2. The reposition, mechanism by mechanism

`interpretation` throughout; each row names the holonic law it instantiates.

| Perelman's mechanism | the holonic species |
|---|---|
| the metric flows by its own curvature | **the terrain diffuses** — the map is the changing morphology; the flow's material is the medium itself, morphology as both current and channel, which is the circulating-cartographer doctrine as a PDE |
| `f` backward along the conjugate (adjoint) heat equation, `W` monotone | **the adjoint ratchet** — a covector transported backward through retained forward lineage, whose receiver face can only improve: the causal adjoint return with a monotone reading. Training's return, in Riemannian dress |
| no local collapsing | **an anti-tolerance law** — extent may not slip below the receiver's grain; the flow is forbidden from hiding geometry beneath the volume receiver's aperture. The cigar is exactly the phase-object failure it excludes |
| L-geodesics and reduced volume | **the navigation face** — a distance founded on the flow's own path space; shortest L-paths are leaders, and the monotone reduced volume is the terrain-founding stroke made quantitative |
| canonical neighborhoods | **the finite strata are tables** — the method atlas's law: near the singular locus the group stratifies and the strata are enumerable; away from it, no table, and none is needed |
| surgery with topological bookkeeping | **condensation that names its cut** — a compression with certified remainder: the removed pieces are classified, the connected-sum ledger is the `ReconstructionFiber`, and nothing is smoothed away unexhibited |
| finite-time extinction | **the return closes** — the termination condition: for the trivial class the circulation runs dry, and that closure *is* the theorem |
| geometrization | **the landmark table at the top** — the flow condenses an arbitrary three-manifold onto the eight geometries: the stratification theorem for the whole terrain |

Two joins to material already in this repository, both exact in kind:

- **Perelman's entropy family and the heat-Fisher chain admitted for M0 are one family.** The
  heat-kernel record's chain — heat probability map → Fisher pullback → directional trace defect
  → Nash entropy → volume growth — is the contemporary form of the same mechanism (Perelman's W
  is a Nash-entropy relative, and no-local-collapsing is a volume-growth consequence of an
  entropy bound). The M0 fixture material is not adjacent to the solved Millennium problem; it is
  its mechanism family.
- **The kernels are built by reflection.** The boundary/comparison kernels of the heat chart are
  constructed by the method of images — the conjugated half-turn constructing the kernel — and
  Perelman's Harnack-type inequality is a two-frame comparison: the invariant made visible across
  two frames, which is this project's own audit law.

## 3. What the classical proof deletes, and where

`interpretation`, and this is the load-bearing observation for the revision. The proof has
**two retention regimes**:

- **At surgery it retains everything that matters**: the cut is at recognized shapes, the removed
  pieces are typed, and the topological ledger is exact. This is the certified-remainder rule met
  by hand, and it is the part Hamilton's program lacked for two decades.
- **In the smoothing itself it retains nothing**: parabolic flow quotients high-frequency
  geometry below the receiver's grain with no fiber kept — backward heat is ill-posed precisely
  because the remainder was never exhibited. The classical statement survives because the two
  monotone receivers ratchet on the quotient face, so the *deletion is load-bearing but
  unexhibited*.

**The revised retention programme, `open`:** at finite grain, exact diffusion is invertible with
testimony — the exact rational boundary elimination in this repository retains both inverse
residuals — so a holonically revised flow would carry, at each scale, what the smoothing
quotiented, turning "the flow forgets" into "the flow deposits." The revision owes a scaling
family (the same bar the mass-gap line carries): the exact-finite discipline must be carried
through the continuum limit, and that is precisely the missing half of the one organ — a compact
representative with a certified remainder — appearing a third time, now under the solved problem.

## 4. The transferable schema, and its six targets

`interpretation` for the schema; `open` for every target; nothing here grades a deed.

The proof's shape, abstracted with nothing invented:

```text
(i)   a flow on the morphology itself
(ii)  an adjoint-transported covector whose receiver face ratchets
(iii) an anti-collapse bound: extent may not hide below the receiver's grain
(iv)  a finite table of near-singular shapes
(v)   condensation that names its cut
(vi)  closure for the distinguished class
```

- **Navier–Stokes** is the nearest target and the sharpest fit: regularity needs exactly (iii)
  and (iv) at the critical grain — a no-collapse receiver and a blowup-profile table — and the
  supercritical energy is the proof that the *magnitude* receiver cannot supply (iii). The
  schema says: build the receiver whose ratchet gives no-collapse, and the standing candidate
  from the strategy review is phase-population-shaped (the crossing population, not the net),
  since Tao's averaged equation shows the energy family blind.
- **RH, through the Deninger shape**: a deterministic flow whose closed orbits are the primes and
  whose Lefschetz-type reading is the explicit formula — the schema with (i) on an arithmetic
  space nobody has built, (ii) as the explicit-formula pairing, and (vi) as the placement. The
  missing item is the space, which is the archimedean realizer again: the Riemann route's own
  terminus reached from the opposite side.
- **Yang–Mills**: the Yang–Mills flow with monotone quantities is the constructive route's (i)
  and (ii); the gap is (vi), closure bounded away from zero; the lattice transfer-matrix line
  supplies the finite-grain instances.
- **Hodge**: (v) is the whole question — condense a far realizer population with a certified
  remainder; the cokernel is what the failed condensation deposits.
- **BSD**: descent is (i)–(ii) run on the arithmetic of the curve (Fermat's infinite descent is
  the FOUND stroke with well-founded terrain as (vi)), and Ш is the obstruction the ledger of
  (v) must carry.
- **P versus NP**: the orbit-closure programme is (i) as degeneration, and the barrier theorems
  are the measured statement that every magnitude receiver fails (ii); the schema locates the
  open work at a phase-carrying receiver, consistent with the strategy review's reading of the
  occurrence-to-multiplicity retreat.

## 5. What is owed, with falsifiers

**None is scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| ~~a finite exact instance of the schema end-to-end~~ — **ENACTED 2026-08-21, same day, in Lean**: `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/Ricci.lean`, 13 theorems, zero `sorry`, all audited by `#print axioms`. See the enactment section below. What remains of this row is the **surgery clause**: a terrain that can pinch — two cycles joined at a neck, cut at the declared scale with the ledger retained — since a triangle has no neck to cut. | a neck-cut whose ledger provably cannot reconstruct the pre-surgery terrain |
| the entropy join formalized at the finite grain: the M0 heat-Fisher chain's trace defect computed on an exact finite complex beside its retained fiber | a finite complex where the defect's monotone reading and the retained fiber disagree about what departed |
| the Navier–Stokes transfer stated as a receiver demand: what (iii) requires of a phase-population receiver at the critical grain, written against Tao's averaged control | an averaged-type equation that also defeats the stated phase-population receiver family |

## 5b. The enactment in Lean — deposited the same day

Brandon's direction was an adaptation *in Lean*, not a prose reading; this section records the
deed. Owner: `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/Ricci.lean` — **13
theorems, zero `sorry`**, all audited by `#print axioms` with only the ordinary foundations; the
library builds at 3,335 jobs; `Millennium/` measures **29 files, 6,333 lines, 331 theorems**
after the merge. **Measured 2026-08-21**: `grep -rli "ricci" Mathlib --include='*.lean'` → **0
files** — Ricci flow has no formal presence in mathlib at any grain, so this is the line's first
formal contact.

The terrain is the combinatorial circle with rational edge lengths — the triangle as the quantum
object — and the flow moves each length toward its neighbours: the metric diffusing by its own
second difference. Every schema clause is a kernel-checked theorem, and the exact grain returns
**identities where the classical proof has estimates**:

- `theFlowConservesTheTotal` — the chain law with zero source, normalization built in;
- `theDeviationContractsAtTheWindingRate` — the deviation contracts at **exactly `1 − 3τ`**,
  which is the winding eigenvalue `1 − 2τ + τ·2cos(2π/3)`: the ratchet's rate is a row of the
  winding table;
- `theReadingObeysItsExactRate` (`W' = (1−3τ)²·W`) and `theRatchetHoldsOnItsAperture` — the
  monotone receiver, with its aperture `0 ≤ τ ≤ 2/3` declared;
- `theExtentDoesNotCollapse` — the minimum is non-decreasing and the maximum non-increasing:
  no-local-collapsing as two exact comparisons;
- `theOnlyFixedShapeIsRound` — the κ-solution table at this grain has one row, proved;
- `theRoundClassIsClosed` — extinction: the distinguished class held, its reading zero;
- **`theFlowIsInvertibleWithTestimony`** — away from one aperture value the backward flow is
  exact and exhibited: *backward heat, well-posed at finite grain*, which is the revised
  retention contract as a theorem rather than a slogan;
- `theCondensationReconstructs` — round part plus deviation is the metric, exactly: the quotient
  carries its fiber;
- **`theCollapseApertureDeletes`** — at exactly `τ = 1/3` the flow collapses every triangle to
  round in one step, many-to-one by witness: **the classical unexhibited quotient, localized to a
  single aperture value**;
- `theRatchetFailsPastItsAperture` — at `τ = 1` the reading quadruples, witness computed: the
  monotonicity belongs to the aperture, not the structure;
- `theWindingsSeparateOnTheSquare` — on the four-cycle the half-turn component contracts at
  `1 − 4τ` and the quarter-turn components at `1 − 2τ`: **the flow's spectrum is the winding
  table**, and the fastest-dying mode is the finite shadow of the singularity model selecting
  itself.

The file states its own scope plainly: Poincaré is a three-manifold theorem and nothing here is
three-dimensional; what is enacted is the proof's mechanism under the retention contract. The
named continuations are the neck-pinch terrain with surgery-and-ledger, and the `n`-cycle
spectrum on the algebraic carriers `winding_inertia` already isolates.

## 6. Boundaries

Perelman's proof needs nothing from this record; its validity is settled and nothing here revises
it. The reposition table is `interpretation` and may not grade a deed; the revised-retention
programme and every transfer target are `open`; the schema is an abstraction of one proof, and
its fit to each open problem is a hypothesis to be paid for at that problem's own carriers. The
stochastic reading of heat kernels is a lawful chart that the proof does not use; nothing here
claims stochastic methods are unlawful elsewhere. No Lean was written for this record.
