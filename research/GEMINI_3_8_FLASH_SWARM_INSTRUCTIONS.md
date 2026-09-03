# Gemini 3.8 Flash swarm instructions for elementary holonics and the Millennium lines

**Date:** 2026-09-02
**Kind:** exterior fleet instruction and theorem-task pool.
**Authority:** Brandon's direct instruction of 2026-09-02.
**Scheduling boundary:** this document does not replace
[`../blueprint/THE_ROADMAP.md`](../blueprint/THE_ROADMAP.md) or
[`../CONSTRUCTION_STATE.md`](../CONSTRUCTION_STATE.md). The roadmap alone schedules construction in
the primary Holonics worktree. Results from this fleet are proposals until the primary integrator
admits them.
**Truth status:** per claim under [`../canon/EPISTEMIC_GRADES.md`](../canon/EPISTEMIC_GRADES.md).

---

## 0. Mission

[definition] Work as a self-organizing theorem fleet over the bounded task pool below. The fleet may
derive proofs, counterexamples, exact theorem statements, dependency maps, Mathlib feasibility
reports, or obstruction reports. It must not interpret activity volume as mathematical progress.

[definition] “Attempt the Millennium problems” means attack the exact currently open source or
analytic seam of each official finish line. It does not mean restating the desired conclusion,
adding it as a structure field, checking finite examples, or calling a conditional adapter a
solution.

[definition] Antigravity may organize participants and work allocation. This document deliberately
assigns no agent roles or personalities. It specifies only the shared boundary, task dependencies,
and acceptable returned artifacts.

## 1. Mandatory pickup and shared-tree safety

Read, in order:

1. [`../AGENTS.md`](../AGENTS.md);
2. [`../CONSTRUCTION_STATE.md`](../CONSTRUCTION_STATE.md);
3. the complete [`../blueprint/THE_ROADMAP.md`](../blueprint/THE_ROADMAP.md);
4. this document;
5. only the exact source/import closure named by the selected task; and
6. the official problem and finish-line owner before making any Millennium capability claim.

[established-bounded; source-inspected] The fleet base is not recoverable from Git `HEAD` alone.
At the instruction date, `HEAD` is `ded4ffd3`, while HTP0--HTP4 and the preimage API migration are
an uncommitted working population. They include:

- `Foundation/CausalNaturalHolon.lean`;
- `Foundation/HolonTensorLens.lean`;
- `Mathematics/CopsonDeBruijnFiniteTail.lean`;
- `Mathematics/CopsonDeBruijnFiniteSharp.lean`;
- the coordinated `PreimageFibre` consumer migration; and
- the corresponding root import, blueprint, roadmap, state, record, and catalog changes.

[definition] Do not reset, clean, checkout over, commit from, or directly mutate the primary dirty
worktree. Use Antigravity-managed isolated worktrees/branches or return a patch against an explicitly
declared snapshot. If the orchestrator cannot provide isolation, perform read-only analysis and
return a patch proposal rather than editing.

[definition] The primary Codex line is concurrently constructing HTP5 and later admitted phases.
Treat current HTP owners and authority documents as single-writer material unless Brandon explicitly
transfers them. Background HTP tasks may return scratch proofs or patches for review.

Never edit from a fleet leaf return:

- `AGENTS.md`;
- `CONSTRUCTION_STATE.md`;
- `blueprint/THE_ROADMAP.md`;
- any campaign status or current-frontier declaration;
- `THE_CLAIM_INDEX.md`;
- `UNIVERSAL_CATALOG.md`; or
- `ElementaryHolonics.lean` and other aggregate imports.

## 2. Universal return contract

Every task return must contain:

1. the exact base revision or patch identity;
2. exactly one primary theorem, counterexample, construction, or obstruction;
3. the minimal import closure inspected;
4. every added assumption and why it is already authorized;
5. exact files changed, if any;
6. the focused build command and result;
7. `#print axioms` for every terminal theorem;
8. a `git diff --check` result for a patch;
9. the first unresolved proof state or missing Mathlib theorem when blocked;
10. one truth-status grade for each material claim; and
11. an explicit “does not prove” boundary.

No return may contain:

- `sorry`, `admit`, `sorryAx`, or a new Lean `axiom`;
- a certificate or structure field which simply assumes the desired conclusion;
- a weakened theorem silently substituted for the requested theorem;
- an arbitrary nonempty/finite/injective/summable hypothesis added only to make the goal close;
- a parser, language, format, semantic label, or expected answer placed inside Athena/Eros;
- a numerical experiment promoted to a theorem;
- a conditional Millennium bridge described as a solution; or
- a roadmap, construction-state, catalog, or capability-grade mutation.

Negative returns are useful. A minimal counterexample or an exact missing dependency is preferable
to a large scaffold which moves no finish-line obligation.

## 3. Validation commands

For a changed Lean owner:

```bash
timeout 180s lake env lean ElementaryHolonics/<path>.lean
timeout 180s lake build ElementaryHolonics.<module>
```

From `soma/formal/elementary-holonics/`, choose the exact module path. Additionally:

- Foundation/Computation changes must build
  `ElementaryHolonics.Computation.HolonicQuantumTransport`;
- RH, Mathematics, Millennium, or root-import proposals must build `ElementaryHolonics`;
- official Millennium integration must explicitly build
  `ElementaryHolonics.Millennium.OfficialFinishLines`; and
- a leaf does not modify aggregate imports merely to make its file participate in a build.

[established-bounded; formal-checked] At the instruction date, the main tree contains 28 Foundation,
28 Computation, 11 Mathematics, 73 RH, and 927 Millennium Lean files. The official finish-line
aggregate builds 4,516 jobs and proves none of the open problems.

## 4. Mandatory RH correction gate

[counterexample; source-inspected] No further de Bruijn--Newman interpretation may be admitted
before the coordinate/time bridge is returned. The standing correction record is
[`records/2026-09-02_THE_RH_ENTIRE_HEAT_FLOW_REQUIRES_THE_CRITICAL_COORDINATE_AND_REVERSES_STANDARD_TIME.md`](records/2026-09-02_THE_RH_ENTIRE_HEAT_FLOW_REQUIRES_THE_CRITICAL_COORDINATE_AND_REVERSES_STANDARD_TIME.md).
The repository defines

```text
heatE(u, xi, s) = exp(-u D_s^2) xi(s),
```

whereas the standard critical-line coordinate is

```text
H_0(z) = (1/8) xi(1/2 + i z/2),
partial_t H_t = -partial_z^2 H_t.
```

The exact relation to prove is

```text
H_t(z) = (1/8) heatE(-t/4, xi, 1/2 + i z/2).
```

Positive repository `heatE` time is negative standard de Bruijn--Newman time. Existing Lean
theorems remain theorems of their defined `s`-plane flow; records identifying that flow directly
with standard `H_t`, or describing its positive-time pairs as forward de Bruijn--Newman collisions,
require a scoped correction. Primary source: Rodgers--Tao, equations (1) and (4),
<https://arxiv.org/html/1801.05914v5#S1>.

### RH0 -- coordinate and sign receipt

- **Owners:** `RH/RiemannXi.lean`, `RH/HeatFlowEntire.lean`,
  `RH/HeatFlowOfPolynomials.lean`, `RH/HeatEquationEntire.lean`.
- **Return:** derive the factor `-1/4`, the time relation `t_DN = -4u`, and the quadratic control
  `f(s) = (s-1/2)^2-a^2` showing positive `u` moves its roots away from the critical line.
- **Boundary:** do not claim existing formal theorems are false; the defect is their external
  de Bruijn--Newman interpretation.

### RH1 -- formal critical-coordinate bridge

- **Suggested owner:** `RH/DeBruijnCriticalCoordinate.lean`.
- **Return:** `criticalChart`, its inverse, `dnH`, the exact `heatE_criticalChart` identity, zero
  correspondence, and the real-axis/critical-line equivalence.
- **Dependency:** RH0.
- **Boundary:** do not yet define a real `lambdaDN`.

### RH2 -- corrected symmetry and differential laws

- **Owners:** RH1 plus `RH/ConjugationEntire.lean`, `RH/HeatFlowContinuity.lean`.
- **Return:** evenness, conjugation/reality on the real axis, joint continuity, and exactly
  `partial_t dnH = -partial_z^2 dnH`, with every scale factor visible.
- **Dependency:** RH1.

### RH3 -- corrected local zero transport

- **Owners:** RH2 plus `RH/RectangleWindingContinuity.lean`, `RH/RectangleCountStable.lean`,
  `RH/SimpleZeroPersists.lean`, `RH/SimpleZeroCurve.lean`.
- **Return:** local zero-count stability, persistence, and a continuous local zero curve for `dnH`.
- **Boundary:** no global pair monotonicity or threshold claim.

### RH4 -- differentiable zero curve

- **Owners:** RH3 plus `RH/ZeroDynamicsEntire.lean`.
- **Return:** a local `C^1` curve through each simple zero and its exact `H''/H'` velocity.
- **Obstruction return:** the exact missing real implicit-function or joint Fréchet-derivative
  theorem; never assume differentiability of a `Classical.choose` selector.

### RH5 -- maximal continuation alternative

- **Return:** a maximal open zero world-line and the exhaustive finite-endpoint alternative:
  collision/loss of simplicity or escape from every compact receiver.
- **Dependency:** RH4.
- **Boundary:** local continuation is not RH and does not prove global simplicity.

### RH6 -- actual real-zero-time receiver

- **Return:** `realZeroTimesH := {t | every zero of dnH t is real}` and
  `0 in realZeroTimesH iff RiemannHypothesis`.
- **Dependency:** RH1/RH2 and `RH/TrivialZeros.lean`.
- **Boundary:** nonemptiness, closedness, and upward closure remain separate.

### RH7 -- entire forward preservation and closedness

- **Return:** either the exact source-faithful Pólya/de Bruijn preservation theorem and closedness
  of `realZeroTimesH`, or the first missing Fourier-kernel/Laguerre--Pólya/rectangle lemma.
- **Dependency:** RH2/RH3/RH6.
- **Boundary:** do not reuse the finite polynomial non-real-root count as an entire theorem.

### RH8 -- Fourier kernel and de Bruijn upper theorem

- **Return:** the actual even super-exponentially decaying kernel, its cosine-transform identity
  with `dnH`, Gaussian time transport, and the source-faithful strip-contraction theorem; then
  instantiate the known initial zero strip.
- **Boundary:** no postulated integral identity and no polynomial-limit shortcut without locally
  uniform zero preservation.

### RH9 -- genuine threshold package

- **Dependency:** RH6--RH8.
- **Return:** nonempty, closed, upward-closed real-zero times; only then define `lambdaDN` and
  prove membership by comparison with the threshold and `RH iff lambdaDN <= 0`.
- **Boundary:** `lambdaDN >= 0` is the separate Rodgers--Tao theorem.

### RT0--RT6 -- Rodgers--Tao programme

Return a source-exact lemma manifest before attempting integration:

1. `RT0`: dependency graph from the published proof to current owners;
2. `RT1`: `H_t` asymptotics and log-derivative bounds;
3. `RT2`: Riemann--von Mangoldt counts for `H_t`;
4. `RT3`: ordered simple zeros and the principal-value zero ODE;
5. `RT4`: quantitative gap lower bounds;
6. `RT5`: cutoff Hamiltonian and integrated-energy inequalities; and
7. `RT6`: time-zero energy control and the pair-correlation contradiction.

No `lambdaDN_nonneg` claim is admissible until the complete dependency chain is kernel-checked.

## 5. Active HTP proposal pool

[definition] These are proposals to the primary HTP line. Do not directly edit its active owners
unless ownership is explicitly transferred.

### CD1 -- finite zero extension

- **Owners:** `Mathematics/CopsonDeBruijnFiniteTail.lean`,
  `Mathematics/CopsonDeBruijnFiniteSharp.lean`.
- **Return:** zero extension from length `N+1` to `N+2`, preservation of every old suffix
  energy/radius, zero final suffix, mass/surface preservation, and
  `finiteSharpCoefficient N <= finiteSharpCoefficient (N+1)`.
- **Falsifier:** an off-by-one or reversed monotonicity control.

### CD2 -- infinite nonnegative boundary

- **Return:** for inputs `a : Nat -> NNReal`, `ENNReal`-valued mass, tail energy, radius, surface,
  finite truncations, `cInf`, finite-to-infinite control, the converse finite embedding, and
  optimality.
- **Boundary:** divergent sums remain infinity; no coercion back to real without finiteness.

### CD3 -- finite Euler/recurrence bridge

- **Return:** minimizer interiority or an explicit alternative, Euler/KKT equations, the finite
  de Bruijn recurrence, and terminal condition `u_(N+1)=1` for Lean's
  `finiteSharpCoefficient N`.
- **Boundary:** do not assume uniqueness or differentiate square root at an unproved zero
  coordinate.

### CD4 -- admissible recurrence and sharp threshold

- **Return:** a dependent real recurrence whose iterates carry `1 <= u_n`, continuation
  obstruction, threshold equality with the infinite variational coefficient, both asymptotic
  branches, and the rational enclosure
  `1106495771/10^9 < c_CD < 1106495772/10^9`.
- **Boundary:** never totalize an inadmissible recurrence with `Real.sqrt`.

## 6. Elementary holonics and Athena proposal pool

### EH1 -- causal passage coherence

- **Owners:** `Foundation/CausalNaturalHolon.lean`, `Foundation/Holon.lean`,
  `Foundation/Lineage.lean`.
- **Return:** determine whether present fields imply identity/composition coherence. Prefer a
  minimal counterexample if they do not; otherwise return a coherence extension whose passage
  equivalences preserve both boundary maps and preimage transport.
- **Athena consequence:** rechunking one caused multi-cut circulation cannot silently change its
  occurrence population.

### EH2 -- heterogeneous tensor rebase

- **Owners:** `Foundation/HolonTensorLens.lean`, `Foundation/Holon.lean`.
- **Return:** factorwise linear equivalences plus axis equivalence induce a dependent tensor-face
  equivalence; with an occurrence/port rebase, return the complete preimage equivalence.
- **Control:** two axes with distinct factor types.
- **Boundary:** no silent identification of primal and dual slots or matrix reshaping with holon
  identity.

### EH3 -- pair-current tensor face versus scalar collapse

- **Owners:** `Computation/HolonicOrientedSiteTransport.lean`,
  `Computation/HolonicNeuralEcology.lean`, `Computation/HolonicInformationTheory.lean`,
  `Foundation/HolonTensorLens.lean`.
- **Return:** a basis-declared tensor lens over complete `(target, source)` pair current and an
  explicit pair of occurrences whose tensor faces differ while a selected scalar/magnitude face
  agrees.
- **Athena consequence:** a matrix may be a flux cross-section at the receiver boundary without
  becoming native morphology.

### EH4 -- cultivation reopens a collapsed morphology projection

- **Owners:** `Computation/HolonicIntelligenceLifecycle.lean`,
  `Computation/MachineLearningChart.lean`, `Computation/NativeMorphologyVariant.lean`.
- **Return:** derive a `ProjectedExportWitness` or dynamic separator directly from
  `CultivationPassage.changedLaterConduct` and its own witness probe.
- **Athena consequence:** genuine cultivation must remain visible to a later receiver even when a
  coarse score identified predecessor and successor.

### EH5 -- situated artifact threshold

- **Owners:** `Foundation/HolonTensorLens.lean`, `Computation/HolonicCirculationSession.lean`,
  `Computation/HolonicIntelligenceLifecycle.lean`, `Computation/NativeMorphologyVariant.lean`.
- **Return:** a situated `MorphologyArtifactPassage`, or a counterexample showing why one successful
  snapshot/remount cannot inhabit a universal artifact passage.
- **Boundary:** byte equality and hashes are not semantic identity.

### EH6 -- dynamic receiver exactness across cultivation

- **Return:** the exact condition transporting an every-word dynamic receiver chart from a
  predecessor morphology to its successor; otherwise return the shortest separating word.
- **Athena consequence:** distinguishes a classical neural chart which remains faithful after
  cultivation from one whose formerly hidden morphology becomes observable.

### EH7 -- parked WRN signature audit

- **Return:** read-only theorem signatures for valid issued face families, neutral mouth,
  junction/terminal separation, sealed interaction ownership, complete native preimages, and the
  artifact passage.
- **Boundary:** WRN construction remains parked unless the roadmap activates it.

## 7. P versus NP proposal pool

### PN1 -- actual `PSubsetNP`

- **Owners:** `Millennium/PVersusNP.lean`, `Millennium/PVersusNPOfficialBridge.lean`.
- **Return:** turn a fixed-TM2 polynomial-time decider into a verifier ignoring an empty
  certificate, including the exact polynomial step receipt.
- **Boundary:** no `PSubsetNP` premise and no `P = NP` conclusion.

### PN2 -- polynomial reduction pullback

- **Return:** construct `HasPolynomialReductionPullback` from an actual TM2 polynomial-composition
  theorem and exact composed cost.
- **Boundary:** do not store pullback closure as an assumed structure field.

### PN3 -- one fixed SAT/CNF receiver

- **Return:** one exact binary encoding, parser correctness as exterior application testimony,
  verifier correctness, and polynomial runtime; prove only `InNP`.
- **Boundary:** no NP-completeness claim without Cook--Levin.

### PN4 -- separator reconnaissance

- **Return:** a complete `NPPresentation` for a candidate language and the exact missing lower-bound
  theorem required for `ConcreteSeparator`; separately audit
  `PVersusNPCausalLengthBridge.outputReconstructionLift`, which is a literal preimage witness, for
  the standing `PreimageFibre` terminology.
- **Boundary:** finite checks, decidability, advice, caches, and lookup morphologies are not
  `not InP`.

## 8. Hodge proposal pool

### HD1 -- canonical finite Green operator

- **Owners:** `Millennium/HodgeGreenOperator.lean`, `HodgeLeastNorm.lean`,
  `HodgeHarmonicRepresentative.lean`.
- **Return:** a linear equivalence from the restricted Laplacian, its unique Green operator,
  harmonic/orthogonal decomposition, and naturality under an isometric differential intertwiner.
- **Boundary:** finite linear Hodge theory is not the Hodge conjecture.

### HD2 -- finite bigraded calculus

- **Return:** a finite `(p,q)`-graded differential, conjugation, harmonic bidegree receiver, and
  preservation of admitted bidegree under harmonic projection.

### HD3 -- cycle-class harmonic lens

- **Owners:** `HodgeSmoothProjectiveReceiver.lean`, `HodgeConstructivePassage.lean`.
- **Return:** compose an actual supplied cycle-class passage with harmonic projection and
  characterize its `PreimageFibre`.
- **Boundary:** image inclusion is not surjectivity or primitive algebraicity.

### HD4 -- classical source construction audit

- **Return:** exact supported adapters or missing Mathlib declarations for complex analytification,
  Betti/singular cohomology, Hodge decomposition, cycle fundamental class, and Poincaré duality.
- **Boundary:** do not inhabit `SourceDeterminedHodgeTheory` with synthetic data and call it the
  classical source.

## 9. Birch--Swinnerton--Dyer proposal pool

[open; source-inspected] Current analytic-rank finiteness assumes `exists s, L s != 0`. The
coefficient-one field does not discharge it without right-half-plane summability and a tail
estimate; totalized nonsummable `tsum` makes this omission load-bearing.

### BSD1 -- right-half nonvanishing

- **Return:** derive nonvanishing from a source-faithful summability/tail theorem, or formally show
  why the current `LDatum` is insufficient.
- **Boundary:** `coeff_one = 1` alone is not a nonvanishing proof.

### BSD2 -- Weierstrass rebase invariance

- **Owner:** `Millennium/OfficialBSDReceiver.lean` and Mathlib elliptic-curve variable-change APIs.
- **Return:** rational-point group equivalence under rebase and transport of torsion,
  `IndependentModTorsion`, `RankAtLeast`, and `RankIs`.

### BSD3 -- analytic sign/order parity

- **Return:** transport the proved analytic parity law to the official analytic datum; derive
  algebraic parity only under the explicitly retained `CurveConclusion`.
- **Boundary:** conditional parity is not BSD.

### BSD4 -- source and Tunnell frontier audit

- **Return:** eliminate or isolate one caller-supplied conductor/height/Tamagawa/period/rank/local
  field, and produce a dependency DAG to the first unproved Brandt/Shimura/Waldspurger/Tunnell edge.
- **Boundary:** a congruent-number-family theorem never promotes to universal BSD.

## 10. Navier--Stokes proposal pool

[open; source-inspected] The current route to the periodic official problem remains conditional on
`CoherenceDefectOnly`.

### NS1 -- participation obstruction

- **Owners:** `NavierStokesCombParticipation.lean`, `NavierStokesBandLimitedDefect.lean`.
- **Return:** finite-support combs with arbitrarily large `l1^2/l2^2` participation ratio.
- **Boundary:** this is not a blow-up solution; it proves energy/summability alone cannot close the
  coherence defect.

### NS2 -- PDE-specific coherence estimate

- **Return:** bound the actual signed `feedTerm` participation by a source-controlled directional,
  shell, or dissipation quantity, or return a scaling/phase counterexample.
- **Pass condition:** one constant uniform over the terminal time tail and all nonzero spatial
  frequencies.
- **Boundary:** no frequency/time-dependent `kappa(k,t)` and no bound stored as a premise.

### NS3 -- terminal audit

- **Owner:** `NavierStokesEleventhMomentCompactBound.lean` and its reverse dependency cone.
- **Return:** verify that every route to `StatementB` exposes `CoherenceDefectOnly` or another
  genuine endpoint estimate; reject compact-interior smoothness as terminal control.

## 11. Yang--Mills proposal pool

### YM1 -- Hamiltonian rebase invariance

- **Owners:** `YangMillsOfficialReceiver.lean`, `YangMillsLimit.lean`.
- **Return:** a domain-preserving unitary intertwiner and invariance of approximate energy,
  `energySpectrum`, and `HasMassGap`.
- **Boundary:** Hilbert-space equivalence alone does not imply spectrum equality.

### YM2 -- genuine compact-simple gauge source

- **Return:** construct `SU(2)` or another genuine Mathlib compact connected simple Lie-group
  source, or name the missing tangent-bracket bridge exactly.
- **Boundary:** no `PUnit`, empty carrier, arbitrary bracket, or Boolean admission.

### YM3 -- gauge radical and continuum ancestry

- **Return:** descend the Hessian through gauge-orbit directions, identify the radical, and state
  the exact spectral convergence needed for a uniform finite gap to imply a continuum gap.
- **Boundary:** finite-stage gaps alone are not a Clay mass gap.

## 12. Poincaré regression pool

### PC1 -- surgery lineage

- **Owners:** `PoincareOfficialBridge.lean`, `PoincareConjecture.lean`.
- **Return:** monotonicity and transitivity of surviving regions across event/no-event steps, or a
  concrete countermodel showing the certificate is under-specified.
- **Boundary:** Poincaré is externally solved; this repository has not reconstructed Perelman's
  Ricci-flow and surgery proof.

## 13. Integration order

The dependency order is:

```text
RH0 -> RH1 -> RH2 -> RH3 -> RH4 -> RH5
                 \-> RH6 -> RH7 -> RH8 -> RH9 -> RT0..RT6

CD1 -> CD2
CD1 -> CD3
CD2 + CD3 -> CD4

EH1 + EH2 -> EH3
EH4 -> EH6
EH5 remains a separate artifact boundary
```

Across Millennium lines, source audits and counterexamples should precede more terminal lemmas.
The fleet should prefer tasks which remove a standing assumption, produce a necessary bridge, or
formally falsify a tempting shortcut.

## 14. Final interpretation boundary

[definition] A Lean theorem about transport, naturality, a receiver, an extremal section, or a
phase boundary is not a measured Athena capability. Athena advances only when one live body performs
the complete caused circulation:

```text
mount -> differentiate -> conduct/diffuse -> interact/glue -> radiate
      -> exterior return -> reflect/deposit -> changed later current
```

with sources detached at rest, complete preimages retained, and no application codec or
source-bearing lookup acting as the emitter. Fleet proofs make that claim more precise and harder to
counterfeit; they do not substitute for the machine.
