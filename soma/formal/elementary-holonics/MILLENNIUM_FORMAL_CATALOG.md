# Millennium formal catalog

**Date:** 2026-08-24
**Scope:** exterior Lean theorem station under `ElementaryHolonics`; this document schedules no
Rust/CUDA construction and does not alter `CONSTRUCTION_STATE.md`.
**Catalog owner:** `soma/formal/elementary-holonics/MILLENNIUM_FORMAL_CATALOG.md`
**Complete import face:** `ElementaryHolonics.lean`

## 1. Purpose and provenance discipline

[definition] This is the surface-level catalog of the repository's Millennium mathematics.  It
records the strongest checked returns, their external mathematical substrate, the project's local
formulation or composition, their hypotheses, and the exact open fibre.  `THE_CLAIM_INDEX.md` is a
generated document router and is not a substitute for this mathematical progress catalog.

[definition] The provenance labels used below are:

- **external object/API** — a carrier or theorem imported from Mathlib or another named source;
- **local pose** — a project definition of the official problem boundary or an explicit hypothesis
  interface;
- **local derivation** — a theorem whose proof term is authored in this repository;
- **project-specific composition** — a local arrangement of standard and local objects which is
  source-identifiable in this repository, without claiming historical novelty;
- **open fibre** — the smallest named unreturned mathematical object or theorem presently exposed
  by the checked composition.

[open] Historical novelty has not been audited theorem by theorem.  Lean dependency inspection can
prove that a declaration and proof term are local and can name every imported dependency; it cannot
prove that no equivalent theorem or formulation exists in the mathematical literature.  Therefore
this catalog uses **project-specific formulation/composition**, never “new theorem to mathematics,”
unless a separate literature audit is deposited.

## 2. Measured station inventory

[established-bounded; measured] On the 2026-08-24 source closure after the measured-difference
composition, the station contains:

| Receiver | Returned count |
|---|---:|
| Lean modules below `ElementaryHolonics/` | 424 |
| theorem or lemma declarations | 5,459 |
| theorem, lemma, definition, abbreviation, structure, class, or inductive declarations | 7,751 |
| modules below `ElementaryHolonics/Millennium/` | 384 |
| theorem or lemma declarations below `Millennium/` | 5,102 |
| broad declarations below `Millennium/` | 7,175 |
| explicit `#print axioms` audit commands below `Millennium/` | 1,275 |

[established-bounded; measured] The principal module bands are 11 Foundation modules, 2 Algorithm
modules, 7 Geometry modules, 20 dedicated RH modules, and 384 Millennium modules.  Search prefixes
inside the Millennium band include 173 `NavierStokes*`, 30 `Family*`, 15 `General*`, 10 `Five*`, 6
`Hilbert*`, 2 `Hodge*`, and 13 `Holonic*` modules.  These prefixes overlap thematic work and are not
a partition of the library.

[definition] The reproducible inventory receiver is:

```bash
rg --files ElementaryHolonics -g '*.lean' | wc -l
rg -n '^\s*(theorem|lemma)\s+' ElementaryHolonics -g '*.lean' | wc -l
rg -n '^\s*(theorem|lemma|def|abbrev|structure|class|inductive)\s+' \
  ElementaryHolonics -g '*.lean' | wc -l
rg --files ElementaryHolonics/Millennium -g '*.lean' | wc -l
rg -n '^#print axioms' ElementaryHolonics/Millennium -g '*.lean' | wc -l
```

[definition] Counts establish the size of the source population only.  A declaration count is not
a theorem-strength metric, and an axiom-audit command is not itself proof that every declaration in
the library has the same dependency boundary.  The per-worktrack rows below name the mathematical
returns that matter.

## 3. Shared holonic theorem surface

| Grade | Owner | External substrate | Project-specific checked return | Exact boundary |
|---|---|---|---|---|
| `proved-derived; formal-checked` | `Foundation/Lineage.lean`, `AddressedBoundary.lean`, `ComparisonCell.lean` | additive algebra, pullbacks, quotients | addressed passages retain occurrence populations, boundary lineage, joined cancellation, and parallel-route defects | the full swing/connection/holonomy/receiver composition remains ordered by the active exterior blueprint |
| `proved-derived; formal-checked` | `Millennium/Swing.lean`, `SwingBridges.lean`, `HolonicDifferenceCalculus.lean` | additive groups, projective ratios, complex exponential | swing reverses an anchored difference; additive receivers commute with iterated differences; finite integration telescopes to the exterior boundary | individual instance bridges do not identify every physical transport with an affine swing |
| `proved-derived; formal-checked` | `Foundation/MeasuredDifferenceReceiver.lean` | normed additive groups and `Real.exp` from Mathlib | a receiver scalar factors through an addressed chart difference; even readings retain a two-orientation fibre; ratios ignore chart-zero shifts; binary normalized exponentials factor through one potential difference | injectivity and physical constitutive laws require their own hypotheses |
| `proved-derived; formal-checked` | `Millennium/HolonicParametron.lean`, `HolonicComplexParametron.lean`, `HolonicMeasuredParametron.lean` | exact real/complex algebra, finite sums, trigonometric identities | the two locked phase sheets, oriented incidence, diagonal and mutual storage, generalized coupled-LC modes, and measured `ΔQ/ΔV`, `ΔI/ΔΦ`, `ΔV/ΔI`, `Δθ/Δt` coefficient fields compose; coordinated branch reorientation preserves the mode | damping, passivity, Floquet theory, device calibration, and continuum realization remain outside these theorems |
| `proved-derived; formal-checked` | `HolonicTorusFlow.lean`, `HolonicTorusKnots.lean`, `HolonicUnknotting.lean` | Mathlib paths, tori, gcd/prime facts, racks and quandles | Fourier receiver passages, triad boundary closure, multiplier/interactor route defects, coprime torus-slope embeddings, rack swing cancellation, irreducible factor law, and finite phase-collapse counterexamples | no ambient three-manifold torus-knot owner, Reidemeister quotient, or complete unknot fibre exists yet |

[proved-derived; formal-checked] The new scalar correction is a composition law, not a slogan:
`DifferenceReceiver` stores the chart and the reading separately; `returnedDifference` precedes
`face`; `reconstructionFiber` retains every addressed pair returning one scalar.  The binary
exponential theorem proves

```text
exp(y) / (exp(x) + exp(y)) = exp(y-x) / (1 + exp(y-x)),
```

so the common potential is an exact null direction of that receiver.

## 4. Riemann hypothesis

| Grade | Layer | Principal owners and returns | Provenance | Open fibre |
|---|---|---|---|---|
| `definition` | official object | Mathlib's `riemannZeta`, `completedRiemannZeta`, and `RiemannHypothesis` | external object/API | the standard conjecture remains open |
| `proved-derived; formal-checked` | statement equivalence | `Millennium/Seam.lean`: the conjugate reflection is involutive; its fixed locus is `Re(s)=1/2`; `EveryModeSitsOnTheSelfConjugateSeam ↔ RiemannHypothesis` | local derivation over the external zeta object | equivalence does not establish mode placement |
| `proved-derived; formal-checked` | analytic infrastructure | the 20 `RH/*` modules: theta/Mellin charts, entire xi, functional and conjugation symmetry, gamma decay, growth, Jensen receivers, multiplicity-preserving zero counts, Weil-vector evaluations, and symmetry balance | project-specific composition of Mathlib complex analysis and number theory | horizontal placement is not controlled by zero counts or symmetry alone |
| `conditional; formal-checked` | explicit formula | `RH/ExplicitFormulaReceiver.lean`: weighted argument-principle and prime/archimedean residual ports compose to a truncated explicit formula | local typed pose and conditional derivation | actual argument-principle port, archimedean receiver, cofinal contours, and vanishing boundary return |
| `proved-derived; formal-checked` | measured difference | `MillenniumDifferenceAtlas.criticalSeamDifference_eq_zero_iff_mem` | project-specific composition | zero seam residual characterizes the target fibre but does not put zeros in it |

[open] The shortest RH return remains a genuine Weil/explicit-formula positivity carrier on an
admitted test-function family, including the archimedean term and the complete boundary remainder.
The exact formal obstruction is not “find another symmetry”; the two involutions and their balanced
fixed locus are already checked.

## 5. Birch--Swinnerton-Dyer

| Grade | Layer | Principal owners and returns | Provenance | Open fibre |
|---|---|---|---|---|
| `definition` | official pose | `BirchSwinnertonDyer.lean`, `UniversalBSD.lean`, `UniversalBSDLedger.lean`: point-count coefficients, analytic data, rank predicates, height/regulator data, rank and leading-coefficient clauses for the family and arbitrary integral models | local pose using Mathlib Weierstrass curves, `LSeries`, analytic order, Gamma, integration, and matrices | the universal conjecture is not inhabited by a universal proof |
| `proved-derived; formal-checked` | arithmetic family | `Family*`, `Five*`, and `General*`: torsion faces, descent cells, collision/halving laws, height contraction, finite generation on full-two-torsion curves, logarithmic family rank bounds, and prime-modulus rank bounds including `FamilyPrimeRank.theRankIsAtMostFourAtEveryPrimeModulus` | project-specific composition of standard elliptic-curve, finite-group, height, and lattice ingredients | these bounds do not identify analytic rank or the complete BSD ledger |
| `proved-derived; formal-checked` | analytic instance | `HeckeTheta.lean`, `HeckeEuler.lean`, `HeckeWitness.lean`: theta construction, entire completed function, Euler coefficients, complete `LDatum 1`, analytic rank zero, algebraic rank zero, and `theRankClauseHoldsAtOne` | local derivation built from Mathlib analysis/number theory and classical Gaussian/Hecke ingredients | the complete rank-zero leading coefficient at one still requires its ledger identity |
| `proved-derived; formal-checked` | universal instance | `MillenniumInstance.theMillenniumRankClauseIsProvedAtOne` and `theUniversalRankClauseIsSatisfiedSomewhere` | project-specific composition of the family witness with the universal pose | one satisfied curve is not the universal theorem |
| `proved-derived; formal-checked` | prime family analytic/arithmetic gate | `FamilyWaldspurgerGate.lean` and `FamilyThetaWaldspurgerBridge.lean`: canonical signed ternary populations, exact coefficient identities, and the scalar Waldspurger--Tunnell defect whose vanishing implies the positive-sign prime-family rank clause | local finite census plus analytic theta composition | vanishing of the displayed defect is the named unreturned port |
| `proved-derived; formal-checked` | measured differences | `MillenniumDifferenceAtlas`: finite rank equality is zero integer difference after finiteness; the rank-zero ledger is zero complex central-value difference | project-specific composition | the rank carrier remains `ℕ∞` until finiteness is supplied, and the ledger zero is still a theorem obligation |

[open] The sharp BSD pressure is two-pronged: close the displayed Waldspurger--Tunnell defect on
the remaining prime family, and construct the universal arithmetic/analytic passages needed beyond
the congruent-number family.  The catalog deliberately keeps the extensive algebraic descent,
the complete witness at one, and the universal conjecture separate so none is forgotten or promoted
into the others.

## 6. Hodge conjecture

| Grade | Layer | Principal owners and returns | Provenance | Open fibre |
|---|---|---|---|---|
| `definition` | official boundary | `HodgeConjecture.Datum`: cycle space, rational cohomology, cycle-class map, rational `(p,p)` submodule, and an explicit `Official` admission predicate | local pose over Mathlib rational modules and submodules | actual smooth projective complex varieties, singular cohomology, Hodge decomposition, and cycle realization |
| `proved-derived; formal-checked` | open population | `theHodgeConjecture_iff_noOpenHodgeClass` | local derivation | emptiness of the open population remains unproved for official realizations |
| `proved-derived; formal-checked` | index geometry | `HodgeIndex.lean`: ample positive direction and negative-definite orthogonal complement in the declared receiver form | project-specific Hilbert-space realization of the signature mechanism | no typed transport currently identifies this model with the intersection form of an admitted variety |
| `proved-derived; formal-checked` | geometric difference | `MillenniumDifferenceAtlas.hodgeQuotientDifference`: a class is sent to `Cohomology / algebraicSpan`; it vanishes exactly on algebraic classes; open Hodge classes are precisely nonzero quotient differences | project-specific composition of the official pose with Mathlib quotient modules | the quotient is intentionally not condensed to a scalar without a separating receiver theorem |

[open] The next Hodge return is an actual official surface realization with rational `H²`, divisor
cycles, the cycle-class map, `(1,1)` classes, an ample class, and its intersection pairing.  Once
that carrier exists, the checked quotient difference and Hodge-index form can be transported into
the same object rather than compared by prose.

## 7. Navier--Stokes

| Grade | Layer | Principal owners and returns | Provenance | Open fibre |
|---|---|---|---|---|
| `definition` | official boundary | `NavierStokes.lean`: three-dimensional fields, derivatives, viscosity, pressure, forcing, decay/periodicity, energy, and the four Clay alternatives | local pose checked against the external statement geometry | no Clay alternative is proved by the pose |
| `proved-derived; formal-checked` | exact fluid calculus | periodic energy/enstrophy/flux, curl and vorticity, Kelvin/moving-loop/material-polygon laws, Hodge/Leray projectors, Fourier triads, heat transport, Duhamel returns, scaling, and overlap uniqueness across the `NavierStokes*` family | project-specific composition of Mathlib analysis, measure, Fourier, and finite combinatorics | each theorem retains its declared regularity, periodic, finite-frequency, or conditional aperture |
| `conditional; formal-checked` | continuation | `NavierStokesCriticalContinuation.lean` and the weighted path/reconstruction tower return compatible continuation from named high-order, integrability, restart, and reconstruction hypotheses | local conditional derivation | the hypotheses are not hidden global-regularity proofs |
| `proved-derived; formal-checked` | dyadic Hodge faces | exact zero-padded second differences, all eight Boolean coordinate-face Abel identities, Haar penalties, low-scale bounds, and the composition from a uniform subset-mass return to a physical kernel bound and continuation | project-specific composition | `UniformLargeScaleDyadicHodgeSubsetMassReturn constant` is uninhabited |
| `proved-derived; formal-checked` | measured difference | `MillenniumDifferenceAtlas.dyadicHodgeSubsetMassExcess`: each subset obligation is exactly `mass - constant·scale ≤ 0`; the uniform return is the same law over every scale `≥3`, all 27 Hodge entries, and all 8 faces | project-specific composition | prove one common constant and all of those nonpositive excess returns |

[open] The immediate Navier--Stokes theorem target is now sharply exposed: inhabit
`UniformLargeScaleDyadicHodgeSubsetMassReturn C`.  Existing checked faces include the exact direct
subset identities and partial scale estimates, but the common three-dimensional padded/reindexed
coefficient comparison and the remaining face assembly have not returned.  Even after this
coefficient port closes, the continuation theorem visibly retains its critical-vorticity
integrability and terminal restart hypotheses.

## 8. Yang--Mills and mass gap

| Grade | Layer | Principal owners and returns | Provenance | Open fibre |
|---|---|---|---|---|
| `definition` | official boundary | `YangMills.lean`: compact-simple group admission, four-dimensional continuum QFT port, axioms, nontriviality, spectrum, and positive gap | local pose | actual gauge/QFT construction and proof of its axioms |
| `proved-derived; formal-checked` | receiver-form gap | `MillenniumCoupling.lean` and `MassGap.lean`: coercivity, definiteness, unit-sphere lower bound, vacuum radical, quotient necessity, perturbation law, compactness obstruction | project-specific composition of standard functional analysis | an abstract positive form is not yet the Yang--Mills Hamiltonian |
| `conditional; formal-checked` | finite transport spectrum | `HilbertTransportSpectrum.lean`: chain Laplacian positivity, harmonic radical, quotient positive definiteness, finite nonnegative spectrum, and positive minimum under a nonharmonic witness | local conditional derivation over Mathlib spectral theory | finite spectrum does not supply a continuum-uniform gap |
| `counterexample; formal-checked` | limit control | `YangMillsLimit.lean`: every finite spectrum `{0,1/(n+1)}` has a pointwise gap while no positive uniform gap survives the family | local counterexample | construct a genuine gauge scaling family and a separator that survives its continuum receiver |
| `proved-derived; formal-checked` | measured difference | `MillenniumDifferenceAtlas.gap_iff_positive_unit_energyDifferences`: coercivity is exactly one positive lower bound on energy differences from the zero vacuum over the unit sphere | project-specific composition | the required physical energy form and continuum calibration remain open |

[open] The next Yang--Mills object is a typed scaling family carrying gauge group, lattice spacing,
volume, reflection positivity, tightness/continuum reconstruction, and one uniform spectral
separator.  Another isolated finite diagonalization cannot close the already-proved limit
counterexample.

## 9. Poincaré and P versus NP

| Grade | Problem | Current local surface | Provenance | Disposition |
|---|---|---|---|---|
| `proved-standard` | Poincaré | `PoincareConjecture.lean` imports Mathlib's topological and smooth three-manifold propositions | external solved theorem boundary; no local Perelman proof term | retained as a regression and geometric pivot, not an open Millennium target |
| `definition` | P versus NP | `PVersusNP.lean` fixes word and pair encodings, TM-computable polynomial-time predicates, verifiers, reductions, `P=NP`, and `P≠NP`; the pair-length theorem is locally checked | local pose over Mathlib computability | intentionally deferred as a direct target; neither equality nor separation is proved |

## 10. The corrective difference atlas across the open problems

[proved-derived; formal-checked] `Millennium/MillenniumDifferenceAtlas.lean` is the compact formal
crosswalk created by this deed:

| Worktrack | Source carrier | Returned difference | Receiver condition |
|---|---|---|---|
| RH | complex spectral point | `Re(s) - 1/2` | zero exactly on the self-conjugate seam |
| BSD rank | finite analytic and algebraic candidates | integer rank difference | zero exactly when candidates agree |
| BSD ledger | central value and arithmetic ledger value | complex subtraction | zero exactly at the rank-zero ledger identity |
| Hodge | rational Hodge class | quotient class modulo the algebraic span | zero exactly for an algebraic class |
| Yang--Mills | vacuum and excited state | quadratic energy difference | one positive lower bound on every unit state is coercivity |
| Navier--Stokes | subset mass and scale allowance | facewise real excess | nonpositive on all addressed faces is the current coefficient return |

[interpretation] This common pattern is the useful holonic unification: each problem asks whether
local transported data return a global zero, positive separator, quotient class, or bounded excess
under a declared receiver.  The formal atlas proves the displayed maps and equivalences.  It does
not assert that all six source theories are identical, and the next derivation is always the named
open fibre in the source carrier rather than another analogy.

## 11. Parallel exterior work order

[definition] The theorem work order following this catalog is:

1. **Navier--Stokes:** prove the common three-dimensional subset-mass constant and inhabit
   `UniformLargeScaleDyadicHodgeSubsetMassReturn`.
2. **BSD:** close or further factor the displayed Waldspurger--Tunnell defect while preserving the
   finite ternary coefficient and analytic theta lineages.
3. **Hodge:** construct one official surface realization and transport the quotient difference and
   Hodge-index form into it.
4. **RH:** construct the weighted argument-principle and archimedean/boundary returns needed by the
   explicit-formula receiver, then pose positivity on the resulting complete functional.
5. **Yang--Mills:** construct a scale-indexed gauge/QFT approximation family and demand a uniform
   energy-difference separator through the continuum receiver.
6. **Cross-domain reuse:** use the measured parametron only where a source worktrack supplies
   actual constitutive sections and chart transitions; retain every reconstruction fibre rather
   than replacing geometry by a binary face.

[definition] This order is an exterior mathematical worktrack.  It does not supersede
`blueprint/THE_ROADMAP.md`, schedule the production engine, or authorize updates to root
`CONSTRUCTION_STATE.md`.

## 12. Maintenance rule

[project-postulate] A Millennium theorem is not considered surfaced merely because its file exists.
Whenever a worktrack gains a stronger unconditional theorem, loses a hypothesis, constructs a
previously declared datum, or exposes a smaller residual, this catalog must update the corresponding
row in the same exterior formal station.

[project-postulate] Every catalog promotion must name one source declaration, one checked return,
one provenance class, and one remaining fibre.  A locally authored proof is recorded as a local
derivation; historical novelty remains `open` until separately audited.

## 13. Evidence records

[historical] The initial seven-object import and DeepMind `formal-conjectures` comparison is
recorded in
`research/records/2026-08-22_THE_SEVEN_MILLENNIUM_OBJECTS_ENTERED_THE_LEAN_BOUNDARY_AND_THE_PARALLEL_SQUEEZE_WAS_TYPED.md`.

[historical] The torus, knot, curved-arc, dimensional, and external knot-formalization audits are
recorded in
`research/records/2026-08-24_THE_ADDRESSED_INSTANCE_LADDER_RETURNED_GEOMETRIC_TORI_CURVED_ARCS_AND_AN_ELEVEN_RANK_QUOTIENT.md`.

[historical] The coupled-LC and complex-parametron source audit is recorded in
`research/records/2026-08-24_THE_COMPLEX_PARAMETRON_IS_AN_ORIENTED_COUPLED_LC_LATTICE_BEFORE_PHASE_LOCKING.md`.
