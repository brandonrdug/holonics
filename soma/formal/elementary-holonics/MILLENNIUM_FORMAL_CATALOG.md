# Millennium formal catalog

**Date:** 2026-08-25
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

[established-bounded; measured] On the 2026-08-25 source closure after transporting the dyadic
Hodge strain into an exact spatial-kernel direction-cancellation carrier, the station contains:

| Receiver | Returned count |
|---|---:|
| Lean modules below `ElementaryHolonics/` | 457 |
| theorem or lemma declarations | 5,838 |
| theorem, lemma, definition, abbreviation, structure, class, or inductive declarations | 8,294 |
| modules below `ElementaryHolonics/Millennium/` | 411 |
| theorem or lemma declarations below `Millennium/` | 5,446 |
| broad declarations below `Millennium/` | 7,639 |
| explicit `#print axioms` audit commands below `Millennium/` | 1,509 |

[established-bounded; measured] The principal module bands are 16 Foundation modules, 2 Algorithm
modules, 8 Geometry modules, 20 dedicated RH modules, and 411 Millennium modules.  Search prefixes
inside the Millennium band include 198 `NavierStokes*`, 30 `Family*`, 15 `General*`, 10 `Five*`, 6
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
| `proved-derived; formal-checked` | `Foundation/PrimeValuationRadixAtlas.lean`, `Millennium/PrimeRadixAtlas.lean` | unique factorization of naturals and Mathlib's `Nat.factorization` | the complete prime-valuation face reconstructs every nonzero population; an exact radix chart returns a unique maximal depth and terminal residual; all prime coordinates balance; equal-depth additive valuation caustics transport through common scale | radix notation never licenses rounding, and the atlas does not turn an unproved analytic bound into a theorem |
| `proved-derived; formal-checked` | `Foundation/TransportLift.lean`, `ReceiverQuotient.lean`, `ExactPartition.lean`, `LatticeTransport.lean`; `Geometry/DivisorAtlas.lean`; `Millennium/ValuationDivisorLatticeAtlas.lean` | additive kernels and quotients, integer modules, finitely supported functions, unique factorization | a general transport request returns an empty/singleton/kernel-coset fibre; partitions reconstruct as dependent sums with paired oriented boundaries; scalar divisibility is isolated as a multiplication lift; signed codimension-one ledgers turn inversion into negation and ratios into differences; Cartier transitions glue local ledgers; lattice maps return kernel, image, cokernel, finite index, torsion witnesses, and saturation | every specialization still owes its geometric locus, chart cover, constitutive transport, and official local-to-global theorem; no scalar factorization is promoted to a source-holon product |
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
| `proved-derived; formal-checked` | exact prime/radix face | `PrimeIndex.lean` and `PrimeRadixAtlas.lean`: `17 = P 6`; the maximal binary charts `34 = 2^1*17` and `2 = 2^1*1`; subtracting the normalized branch equations returns `v^2 - 17*u^2 = 1` | project-specific composition of prime indexing, exact factorization, and the existing congruent-seventeen descent | the prime index is an ordering receiver; the arithmetic load is carried by the valuation/residual face, and this normalization alone does not prove the BSD rank or ledger clauses |
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
| `proved-derived; formal-checked` | dyadic Hodge faces | exact zero-padded second differences, all eight Boolean coordinate-face Abel identities, Haar penalties, low-scale bounds, and the composition from the now-inhabited uniform subset-mass return to a physical kernel bound and continuation | project-specific composition | the coefficient and kernel interfaces are closed; downstream continuation retains critical-vorticity integrability |
| `proved-derived; formal-checked` | anisotropic Hodge product words | the `(1,1,2)` and `(1,2,2)` differences equal their complete 16/32-occurrence ledgers and exact 12/18-face binomial returns; occurrence sums equal the commuting returns, and genuine Hodge entries instantiate both identities | local derivation from the addressed higher-difference owner | prove the Hodge-specific pointwise norm bounds and finite mass assembly |
| `proved-derived; formal-checked` | full three-axis coefficient passage | `NavierStokesDyadicHodgeThreeAxisAllocation.lean` constructs the complete three-axis backward-padded chart, proves all six aperture flanks reconstruct the finite cube, carries each coordinate difference through the chart, identifies the actual full zero-padded coefficient with the `64 -> 27` allocation return, and identifies the official full-coordinate subset mass with its finite norm population | source-specific composition of the direct dyadic coefficient, zero-extension, higher-difference, and subset-receiver owners | closed through the exact full-mass and Boolean-reconstruction owners below |
| `proved-derived; formal-checked` | all scalar allocation charts | `NavierStokesDyadicHodgeThreeAxisScalarChart.lean` proves the direct scalar band equals its triple delayed finite cube on the complete padded lattice, proves arbitrary-order chart naturality, and identifies every admitted `(a,b,c) in {0,1,2}^3` global face at its complementary shift with the existing natural tensor variation | source-specific reconstruction from the scalar band, delayed zero extension, natural forward transport, and tensor separation | compose each scalar face with its addressed complementary Hodge-entry bound |
| `proved-derived; formal-checked` | zero-scalar / full-Hodge corner | `NavierStokesDyadicHodgeThreeAxisCornerMass.lean` identifies the actual `(0,0,0)` allocation face with its global product chart, removes all three pairs of left aperture residues exactly, obtains the complete `222` Hodge stencil from a nonzero scalar pin, and proves its global mass is at most `4096000000000000000 / R^3` for every scale at least three | source-specific composition of scalar support, controlled Hodge scale descent, tensor Fubini mass, and exact three-axis reindexing | transport the same proof through the remaining 26 allocation addresses, using axis-addressed variants for the permuted `112` and `122` complements |
| `proved-derived; formal-checked` | scalar-third-order-two allocation slab | `NavierStokesDyadicHodgeThreeAxisThirdTwoSlice.lean` descends the complementary third-order-zero Hodge stencil to the genuine first/second two-axis stencil, bounds all nine natural product faces, retains their exact binomial weights, and proves the complete actual slab mass is at most `12416369280072 / R^3` at every scale at least three | source-specific composition of the all-orders scalar chart, controlled support, two-axis pointwise Hodge bounds, tensor Fubini mass, and exact weighted allocation faces | the other coordinate slabs are now closed by the generic axis-addressed owner; compose the `111` face and derive the six residual `112`/`122` pointwise laws |
| `proved-derived; formal-checked` | other scalar-order-two allocation slabs | `NavierStokesDyadicHodgeThreeAxisOtherTwoSlices.lean` proves the two-axis complementary Hodge law for arbitrary distinct coordinate axes, constructs a generic natural mass for every actual weighted allocation address, and bounds both the scalar-first-order-two and scalar-second-order-two slabs by the same exact `12416369280072 / R^3` numerator | axis-addressed composition of the support-stencil projections, generic weighted face factorization, tensor Fubini envelopes, and the established two-axis Hodge laws | among the eight addresses in `{0,1}^3`, compose the existing `111` and `222` pointwise laws and derive the six permuted `112`/`122` pointwise laws |
| `proved-derived; formal-checked` | central scalar/Hodge `111` face | `NavierStokesDyadicHodgeThreeAxisOneFace.lean` composes the pointwise three-axis `111` Hodge-entry theorem with the exact central scalar chart and support stencil; its unweighted natural mass is at most `28928000000 / R^3`, and its actual multiplicity-eight allocation mass is at most `231424000000 / R^3` | source-specific composition of the complete `111` product ledger, dyadic Hodge scale descent, scalar tensor Fubini mass, and the generic weighted allocation owner | compose and reindex the six residual natural face masses into the common official allocation population |
| `proved-derived; formal-checked` | strict `112`/`122` Hodge-entry descent | `NavierStokesHodgeEntryScaleDescent.lean` proves a quotient recurrence for every right section whose denominator product is annihilated, proves that every axis-addressed `112` and `122` word annihilates the genuine quadratic Hodge numerator, condenses their complete product ledgers to five and seven translated predecessor occurrences, and derives pointwise Hodge-entry bounds for all six permutations with exact dyadic envelopes `34505600000 / R^4` and `7483641600000 / R^5` | source-specific composition of the addressed product rule, quadratic numerator annihilation, controlled-stencil rebase, lower-order Hodge-entry laws, and exact dyadic aperture descent | compose the six pointwise laws with their complementary scalar faces and reindex every natural face mass into the common official allocation population |
| `proved-derived; formal-checked` | six residual masses and 27-face common-chart gluing | `NavierStokesDyadicHodgeThreeAxisResidualFaces.lean` composes all three `110/112` and all three `100/122` faces, proves their exact weighted six-face mass `23095748198400000 / R^3`, proves coordinatewise vanishing before every complementary offset, and consequently reindexes every one of the 27 actual weighted face masses exactly from the common doubly padded population to its natural translated population | source-specific composition of strict Hodge-entry descent, scalar support causation, tensor Fubini mass, exact occurrence weights, and complete prefix-fibre elimination | apply the 27-face triangle inequality on the common population, sum the already proved face constants without overlap, and transport that return to the official full-coordinate subset mass |
| `proved-derived; formal-checked` | complete full-coordinate mass | `NavierStokesDyadicHodgeThreeAxisFullMass.lean` proves the staged `3 × 9` return equals the complete addressed 27-face sum, proves the norm and six-axis finite Fubini passages, assigns every face its exact integer numerator, proves their sum is `4119133228099520072`, and transports the resulting inverse-cubic bound to the official `univ` subset receiver for every scale at least three | source-specific composition of exact Leibniz reconstruction, address-retaining triangle inequality, proved common-chart gluing, all 27 face bounds, and exact finite arithmetic | construct the other seven Boolean subset receiver bounds and assemble one common constant for `UniformLargeScaleDyadicHodgeSubsetMassReturn` |
| `proved-derived; formal-checked` | complete Boolean reconstruction and uniform physical carrier | `NavierStokesDyadicHodgeRemainingSubsetMasses.lean` proves exact prefix reconstruction from zero-padded first and second differences, lifts the law through all three coordinate axes, uses the boundary-preserving interchange cell to reconstruct all seven residual Boolean faces, proves their cubic/linear/inverse-linear scale laws, inhabits `UniformLargeScaleDyadicHodgeSubsetMassReturn`, and constructs `UniformDyadicHodgeJacobianKernelBound` | source-specific composition of finite boundary gluing, coordinate Fubini/interchange, the full 27-face mass, the existing two-axis mass, and the Haar receiver | transport the now-unconditional kernel carrier through the logarithmic law; continuation still owes critical-vorticity integrability and terminal restart supply |
| `proved-derived; formal-checked` | completed kernel/logarithmic/continuation passage | `NavierStokesDyadicHodgeCompletedKernelPassage.lean` inhabits the existential uniform-kernel interface, removes the kernel premise from the actual periodic BKM logarithmic Jacobian and lifespan high-order laws, and composes the already constructed weighted classical restart supply; for positive viscosity its continuation constructor now accepts only interval integrability of the critical vorticity rate | exact composition of the completed Boolean receiver, coordinate-Haar kernel return, dyadic logarithmic law, and native weighted restart carrier | prove the critical-vorticity rate is interval-integrable on every finite maximal open lifespan, or return a source-specific obstruction to the current rate receiver |
| `receiver-insufficiency; formal-checked` | sign-bearing strain difference | `NavierStokesVorticityStrainDifference.lean` proves that the canonical skew jet reconstructed from vorticity annihilates that same vorticity, so the signed stretching reading is carried exactly by symmetric strain; explicit trace-free jets have equal curl and divergence but stretching readings `+1` and `-1` | source-specific composition of the actual `Matrix3` curl, divergence, Hodge jet split, and inner-product action owners | curl, divergence, and vorticity magnitude cannot factor the remaining integral; construct the symmetric Hodge/Biot--Savart strain passage with its vorticity-direction difference retained |
| `proved-derived; formal-checked` | exact Fourier direction remainder | `NavierStokesVorticityDirectionCancellation.lean` takes the symmetric face of the genuine-torus Hodge reconstruction, proves its nonzero-mode stretching reading is an exact scalar triple product, proves every receiver-aligned source component vanishes, and factors every finite actual-solution population through character-transported vorticity after arbitrary aligned subtraction | source-specific composition of actual periodic vorticity coefficients, nonzero-mode Hodge/Biot--Savart ascent, symmetric strain, torus characters, and finite addressed sums | bound the returned direction remainder by a scale-correct angular/coherence receiver and compose it with viscous direction-curvature damping |
| `proved-derived; formal-checked` | canonical direction projection | `NavierStokesVorticityDirectionProjection.lean` defines the unique receiver-aligned amplitude and bilinearly orthogonal remainder, proves exact reconstruction and uniqueness, discharges the nonzero projection denominator for the complexification of every nonzero real vorticity vector, handles zero-vorticity receivers separately, and factors the actual finite Hodge-strain return through the canonical projected remainder | source-specific composition of the returned direction-difference carrier with the actual real pointwise vorticity and transported torus modes | prove a uniform scale-correct norm/coherence bound for the canonical remainder and descend it through the full Fourier reconstruction |
| `proved-derived; formal-checked` | uniform finite direction-remainder bound | `NavierStokesVorticityDirectionRemainderBound.lean` proves exact three-coordinate `L¹` dot and cross transport bounds, proves `|k|₁² ≤ 3|k|₂²`, cancels the complete nonzero-frequency modulus, and bounds every actual finite Hodge-strain return by `3 |r|₁²` times the sum of canonical direction-remainder norms | source-specific norm composition of the scalar-triple-product law, integer lattice geometry, canonical projection, and actual periodic finite population | control the exact finite direction-remainder mass uniformly across scale and descend the result through full Fourier reconstruction and terminal time |
| `proved-derived; formal-checked` | actual finite-band gluing | `NavierStokesVorticityDirectionFiniteBandBridge.lean` proves Hodge ascent is complex-linear, symmetrization and the quadratic receiver commute with finite addressed sums, identifies the direction-remainder scalar exactly with the symmetric Hodge-band reading, then transports it through `openPeriodicHodgeJacobianBandProjector_eq_actual` to the actual finite Jacobian band | exact reconstruction/gluing of the modewise direction carrier with the existing solution derivative projector | pass the actual finite-band estimate to the full smooth Jacobian via a proved cofinal Fourier convergence mode, while retaining the remainder-mass limit |
| `proved-derived; formal-checked` | full strain reconstruction with addressed tail | `NavierStokesVorticityDirectionFullStrain.lean` proves that the complete symmetric Jacobian stretching receiver is exactly the finite direction-depleted band plus its complementary Fourier tail, controls the tail action by the complete nine-face coefficient mass, and on every frequency cube supplies the explicit `sqrt(jacobianTailScale radius * jacobianTailLatticeMass)` weighted-`H³` return | exact composition of complete coordinate Fourier reconstruction, actual finite-band Hodge gluing, canonical direction projection, and the proved coefficient-tail decay law | the Fourier limit seam is closed as an exact remainder-carrying inequality; prove uniform control of the direction-remainder population and connect the complexified receiver to the real local stretching/integrability passage |
| `proved-derived; formal-checked` | physical vortex-stretching bridge | `NavierStokesVorticityDirectionPhysicalBridge.lean` proves real continuous-linear action and Euclidean inner product commute exactly with coordinatewise complexification, constructs the quotient-descended real stretching occurrence, proves its pullback is the literal periodic-enstrophy integrand, and identifies its absolute value exactly with the norm of the complete Fourier strain chart | exact chart transition from the real torus Jacobian/vorticity owners through the complex Hodge/Fourier receiver back to the physical integrand | the receiver identity is closed; uniformly control the explicit direction-remainder population strongly enough to integrate it in space and time and absorb or continue the enstrophy law |
| `proved-derived; formal-checked` | geometric cross-difference reconstruction | `NavierStokesVorticityDirectionCrossReconstruction.lean` proves the receiver/source cross annihilates exactly the aligned projection face, reconstructs the complete canonical orthogonal remainder by the vector triple product on every nonzero real receiver chart, proves cross vanishing iff remainder vanishing, and transports the full physical stretching estimate through the finite addressed cross-direction mass; zero-vorticity points close separately without an inverse | source-specific composition of the swing-derived cross owner, canonical projection, exact vector triple product, physical stretching bridge, and Fourier-tail reconstruction | identify the cross population as Fourier transport of the two-point spatial vorticity-direction difference, then prove the required spatial/scale/time coherence return rather than estimating it by coefficient count |
| `proved-derived; formal-checked` | two-point coherence Fourier carrier | `NavierStokesVorticityDirectionCoherenceFourier.lean` bundles fixed-receiver cross as a complex continuous-linear map, proves it commutes with the genuine-torus Bochner Fourier integral, identifies every actual cross coefficient with the coefficient of `y ↦ omega(x) × omega(y)`, proves character transport preserves the exact `L¹` mass, and rewrites the complete physical stretching inequality through that literal coherence-field coefficient population | exact quotient/Fourier composition of actual torus vorticity, continuous-linear cross transport, addressed character return, cross reconstruction, and physical strain | the coefficient interpretation is closed; construct a spatial norm/singular-kernel receiver for the coherence field and prove a uniform scale/time law strong enough for the enstrophy integral |
| `proved-derived; formal-checked` | complete coherence summability and aperture removal | `NavierStokesVorticityDirectionCoherenceSummability.lean` proves the six addressed Jacobian entries majorize every curl coefficient, proves absolute summability of the complete vorticity and two-point cross populations, constructs their full `ℓ¹` masses, proves every finite aperture is bounded by the same full carrier, proves the fixed-receiver capacitance law `coherenceMass(x) ≤ |omega(x)|₁·vorticityCoefficientMass`, sends the explicit Jacobian reconstruction fibre to zero, and concludes a radius-free pointwise bound of physical vortex stretching by the complete coherence mass | exact composition of curl incidence, smooth-slice `H³` coefficient summability, continuous-linear cross/Fourier transport, finite-to-infinite `tsum` gluing, and the proved reciprocal tail scale | the spatial-scale aperture is closed; prove a terminal-time-uniform or space-time-integrable bound for this full coherence carrier, preferably through a geometric difference/Besov or singular-kernel receiver that composes with viscous direction-curvature dissipation |
| `proved-derived; formal-checked` | physical-space dyadic direction cancellation | `NavierStokesVorticityDirectionKernelCancellation.lean` constructs the exact finite Fourier kernel of each dyadic symmetric Hodge band, identifies its convolution with the actual dyadic strain, proves that an independently varying source component aligned with the fixed receiver annihilates pointwise at every displacement, rewrites the band reading as the Bochner integral of the canonical receiver-relative remainder, and bounds it by both the kernel-weighted direction-remainder mass and its exact cross-coherence reconstruction | source-specific composition of the dyadic Hodge multiplier, torus-character transport, Bochner convolution, symmetric stretching receiver, canonical direction projection, and cross-product reconstruction | the finite scale assembly is closed by the next owner; the remaining law is infinite-depth and terminal-time control |
| `proved-derived; formal-checked` | complete spatial dyadic scale assembly | `NavierStokesVorticityDirectionKernelScaleAssembly.lean` proves symmetric stretching commutes with arbitrary finite occurrence populations, reconstructs the full strain exactly as fixed base plus every ordered dyadic spatial direction-remainder integral plus the addressed high-frequency fibre, constructs summed direction- and cross-coherence words, and bounds the full strain by fixed base, the literal summed cross population, and the exact coefficient tail | exact reconstruction/gluing of the complete dyadic Hodge scale chain with the physical-space kernel cancellation, canonical projection, cross reconstruction, low-pass bound, and coefficient-tail owner | the coefficient fibre is removed by the next owner; prove the scale constitutive law and terminal-time return |
| `conditional; formal-checked` | infinite-depth spatial cross receiver | `NavierStokesVorticityDirectionKernelScaleLimit.lean` constructs the full spatial cross-coherence `tsum`, proves every finite word is uniformly bounded by it under the exact summability condition, proves dyadic cutoffs escape to infinity, sends the coefficient reconstruction fibre to zero on every strict-interior slice, and returns an infinite-depth bound for the literal real vortex-stretching integrand, including the zero-vorticity chart | exact limit composition of the spatial scale assembly, smooth-slice coefficient decay, dyadic cofinality, nonnegative `tsum` gluing, and the physical stretching bridge | prove the displayed dyadic spatial cross population is summable from a scale-correct direction/coherence law rather than assuming it; replace the fixed base's critical-rate bound by a lower-order energy carrier and establish the resulting space-time estimate up to maximal time |
| `conditional; formal-checked` | modulus-to-kernel-moment constitutive passage | `NavierStokesVorticityDirectionKernelMoment.lean` defines a continuous nonnegative receiver-relative spatial cross modulus, constructs the matching physical Hodge kernel moments, proves the actual cross mass at every scale is bounded by `constant × moment`, and proves summable moments construct both the full cross-coherence summability carrier and a full-mass bound; integer powers of torus distance instantiate the modulus interface | exact spatial integral transport through the positive kernel-point-mass receiver, continuous compact integration, nonnegative comparison, and `tsum` gluing | prove a decaying moment law for the actual dyadic Hodge kernel for a scale-correct fractional or integer direction modulus, and prove the solution supplies that modulus with terminal-time-integrable coefficient |
| `receiver-insufficiency; formal-checked` | uniform scale bound versus summability | `NavierStokesVorticityDirectionKernelMoment.uniform_nonnegative_scale_bound_does_not_imply_summable` exhibits the constant nonnegative scale population `1`, uniformly bounded by `1` but not summable | exact real-series counterexample | the completed uniform kernel `L¹` law cannot close the infinite-depth direction carrier without a genuinely decaying localization/moment return |
| `counterexample; formal-checked` | coarse coefficient magnitude | `PrimeRadixAtlas.lean`: the declared intermediate bound faces sum to `412236000 = 2^5*3^3*5^3*11*347`; `347` is absent from both incoming terms and appears after addition | exact natural arithmetic and prime valuation | `420000000` is a rounded enlargement of this intermediate return; the separate `42*10^17` common-magnitude proposal is withdrawn because no complete assembly returns it |
| `proved-derived; formal-checked` | measured difference | `MillenniumDifferenceAtlas.dyadicHodgeSubsetMassExcess`: each subset obligation is exactly `mass - constant·scale ≤ 0`; `NavierStokesDyadicHodgeRemainingSubsetMasses.lean` proves one common constant and all those nonpositive excess returns over every scale `≥3`, all 27 Hodge entries, and all 8 faces | project-specific composition | the excess and restart receivers are closed; the next difference is the critical-vorticity integrability defect |

[proved-derived; formal-checked] The immediate coefficient target is closed.  The exact
zero-exterior prefix gluing reconstructs each removed coordinate with cost `N(N+1) ≤ 72R²`; the
full and `{0,1}` source faces therefore generate all eight scale-correct receiver faces.  The
common returned constant is `72·72·4119133228099520072`, and the named large-scale subset return
and uniform physical dyadic kernel carrier are inhabited without analytic hypotheses.

[proved-derived; formal-checked] The magnitude-only alternative has been falsified, and the
surviving fibre is retained through two exact receivers.  The complete Fourier receiver proves
absolute summability and removes the finite aperture.  The sharper spatial receiver reconstructs
each dyadic strain band as a convolution, cancels the aligned source at every displacement before
integration, and retains only the kernel-weighted direction difference or its lossless oriented
cross reconstruction.  The next local-to-global edge is therefore the complete dyadic scale
assembly followed by a source-specific terminal-time estimate proving enough space-time
integrability of that geometric carrier to close the enstrophy/critical-vorticity return.

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

## 10a. Exact prime/radix faces and caustics

[proved-derived; formal-checked] `Foundation/PrimeValuationRadixAtlas.lean` makes the radix gesture
exact.  For every nonzero natural population, `primeValuationAtlas` is its finitely supported
prime-exponent face and its prime-power product reconstructs the source.  An
`ExactRadixChart b n` returns `n = b^k*rho`, proves `k` maximal among the exponents whose radix
power divides `n`, and consequently proves that `b` does not divide `rho`.  Two such charts of the
same source are equal in both depth and residual.

[proved-derived; formal-checked] The chart balance is equality of complete atlases:

```text
valuationAtlas(n) = k * valuationAtlas(b) + valuationAtlas(rho).
```

For `42*10^17`, the returned face is exactly `2^18*3*5^17*7`, the maximal decimal depth is `17`,
and the terminal residual is `42`.  This statement concerns that exact integer occurrence only; it
does not rehabilitate the withdrawn Navier--Stokes rounding.

[proved-derived; formal-checked] `AdditivePrimeCaustic p a b d` records that the incoming
valuations agree at depth `d` while the valuation of `a+b` is strictly larger.  The displayed
intermediate bound arithmetic has incoming faces `396000` and `411840000 = 1040*396000`; their return is
`1041*396000 = 3*347*396000`.  Thus `347` appears by exact additive cancellation in that prime
chart, and multiplying the whole occurrence by any positive common scale transports the caustic
by adding precisely the scale's `347`-valuation.

## 10b. Transport lifts, partitions, divisor ledgers, and lattice quotients

[proved-derived; formal-checked] The word `divisor` is now split into typed owners rather than
allowed to act as one universal operation:

| Typed owner | Exact object | Returned inverse information |
|---|---|---|
| `TransportLift` | solutions of `transport source = target` | empty obstruction, singleton, or complete fibre |
| additive transport lift | one inhabited fibre | an explicit equivalence with a translate of the kernel |
| `PartitionReceipt` | occurrence-to-piece address plus paired oriented cut sides | equivalence of the source population with the dependent sum of piece fibres; paired hand cancels |
| `NatFactorWitness d n` | `n = d*k` with `k` retained | equivalence with `d ∣ n`; uniqueness only when `d > 0` |
| `ReceiverQuotient` | every declared receiver factors through `q` | complete predecessor fibre; a section is separately declared structure |
| `WeilDivisorLedger` | finite signed population of declared codimension-one loci | inversion negates coefficients; a function quotient subtracts ledgers |
| `CartierDivisorAtlas` | local equations joined by admitted unit transitions | overlap cocycle, reverse transition, and equality of local divisor ledgers |
| `LatticeIndexReceipt` | integer-linear transport with finite cokernel | kernel, image, complete lift fibre, cokernel, exact index, torsion witness, saturation |

[proved-derived; formal-checked] The existing binary normalized-exponential adaptation is now an
instance of `ReceiverQuotient`, not a newly invented softmax theory.  Its quotient is the oriented
potential difference, its factor is the existing logistic-difference chart, and every common
potential shift is exhibited in one reconstruction fibre.  This composes the Lean owner with the
engine's established `RatioFamily`/receiver-exact-compression doctrine while leaving the engine's
full exact cocycle strictly richer than the binary formal instance.

[proved-derived; formal-checked] The rational finite-place ledger in `PlaceLedger.lean` now lands
in one finitely supported signed divisor population.  Every occupied natural address is proved
prime, every coefficient returns the established local ledger, and inversion negates the complete
ledger simultaneously.  This is the first checked bridge from the place atlas into the geometric
signed-divisor carrier.

[definition] These owners refine the common staircase.  The generic operation is now

```text
source occurrence
  -> typed transport or partition
  -> receiver face
  -> complete lift / reconstruction fibre
  -> kernel, boundary, signed locus, or cokernel obstruction
  -> chart gluing and scale/place transport
  -> official problem receiver.
```

[open] RH still needs the complete prime/zero/archimedean divisor passage and positive Weil
receiver. BSD needs genuine elliptic-curve divisor classes, local heights, Selmer--`Sha`, and the
analytic ledger. Hodge needs an official variety whose codimension-one Cartier/Weil divisors and
higher cycles enter its cycle-class map. Yang--Mills needs bundle-transition and continuum
reconstruction owners. Knot and three-manifold routes need the geometric connected-sum and
Reidemeister quotient rather than arithmetic factorization. Fluid routes use the partition,
lift, boundary, and lattice owners but acquire divisor language only after a genuine zero, pole,
or defect locus is founded.

## 11. Holonics is the source catalog: the common closure staircase

[definition] A **candidate solution condition** in this catalog is a typed sufficient theorem
family, not a prediction that its hypotheses are already available.  It must name the official
target receiver, the local entering receiver, every composition and limit needed between them, and
an insufficiency witness which can refute the route.  Merely restating the official conjecture under
a new name is not a candidate route.

[definition] The shared staircase is composed from the existing holonics arsenal in this order:

```text
situated occurrence
  -> swing / oriented returned difference
  -> addressed transport word and complete occurrence ledger
  -> annihilator, boundary cancellation, and retained remainder
  -> receiver quotient with its complete reconstruction fibre
  -> chart rebase, route comparison, and holonomy
  -> scale descent / recurrence tower
  -> compactness, tightness, or local-to-global gluing
  -> official Millennium receiver.
```

[proved-derived; formal-checked] The early and middle stairs already have generic Lean owners:
`Swing`, `Lineage`, `HigherDifferenceTransport`, `HigherDifferenceAnnihilator`,
`MeasuredDifferenceReceiver`, chart/rebase and holonomy owners, and
`HigherDifferenceScaleDescent`.  Their exact consequences include oriented differences, `2^n`
shifted-Leibniz occurrence ledgers, sparse zero-certified quotients, complete reconstruction fibres,
noncommuting route defects, and strict predecessor descent.

[definition] The receiver criterion is the common closure test.  For a source population `X`, a
local receiver `entering : X -> Entering`, and the official or later receiver
`returned : X -> Returned`, a transformer exists on the actually presented range exactly when

```text
entering left = entering right  ->  returned left = returned right
```

for every source pair.  A pair with equal entering faces and unequal returned faces is the exact
counterexample: the local atlas has collapsed a distinction the problem still needs.  Enlarging the
receiver by the shortest such separator is the next constructive move.

[interpretation] The staircase repeats across the problems because it is a calculus of local-to-
global factorization, not because the source theories are identified.  RH uses prime/Mellin
transport and a positivity receiver; BSD uses local-place and height transport with an arithmetic-
analytic ledger; Hodge uses cycle-class quotient transport; Navier--Stokes uses dyadic Hodge and
critical continuation; Yang--Mills uses noncommuting gauge holonomy and continuum spectral
reconstruction; Poincare supplies a solved flow/surgery regression; and P versus NP asks whether a
history quotient preserves all complexity-visible successors.

## 12. Candidate solution conditions for all seven worktracks

### 12.1 Riemann hypothesis

[definition] The candidate RH closure theorem is the following composite, over the actual completed
Riemann zeta function and a full admissible Weil test family:

1. construct `HasWeightedArgumentPrinciple` on a cofinal contour family;
2. construct the exact prime plus archimedean residual identity on the same tests;
3. prove the contour/boundary remainder vanishes in the cofinal return;
4. identify the resulting global functional with the classical Weil explicit-formula form;
5. prove that form nonnegative on every admitted test; and
6. import or derive the full positivity equivalence which sends that nonnegativity to
   `RiemannHypothesis`.

[conditional] Those six returns are sufficient because they turn every nontrivial zero into a
source occurrence separated by the complete test family and force its
`criticalSeamDifference = Re(s)-1/2` to vanish.  The present Lean tree owns the symmetry, zero-count,
test-vector, and truncated explicit-formula components; it does not own items 1--6 as one complete
unconditional passage.

[open] The shortest present RH gate is the complete positive Weil carrier, including the
archimedean and boundary returns.  A decisive route falsifier is either a negative value of the
assembled form on an admitted test or two admissible spectral populations with the same complete
entering receiver and different seam placement.

### 12.2 Birch--Swinnerton--Dyer

[definition] The candidate BSD closure has two nested scales.  On the congruent-number family it
requires: an actual `LDatum`; vanishing of the Waldspurger--Tunnell defect on the addressed sign
branch; a finite Mordell--Weil/Selmer descent returning the algebraic rank; equality with analytic
order; and the leading-coefficient ledger with period, regulator, Tamagawa, torsion, and Tate--
Shafarevich factors.  On the universal scale it additionally requires a transport from arbitrary
elliptic curves or abelian varieties into those arithmetic and analytic receivers without erasing
bad-place or `Sha` fibres.

[conditional] A family theorem that the displayed defect vanishes closes the currently typed
positive-sign prime-family rank gate.  A universal theorem still requires the complete analytic
continuation, Mordell--Weil/height, Selmer--`Sha`, and leading-coefficient passages; the checked
witness at one and prime rank bounds do not supply that quantifier change.

[open] The immediate family gate remains `waldspurgerTunnellDefect = 0`; the universal gate is a
receiver-exact adelic arithmetic/analytic ledger for every admitted curve.  A decisive falsifier is
a pair of curves or local histories identified by the proposed entering receiver but separated by
analytic rank, Mordell--Weil rank, regulator, or `Sha` in the official ledger.

### 12.3 Hodge conjecture

[definition] The terminal Hodge condition is already exact in the library:

```text
for every official datum D,
  every class in D.rationalHodgeClasses has zero image in
    D.Cohomology / D.algebraicSpan,
```

equivalently `OpenHodgeClasses Official = empty`.  A constructive holonic route must first build
the real smooth-projective carrier, singular rational cohomology, Hodge decomposition, cycle-class
map, Lefschetz/primitive transport, and intersection receiver.  It must then construct compatible
local sections of the cycle-class map on the rational `(p,p)` population and prove that chart
transport, primitive decomposition, and gluing preserve those sections globally.

[conditional] Such a compatible section sends every rational Hodge class to an algebraic cycle and
therefore kills `hodgeQuotientDifference`.  Hodge--Riemann positivity and the Hodge-index shell are
useful separation/coercivity stairs, but positivity alone does not construct the missing cycle.

[open] The first honest carrier is still one official surface realization in which divisor cycles,
`H^2`, `(1,1)` classes, an ample class, and the intersection form coexist.  A nonzero official
quotient class is both the exact falsifier of the conjecture and the exact insufficiency witness for
any local receiver that fails to see it.

### 12.4 Navier--Stokes

[definition] The periodic smoothness route was factored through three visible continuation ports
for every admitted maximal open periodic solution:

1. one `massConstant` inhabits `UniformLargeScaleDyadicHodgeSubsetMassReturn` across every scale
   `>= 3`, all twenty-seven Hodge entries, and all eight coordinate faces;
2. the actual `criticalVorticityRate` is interval-integrable on every finite lifespan; and
3. the uniform coordinate `H^3` receiver supplies the terminal restart seam.

The checked composition produces `CompatibleOpenPeriodicExtension`; the first and third ports are
now constructed.  A maximal-lifespan argument must turn universal extendibility into global
existence and hence `StatementB` after the second port is returned.

[proved-derived; formal-checked] The Boolean dyadic passage constructs the first port and its
physical Jacobian-kernel bound with explicit constant `804357 + 216 * massConstant`; the native
weighted classical restart owner constructs the third.  Their composition leaves only the second
port before maximal-time globalization.

[receiver-insufficiency; formal-checked] The coefficient gate is closed, while the local
curl/divergence receiver has been proved too coarse: two admitted trace-free jets with the same
curl return opposite stretching signs.  The deeper analytic gate is now the exact periodic
Hodge/Biot--Savart strain reconstruction and its direction-difference cancellation.  That enriched
receiver must either yield critical-rate integrability or return a source-specific obstruction;
the maximal-time globalization follows only after such a return.

### 12.5 Yang--Mills existence and mass gap

[definition] A sufficient Yang--Mills route requires, for every compact simple gauge group:

1. a gauge-covariant lattice/current family with exact plaquette curvature and Wilson/loop
   receivers;
2. reflection positivity and compatible finite-volume measures;
3. uniform renormalized estimates giving tightness as lattice spacing tends to zero and volume to
   infinity;
4. Osterwalder--Schrader or equivalently strong continuum reconstruction into a nontrivial physical
   Hilbert space and Hamiltonian; and
5. one positive spectral separator `Delta` uniform in scale and volume whose law descends through
   that reconstruction.

[conditional] Those returns inhabit the fields of `YangMills.Problem` and prove
`TheYangMillsExistenceAndMassGap`.  Finite chain-Laplacian positivity supplies a bounded spectral
model for item 5, while `YangMillsLimit.theShrinkingFamilyHasNoUniformMassGap` proves that a positive
gap at every finite scale is insufficient without a uniform separator and limit-preservation law.

[open] The exact gate is therefore not another finite diagonalization but a genuine gauge scaling
family with continuum reconstruction and a uniform gap.  A shrinking positive spectrum is the
existing formal falsifier of the weaker route.

### 12.6 Poincare conjecture

[proved-standard] Poincare is solved, so its candidate conditions are a regression target for the
holonic staircase: Ricci flow on the actual three-manifold carrier, monotone entropy/noncollapsing,
classification of singularity models, addressed surgery with topology lineage, continuation across
every surgery time, finite extinction in the simply connected closed case, and identification of
the initial manifold with `S^3`.

[open] The local Lean project currently imports the proposition but not a kernel-checked Perelman
proof.  The regression fails exactly if a local flow/surgery receiver forgets a topology-changing
neck or cannot reconstruct the pre-surgery manifold from its returned pieces.  This makes Poincare
a calibration of the staircase's local-to-global discipline, not an open prize target.

### 12.7 P versus NP

[definition] Holonics admits two exact terminal routes.  A `P = NP` route must uniformly transform
every polynomial-time verifier and polynomial certificate bound into a polynomial-time decider,
with a checked polynomial cost receipt.  A `P != NP` route must construct one NP language and an
encoding-invariant history separator which every polynomial-time deterministic decider obeys but
the language provably violates; it must survive polynomial many-one transport and the relevant
relativization/natural-proof/algebrization barrier audit.

[conditional] Either terminal construction settles the local `PEqualsNP`/`PNotEqualsNP` pose.  An
endpoint Boolean receiver is insufficient for lower bounds because equal answers can carry
different causal histories, branching, and resource fronts; the proposed separator must factor
through complete computation histories and still return a polynomially invariant consequence.

[open] No such uniform verifier-to-decider transformer or universal lower-bound separator exists in
the Lean tree.  A faster decider falsifies a proposed separating invariant; a proved superpolynomial
lower bound falsifies a proposed universal collapse construction.

## 13. Recurrence of recurrence and the derivation atlas

[definition] Repetition and differentiation coincide only after an additive difference receiver
is declared.  If `R_n` is the face returned at recurrence depth `n`, then

```text
Delta R_n = R_(n+1) - R_n,
Delta^k R_n = Delta (Delta^(k-1) R_n).
```

For a discrete transport `T`, the same operator is `T - I` and its `k`th finite difference is
`(T-I)^k`.  Powers `T^n` count repeated transport; they are not derivatives by themselves.  In an
additively enriched category the subtraction occurs in a hom-group; an arbitrary category does not
provide that operation merely because its arrows compose.

[established-bounded; implemented-exact] `soma/tools/derivation-atlas` now returns two additional
receivers without changing the Lean export schema: exact complete-operation argument transitions,
and same-head structural recurrence towers with the finite-difference rows of their occurrence
profiles.  Function-side partial applications introduced by Lean's curried encoding are removed per
use edge rather than by deleting interned nodes.

[established-bounded; measured] On the addressed
`Foundation/HigherDifferenceTransport.lean` bundle, the atlas returned 69,058 expression nodes,
174 declarations, 75 theorem bodies, 1,392 proof events, and 20,078,103 multiplicity-weighted
expression uses.  Its structural receiver found complete `fwdDiff` nesting through order six and
`HSub.hSub` nesting through order six, agreeing with the owner's bounded higher-difference surface.

[definition] These counts are exterior proof-term morphology.  A weighted face-transition matrix
may be composed to count length-`n` expression routes, and its quotient cycles may suggest reusable
proof shapes, but neither a cycle nor a finite-difference row is promoted into a theorem about the
mathematical carrier until a typed source receiver proves that identification.

## 14. The matching-logic supplement: localization is a load-bearing stair

[historical] Chen and Rosu's 2026 preprint, [*Completeness and incompleteness of basic matching
logic*](https://arxiv.org/abs/2608.13306), proves a one-sorted, fixpoint-free global-completeness
result by composing both semantics and derivability through a localization `Delta_Gamma`.  That
localization boxes every hypothesis along every composable coordinate word and denotes the largest
backward-closed core.  A two-sheet cover replaces the unreachable exterior while preserving what
the local language can observe.

[interpretation] This supplies a rigorous audit pattern for the holonic staircase.  Each
Millennium route must exhibit the typed word from its local hypothesis sort to its official
conclusion sort, localize along every admitted word, and return a reconstruction that preserves the
official receiver.  The new receiver-factorization criterion is the set-level form of that last
test; it is not a claim that holonics and matching logic are the same theory.

[historical] The same paper proves that the route is sharp: many-sorted global completeness can
fail when no symbol-input chain carries the hypothesis sort to the conclusion sort, and adding
least fixpoints makes validity non-recursively-enumerable in a very small fragment.  It also states
an open mechanization ladder: the structural/double-cover lemmas, then global completeness assuming
local completeness and soundness, then discharge of local completeness.

[interpretation] The consequence for this project is constructive.  More recursion, tower depth,
or fixpoint syntax is not evidence of global closure.  Every recurrence must retain sort/port flow,
and every proposed local-to-global proof must either produce its receiver transformer or return the
explicit insufficiency pair which tells us which face to add.

## 15. Active exterior closure goal and pivot law

[definition] The active theorem-development objective is:

> Prove or disprove at least one unsolved Millennium problem in Lean by completing a
> source-specific holonic realization passage from local occurrences to the official receiver.
> Work may pivot among Navier--Stokes, RH, BSD, Hodge, Yang--Mills, and P versus NP whenever that
> pivot closes a shared missing edge. Every deed must return at least one of: a constructed official
> carrier, a proved constitutive law, a uniform scale theorem, an exact reconstruction/gluing
> theorem, a removed hypothesis, or a receiver-insufficiency counterexample. Continue until an
> official statement is inhabited or refuted with a complete assumption audit.

[definition] A pivot is therefore licensed by a returned edge, not by resemblance between subjects.
The worktrack may move when a source theorem constructs a carrier or transport reusable by another
official passage, when a counterexample proves the present receiver insufficient, or when an exact
dependency audit identifies a strictly shorter open fibre.  A catalog rewrite, a new analogy, a
conditional wrapper which merely renames its conclusion, or a numerical fit returns no such edge.

[proved-derived; formal-checked] The first deed returned the complete three-axis dyadic Hodge
allocation/reconstruction passage for the actual Navier--Stokes coefficient.  All left and right
aperture residues remain in the chart, the three coordinate operators commute with their natural
addresses, and the official full-coordinate subset mass is exactly the norm population of the
twenty-seven-face allocation return.  The subsequent frontier is selected by the returned
dependency:

[proved-derived; formal-checked] The fourth deed has now returned the first complete nine-face
allocation slab.  Its exact weighted numerator is `12416369280072`, every term has inverse-cubic
radial scale, and no mode-count estimate or rounded enlargement enters the proof.  This closes a
uniform scale theorem admitted by the active goal; it does not yet inhabit a Clay alternative.

[proved-derived; formal-checked] The fifth deed transports that result through proved `(1,2)` and
`(0,2)` stencil projections and returns the other two coordinate slabs with the same exact
numerator.  The three slabs cover all 19 addresses having at least one scalar order two.  The open
pointwise population is therefore no longer “the other 26 faces”: it is the six explicit
permutations of complementary Hodge orders `112` and `122`; the central `111` face is now composed
and uniformly bounded as an actual weighted allocation face.

1. **Navier--Stokes:** carry the 27 allocation faces into
   `UniformLargeScaleDyadicHodgeSubsetMassReturn`, then test whether that receiver factors the
   critical-vorticity and restart receivers.
2. **BSD:** close or further factor the Waldspurger--Tunnell defect while preserving the finite
   ternary coefficient and analytic theta lineages.
3. **Hodge:** construct an official surface realization and transport the quotient difference and
   Hodge-index form into it.
4. **RH:** complete the weighted argument-principle, archimedean, and boundary returns and pose
   positivity on the complete explicit-formula functional.
5. **Yang--Mills:** construct a scale-indexed gauge/QFT approximation family and demand a uniform
   energy-difference separator through continuum reconstruction.
6. **P versus NP:** pursue only a carrier or history-separator theorem that survives the stated
   encoding and barrier audit.
7. **Cross-domain reuse:** compose the existing swing, returned-difference, addressed-word,
   partition, quotient, divisor/lattice, gluing, holonomy, scale-descent, and measured-parametron
   owners only through declared source maps, retaining every reconstruction fibre.

[definition] This order is an exterior mathematical worktrack.  It does not supersede
`blueprint/THE_ROADMAP.md`, schedule the production engine, or authorize updates to root
`CONSTRUCTION_STATE.md`.

## 16. Maintenance rule

[project-postulate] A Millennium theorem is not considered surfaced merely because its file exists.
Whenever a worktrack gains a stronger unconditional theorem, loses a hypothesis, constructs a
previously declared datum, or exposes a smaller residual, this catalog must update the corresponding
row in the same exterior formal station.

[project-postulate] Every catalog promotion must name one source declaration, one checked return,
one provenance class, and one remaining fibre.  A locally authored proof is recorded as a local
derivation; historical novelty remains `open` until separately audited.

## 17. Evidence records

[historical] The initial seven-object import and DeepMind `formal-conjectures` comparison is
recorded in
`research/records/2026-08-22_THE_SEVEN_MILLENNIUM_OBJECTS_ENTERED_THE_LEAN_BOUNDARY_AND_THE_PARALLEL_SQUEEZE_WAS_TYPED.md`.

[historical] The torus, knot, curved-arc, dimensional, and external knot-formalization audits are
recorded in
`research/records/2026-08-24_THE_ADDRESSED_INSTANCE_LADDER_RETURNED_GEOMETRIC_TORI_CURVED_ARCS_AND_AN_ELEVEN_RANK_QUOTIENT.md`.

[historical] The coupled-LC and complex-parametron source audit is recorded in
`research/records/2026-08-24_THE_COMPLEX_PARAMETRON_IS_AN_ORIENTED_COUPLED_LC_LATTICE_BEFORE_PHASE_LOCKING.md`.

[historical] The candidate solution conditions, recurrence-atlas extension, and matching-logic
localization audit are recorded in
`research/records/2026-08-24_THE_MILLENNIUM_SOLUTION_CONDITIONS_ARE_RECEIVER_FACTORIZATIONS_THROUGH_THE_HOLONIC_STAIRCASE.md`.

[historical] The active official-receiver goal, its admissible deed return, and its evidence-driven
pivot law are deposited in
`research/records/2026-08-24_THE_MILLENNIUM_GOAL_CLOSES_ONE_OFFICIAL_RECEIVER_AND_PIVOTS_ONLY_THROUGH_RETURNED_EDGES.md`.
