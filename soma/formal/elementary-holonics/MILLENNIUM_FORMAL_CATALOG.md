# Millennium formal catalog

> **ARCHIVE BANNER — 2026-08-28 RESEARCH-STATION SNAPSHOT.** This catalog preserves the measured
> theorem inventory and open mathematical fibres of that date. It is not a current build report,
> roadmap, or construction authority; every “next”, “current”, and “present” below is historical
> testimony. The sole schedule is `blueprint/THE_ROADMAP.md`. The production Lean face is
> `ElementaryHolonics.Computation.HolonicMachineLearning`; the broader `ElementaryHolonics`
> research umbrella retains independent Lean 4.33 compatibility work outside the production gate.

**Date:** 2026-08-28
**Scope:** exterior Lean theorem station under `ElementaryHolonics`; this document schedules no
Rust/CUDA construction and does not alter `CONSTRUCTION_STATE.md`.
**Catalog owner:** `soma/formal/elementary-holonics/MILLENNIUM_FORMAL_CATALOG.md`
**Snapshot research import face:** `ElementaryHolonics.lean`

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

[established-bounded; measured] On the 2026-08-28 dependency audit, the station contains:

| Receiver | Returned count |
|---|---:|
| Lean modules below `ElementaryHolonics/` | 687 |
| theorem or lemma declarations | 8,921 |
| theorem, lemma, definition, abbreviation, structure, class, or inductive declarations | 13,491 |
| modules below `ElementaryHolonics/Millennium/` | 624 |
| theorem or lemma declarations below `Millennium/` | 8,189 |
| broad declarations below `Millennium/` | 12,340 |
| explicit `#print axioms` audit commands below `Millennium/` | 3,277 |

[established-bounded; measured] The principal module bands are 24 Foundation modules, 2 Algorithm
modules, 8 Geometry modules, 9 Mathematics modules, 20 dedicated RH modules, and 614 Millennium
modules.  Search prefixes inside the Millennium band include 222 `NavierStokes*`, 117 `Family*`,
67 `Hodge*`, 38 `Holonic*`, 15 `General*`, 10 `Five*`, and 6 `Hilbert*` modules.  These prefixes
overlap thematic work and are not a partition of the library.

[established-bounded; measured] The root umbrella directly imports 616 modules and its recursive
closure reaches 673 of the 674 library modules.  The two substantive umbrella orphans are
`FamilyTunnellHeckeCorrespondence.lean` and `HolonicCosmologicalInference.lean`; the former lies on
the shortest BSD Hecke-intertwining path and therefore requires a mathematical consumer rather
than a barrel-only import.

[counterexample; computational-witness] The present aggregate checkout is not globally green:
`lake build` returns thirteen failing targets (seven Navier--Stokes, five BSD/family, and
`Mathematics/JacobiFiniteDiagonalBridge.lean`).  Isolated elaboration still returns the principal
foundation and official-pose owners used below, but no current claim may cite the aggregate build
as a station-wide proof receipt until those failures are repaired and the `sorryAx` emissions in
the failing targets are removed.

[definition] The reproducible inventory receiver is:

```bash
rg --files ElementaryHolonics -g '*.lean' | wc -l
rg -n '^\s*(theorem|lemma)\s+' ElementaryHolonics -g '*.lean' | wc -l
rg -n '^\s*(theorem|lemma|def|abbrev|structure|class|inductive)\s+' \
  ElementaryHolonics -g '*.lean' | wc -l
rg --files ElementaryHolonics/Millennium -g '*.lean' | wc -l
rg -n '^\s*(theorem|lemma)\s+' ElementaryHolonics/Millennium -g '*.lean' | wc -l
rg -n '^\s*(theorem|lemma|def|abbrev|structure|class|inductive)\s+' \
  ElementaryHolonics/Millennium -g '*.lean' | wc -l
rg -n '^#print axioms' ElementaryHolonics/Millennium -g '*.lean' | wc -l
```

[definition] Counts establish the size of the source population only.  A declaration count is not
a theorem-strength metric, and an axiom-audit command is not itself proof that every declaration in
the library has the same dependency boundary.  The per-worktrack rows below name the mathematical
returns that matter.

## 3. Shared holonic theorem surface

| Grade | Owner | External substrate | Project-specific checked return | Exact boundary |
|---|---|---|---|---|
| `proved-derived; formal-checked` with one `counterexample; formal-checked` control | `Foundation/BoundaryScalePassage.lean`; `Millennium/HolonicBoundaryCycleReflection.lean` | additive chain groups, two consecutive boundary maps, exact scale-naturality squares | a lawful compression passage carries cycles to cycles and boundaries to boundaries; reflecting a coarse filler to a chosen fine predecessor returns the exact retained seam `fineBoundary(fineFiller) - sourceCycle` in the middle transport kernel; source boundaryhood is equivalent to seam nullity, and injective middle transport reflects coarse boundaryhood; an explicit rational passage erases a nonzero fine seam at the coarse receiver | every application owes its actual chain complex, scale maps, source filler or obstruction, and either the complete kernel fibre or a proved faithfulness law; coarse cycle nullity alone cannot close Hodge, fluid, gauge, or arithmetic reconstruction |
| `proved-derived; formal-checked` | `Foundation/FractalPacking.lean`; `Millennium/HolonicPlatonicDiffraction.lean` | exact rational intervals, ordered binary words, finite cyclic sums, complex roots of unity | every restriction word returns a nested rational cell of exact width `3⁻ⁿ`; polarized children share one coarse parent while retaining strict geometric separation and chronology; the five Platonic face/order populations return the exact `32,96,64,160,384` hyper-lift ledger; complete cyclic phase incidence cancels, while cutting one addressed aperture returns the negative missing ray and reopens the zero | construct source metric embeddings, actual polyhedral vertex/weight/reciprocal-covector receivers, a continuum or limit-set theorem, and the source-specific restriction square consumed by an official receiver |
| `proved-derived; formal-checked` | `Foundation/ProductDegreeTwo.lean` | simplicial boundaries over a commutative coefficient ring, exact degree-zero/degree-one contractions, generic factor currents | packages the low-degree factor data required by a binary product decomposition; constructs the `0×2`, `1×1`, and `2×0` axes, and gives an exact polarized filling of the middle product boundary | instantiate the datum for genuine singular sphere chains and close the coupled outer-axis residual; the present middle filler assumes its paired edge inputs are individually closed and does not yet prove arbitrary sphere-power ruling-map surjectivity |
| `proved-derived; formal-checked` | `Foundation/Lineage.lean`, `AddressedBoundary.lean`, `ComparisonCell.lean` | additive algebra, pullbacks, quotients | addressed passages retain occurrence populations, boundary lineage, joined cancellation, and parallel-route defects | the full swing/connection/holonomy/receiver composition remains ordered by the active exterior blueprint |
| `proved-derived; formal-checked` | `Foundation/Holon.lean`; `Millennium/HolonicTerminalCurrent.lean`; `Millennium/HodgeTriangleHomotopyPrism.lean`; `Millennium/NavierStokesEnstrophyTerminalCurrent.lean` | dependent occurrence types, pullbacks, finite sums, additive boundary maps, singular-chain prisms, exact interval currents | one generic holon retains addressed source/target maps and an arbitrary receiver face; serial interaction retains its exact pullback join; Cartesian, diagonal, and proof-carrying off-diagonal occurrence bodies remain distinct; paired Cartesian receiver fibres reconstruct exactly; every finite boundary holon promotes its local constitutive law to the global outgoing-minus-incoming ledger; the refined Hodge triangle population instantiates this carrier and its finite upper receiver is exactly the existing refined-cycle point current; arbitrary receiver-valued interval populations instantiate the same carrier; periodic enstrophy attaches its exact viscous/exterior constitutive law to that returned interval face | Cartesian population is not an apparatus-independence theorem; Hodge still owes the raw-singular-to-normalized homological return, Navier--Stokes still owes terminal current control, and the official smooth-projective Hodge carrier remains open |
| `proved-derived; formal-checked` with one `counterexample; formal-checked` control | `Millennium/HolonicComposition.lean` | group actions, equivalences, additive groups, addressed comparison cells | two complete addressed routes return curvature `T_right*T_left⁻¹`, which is flat exactly when their transports agree; exact chart rebase conjugates the return; a possibly noninvertible `RouteScalePassage` carries it through every receiver intertwining both routes; injectivity reflects flatness, surjectivity descends it, and bijectivity makes it invariant; additive connection words translate by their exact increment sum; the Boolean-to-unit control proves a coarse receiver can erase nontrivial curvature | every source still owes the actual route cell and connection, every scale passage owes both naturality laws, and a nonseparating receiver cannot reconstruct fine/global flatness without its retained fibre or a stronger source theorem |
| `proved-derived; formal-checked` | `Millennium/Swing.lean`, `SwingBridges.lean`, `HolonicDifferenceCalculus.lean` | additive groups, projective ratios, complex exponential | swing reverses an anchored difference; additive receivers commute with iterated differences; finite integration telescopes to the exterior boundary | individual instance bridges do not identify every physical transport with an affine swing |
| `proved-derived; formal-checked` | `Millennium/HolonicDirectedPassage.lean` | additive groups, arbitrary filters, Cauchy filters, complete separated uniform spaces | an arbitrary addressed current returns an exact finite ledger `local population = exterior current + composition defects`; a closed-path return is exactly the accumulated defect ledger; state-induced currents are defect-free; additive receiver maps commute with the local population and every defect; filter-directed null currents reconstruct one unique return and survive cofinal reindexing, paired receivers, and uniformly continuous chart changes | every source still owes its occurrence type, directed filter, constitutive local current, complete receiver, and proof that the required defect/current enters the reconstructible fibre |
| `proved-derived; formal-checked` | `Millennium/HolonicTerminalCurrent.lean` | complete uniform spaces, Cauchy filters, exact finite telescoping, `BoundaryHolon` | an oriented interval current reverses by negation, every occurrence population is an elementary boundary holon, every finite addressed population returns its exterior difference, terminal nullity is exactly eventual vanishing of pairwise receiver currents, and in a complete separated receiver it reconstructs one unique incoming terminal trace | each source theory must prove that its actual constituted current enters this null cone; periodic enstrophy now supplies one such local attachment but not the uniform terminal control |
| `proved-derived; formal-checked` | `Millennium/HolonicSnellInteraction.lean` | Euler phase and exact real/complex trigonometry | Euler turns compose multiplicatively; paired normal/tangential receivers reconstruct the weighted complex phase exactly; Snell compatibility is zero tangential interface current; every finite path in a compatible multiway graph preserves that receiver; an explicit half-turn keeps zero tangential current while returning a nonzero normal remainder | positivity, material refraction, interface calibration, and selection among the retained outgoing phase fibre require source-specific constitutive and apparatus laws |
| `proved-derived; formal-checked` | `Foundation/MeasuredDifferenceReceiver.lean` | normed additive groups and `Real.exp` from Mathlib | a receiver scalar factors through an addressed chart difference; even readings retain a two-orientation fibre; ratios ignore chart-zero shifts; binary normalized exponentials factor through one potential difference | injectivity and physical constitutive laws require their own hypotheses |
| `proved-derived; formal-checked` | `Foundation/PrimeValuationRadixAtlas.lean`, `Millennium/PrimeRadixAtlas.lean` | unique factorization of naturals and Mathlib's `Nat.factorization` | the complete prime-valuation face reconstructs every nonzero population; an exact radix chart returns a unique maximal depth and terminal residual; all prime coordinates balance; equal-depth additive valuation caustics transport through common scale | radix notation never licenses rounding, and the atlas does not turn an unproved analytic bound into a theorem |
| `proved-derived; formal-checked` | `Foundation/TransportLift.lean`, `ReceiverQuotient.lean`, `ExactPartition.lean`, `LatticeTransport.lean`; `Geometry/DivisorAtlas.lean`; `Millennium/ValuationDivisorLatticeAtlas.lean` | additive kernels and quotients, integer modules, finitely supported functions, unique factorization | a general transport request returns an empty/singleton/kernel-coset fibre; partitions reconstruct as dependent sums with paired oriented boundaries; scalar divisibility is isolated as a multiplication lift; signed codimension-one ledgers turn inversion into negation and ratios into differences; Cartier transitions glue local ledgers; lattice maps return kernel, image, cokernel, finite index, torsion witnesses, and saturation | every specialization still owes its geometric locus, chart cover, constitutive transport, and official local-to-global theorem; no scalar factorization is promoted to a source-holon product |
| `proved-derived; formal-checked` | `Millennium/HolonicParametron.lean`, `HolonicComplexParametron.lean`, `HolonicMeasuredParametron.lean` | exact real/complex algebra, finite sums, trigonometric identities | the two locked phase sheets, oriented incidence, diagonal and mutual storage, generalized coupled-LC modes, and measured `ΔQ/ΔV`, `ΔI/ΔΦ`, `ΔV/ΔI`, `Δθ/Δt` coefficient fields compose; coordinated branch reorientation preserves the mode; the logarithmic winding holon proves all integer branches collapse to the same `i` exponential face while its reconstruction fibre is exactly `ℤ`, and multiplication by `i` reopens the exact family `exp(-π/2-2πn)`; branch, full branch-pair, same-branch diagonal, and proof-carrying ordered off-diagonal Parametron holons retain their distinct occurrence populations, and the full mutual current partitions exactly into diagonal plus off-diagonal contributions | the branch-resolved theorem is not a hardware calibration; damping, passivity, Floquet theory, material constitution, and continuum realization remain outside these theorems |
| `proved-derived; formal-checked` | `HolonicTorusFlow.lean`, `HolonicTorusKnots.lean`, `HolonicUnknotting.lean` | Mathlib paths, tori, gcd/prime facts, racks and quandles | Fourier receiver passages, triad boundary closure, multiplier/interactor route defects, coprime torus-slope embeddings, rack swing cancellation, irreducible factor law, and finite phase-collapse counterexamples | no ambient three-manifold torus-knot owner, Reidemeister quotient, or complete unknot fibre exists yet |
| `proved-derived; formal-checked` | `Millennium/Turn.lean`, `HolonicPolygonalTorusCarrier.lean` | exact finite sums, integer `Finsupp` chains, cyclic finite equivalences, and Mathlib's Euclidean-circle constant | a typed arc partition integrates circumference before a radial receiver forms half/full turns; `π` is recovered only from an explicit Euclidean-circle law, while a four-unit-arc calibration proves the law is not automatic; the finite polygonal solid-torus complex returns oriented cells through dimension three, `∂₁∂₂ = 0`, `∂₂∂₃ = 0`, closed longitude/meridian cycles, a cross-section disk whose boundary is the meridian, and a dual cut proving the longitude is not a two-boundary; typed chart zeros agree only through a declared rebase and an equal-zero receiver need not reconstruct its occurrence | no geometric realization or homeomorphism to `S¹ × D²`, complete homology computation, material constitution, or continuum reconstruction is asserted |
| `proved-derived; formal-checked` | `Millennium/HolonicTorusParametronRealization.lean` | the finite torus cellular boundary, the existing Complex Parametron incidence/drive algebra, and the common transport-lift reconstruction theorem | cell vertices realize Parametron nodes, oriented edges realize branches, and the signed integer boundary realizes the real incidence matrix; each branch drop is terminal minus initial potential; integer chain drives embed injectively; discrete integration by parts identifies drive action with the chain-boundary pairing; exact cross-section current and winding flux-linkage receivers return their full kernels and kernel-translate reconstruction fibres; exact drops vanish on closed windings; a nonzero meridian is proved invisible to the current cut and separated by one additional branch probe; branch reorientation transports through the existing sign action | the rank-four winding realization and proof that its induced current/flux square is the abstract monodromy pairing, material constitutive forms and radicals, continuum reconstruction, and hardware realization remain open |
| `proved-derived; formal-checked` | `Millennium/HolonicTorusMonodromyReceiver.lean` | the rank-four integral lattice and primal/dual matrices in `Geometry/SixSphereMonodromy.lean`, integer dot products, additive equivalences, and transport-lift reconstruction fibres | inverse-transpose probe transport exactly cancels primal cycle transport; the order-three, order-four, and unipotent monodromies preserve the receiver; every monodromy carries the complete fixed-value reconstruction fibre by an explicit equivalence | this is the abstract receiver square; its faithful finite carrier and Parametron realization now reside in the subsequent four-torus owners, while smooth/complex realization and material constitution remain open |
| `counterexample; proved-derived; formal-checked` | `Millennium/HolonicRankFourWindingRealization.lean` | two addressed copies of the finite polygonal solid-torus carrier, the paired current/branch receiver, and the rank-four monodromy pairing | four integral chain coefficients embed injectively and their real current/flux pairing is monodromy covariant, but the second and fourth generators are meridians which bound cross-section disks while the first and third longitudes do not; the explicit receiver-insufficiency witness proves that chain rank four does not imply homology rank four | the doubled carrier is rejected as a complex-two-torus realization and retained as the regression guard |
| `proved-derived; formal-checked` | `Millennium/HolonicFourTorusCarrier.lean` | finite products of cyclic axes, integer cellular chains, square commutator faces, dual cochains, and the rank-four monodromy pairing | four axis swings generate a finite cubical two-skeleton with `∂₁∂₂ = 0`; every axis winding closes and is not a two-boundary; four dual cuts reconstruct every lattice coefficient; the exact current pairing commutes with order-three, order-four, and unipotent monodromy | smooth/complex realization as `ℂ² / Λ`, complete higher-dimensional cell structure and homology, material constitution, and continuum reconstruction remain open |
| `proved-derived; formal-checked` | `Millennium/HolonicFourTorusParametronRealization.lean` | the faithful finite four-torus carrier and existing Complex Parametron incidence/drive algebra | vertices and axis edges realize nodes and branches; branch drop is terminal minus initial potential; integer currents embed injectively; discrete integration by parts and closed-current/exact-drop cancellation hold; four real cut currents reconstruct the period lattice; their pairing commutes with all three special monodromies | cell-derived capacitance/inverse-inductance/coupling/loss forms, their radicals and positive quotients, material interfaces, continuum reconstruction, and hardware realization remain open |
| `proved-derived; formal-checked` | `Millennium/HolonicTorusEntropyParametronEquivalence.lean` | the faithful four-torus winding lattice, its Complex Parametron branch-current realization, the four cut receivers, and the alternating cycle interaction | identifies the realized Parametron current image exactly with integral winding data; reconstructs all four winding coefficients from the branch current; proves the Parametron current interaction is the real cast of the lattice wedge; and proves, for a nonzero reference current, that all six interaction planes vanish exactly when the second rational current lies on the same line | the equivalence is deliberately restricted to realized winding currents; arbitrary branch currents, material constitutive response, continuum realization, and source-specific scale laws retain larger fibres |
| `proved-derived; formal-checked` | `Millennium/HolonicDiscreteInduction.lean` | the faithful finite four-torus faces and incidence, exact telescoping, Complex Parametron branch transport, and the geometric complex-two-torus period owner | one addressed time--face grain satisfies finite Faraday/Stokes exactly; exact nodal drops have zero curl and nonzero flux change cannot be a global scalar drop; equal induced curls retain a curl-free reconstruction fibre; histories telescope without approximation; each oriented face boundary supplies an exact source-free local eddy-loop grain; local current divergence returns the charge/source ledger and cancels globally; a conductive response is separated from the nonzero closed-current eddy cut; the four chain coordinates are the `(γ̂,û,ŵ,δ̂)` period translations `(6μ,β)`, `(τ,μ)`, `(1,0)`, `(0,1)` with invariant dual-lattice bivector pairings; general four-axis mutual induction `-Δ(MI)` is covariant under winding reorientation | physical calibration of the returned geometric Hodge, exact permeability/conductivity/coupling laws, primal/dual bulk-conductor realization, addressed air-gap/cut ports, flux-quantized Josephson specialization, and source-specific continuum/scale reconstruction remain open |
| `proved-derived; formal-checked` | `Millennium/HolonicEntropyActionInduction.lean` | additive successor currents, the existing exact Faraday history, finite sums, ordered rings, the integral four-torus/exterior-square carrier, alternating bilinear forms, and typed additive quantity lines | a one-grain successor law promotes by structural induction to every finite successor word; Faraday induction inhabits that carrier exactly; entropy storage plus outward flux equals interior production and telescopes over the world-tube; closed nonnegative production implies monotonicity; strict constitutive order makes positive production equivalent to a nonzero returned difference; a four-axis inverse-temperature derivative splits into symmetric stretch and antisymmetric turn; two four-axis currents return the existing six-plane wedge, reverse under orientation exchange, transport naturally under every common integral chart change through `Lambda^2`, and retain a proved nontrivial zero-cross fibre; skew circulation separates from positive dissipation; physical free energy is the typed difference `E-Theta(S)` and descends for a closed dissipative grain; equal entropy coordinates with separated successors prove that continuation cannot factor through the scalar entropy receiver | every source still owes its actual entropy/current/action map, boundary and constitutive hypotheses; the theorem does not equate physical and variational free energy, infer a stochastic microscopic governor, instantiate the material Hodge/force sectors, or close an official Millennium receiver |
| `proved-derived; formal-checked` | `Millennium/HolonicPortResolvedBoundaryTransport.lean` | finite exact current balances, finite sums, ordered receivers, and explicit boundary-port addressing | refines one exterior flux into a finite port ledger without losing the telescope; proves every zero-input returned port lies in the total receiver kernel; identifies received storage change with received input when the returned boundary lies in that kernel; proves that a zero sum of nonnegative received port currents forces every port current to vanish; and gives an exact antitone storage law under zero input and nonnegative outward return | each physical instance still owes its port population, source map, constitutive signs/order, chronology, and scale passage; the ocular specialization names optical-energy ports only and does not identify thermal deposition or neural signal with a second copy of optical energy |
| `proved-derived; formal-checked` | `Millennium/HolonicSlingTransport.lean` | Swing, additive successor currents, addressed ordered words, receiver descent, exact inner-product algebra, and finite reconstruction fibres | defines a sling as a released Swing whose source decomposes exactly into impulse plus medium return; proves receiver-kernel negligibility and serial impulse accumulation; computes the affine Swing impulse as twice the anchored difference; retains the full released-medium word lineage; characterizes a deterministic Markov quotient exactly by stability of every receiver fibre under every source successor; and proves the moving-pivot gravity-assist squared-speed identity without approximation | one frozen affine Swing is a point reflection, so general physical deflection still requires an ordered connection/holonomy or a source isometry; each projectile, atmosphere, optical cavity, or orbital instance owes its constitutive medium law, release/capture boundary, admissible receiver, and continuum/scale reconstruction |
| `proved-derived; formal-checked` | `Millennium/HolonicRankFourInteractionPlanes.lean` | the rank-four period lattice and complex period embedding from the `S⁶` torus-family owners, finite exterior-plane enumeration, and exact integer matrix algebra | `ℤ³ × ℤ` is additively equivalent to `ℤ⁴`; the four ordered period directions have exactly six distinct interaction planes and a chosen `3 + 1` receiver partitions them into three spatial plus three space--time planes; the source forms read `Q₀(γ,δ)=1`, `Q₀(u,w)=6`, `η(γ̂,δ̂)=6`, `η(û,ŵ)=1`; the left period block has determinant `6μ²-τβ`; every winding population has its exact `ℂ²` displacement; the period map is injective under the source nondegeneracy hypotheses | the metric/material Hodge response, physical force-sector realizations, Lorentz-covariant indexed-mass receiver, physical flux-period integrality, and scale/global reconstruction remain open |
| `proved-derived; formal-checked` | `Millennium/HolonicMaxwellPropagation.lean` | the six interaction-plane carrier, the existing first/second returned-difference calculus, exact real linear maps, positive square-root algebra, and the rank-four period embedding | one external successor difference along the declared lattice chronology is exactly one internal `δ̂` period cycle with universal-cover displacement `(0,1)`; the six face coordinates are linearly equivalent to an oriented electric/magnetic `3 + 3` split; typed primal/dual curl maps satisfying discrete Faraday and Ampere--Maxwell yield exact electric and magnetic second-difference curl--curl laws with `c²=(με)⁻¹` and positive `c=sqrt((με)⁻¹)`; the algebraic square of the defined rest-energy face is `(m*c²)²=m²*c⁴`; every field receiver fold intertwining both curl maps preserves both wave laws and their `c²` coefficient | construct the field-dynamics naturality square relating external successor to `δ̂` transport (or restrict to three spatial axes with external `ℕ` time); attach physical calibration, Lorentz mass-shell structure, source/Gauss laws, addressed cut/interface traces, and continuum characteristic-cone reconstruction |
| `proved-derived; formal-checked` | `Millennium/HolonicDiscreteMaxwellOperator.lean` | the faithful four-torus face boundary, addressed connection/additive-translation owner, typed quantity occurrences, exact positive rational primal edge/dual three-cell and primal/dual face measures, finite real pairings, the standing current-balance owner, and the exact Maxwell propagation owner | the four signed increments of every addressed face have holonomy equal to cellular curl; the positive geometric ratios `|dual edge|/|primal edge|` and `|dual face|/|primal face|` construct the existing Hodge datum while retaining distinct primal/dual origins; its co-curl is `M₁⁻¹BᵀM₂`, both metric radicals are trivial, and both curl--curl actions are passive; exact midpoint polarization returns `ΔEnergy + boundaryPower + sourceWork = 0`, where boundary power is precisely the curl/co-curl adjoint defect; the history factors through `CurrentBalance`, telescopes, descends under nonnegative outward power/work, and conserves energy for a closed source-free material co-curl; a scale passage preserving curl, co-curl, and both complete Hodge pairings preserves energy and composes; positivity forces both transports injective, and the concrete zero edge receiver is proved unable to support such a passage | exact cell measures remain admitted source geometry, not a calibrated conductor/core model; derive anisotropic permeability, conductivity, capacity, loss, and coupling as typed material maps; resolve the adjoint defect through actual cut/interface ports; instantiate a source-specific directed scale family, the three-space/Gauss sector, and continuum reconstruction |
| `proved-derived; formal-checked` | `Millennium/HolonicTypedOriginDimensions.lean` | the common transport-lift reconstruction theorem and the prior conventional `(length,mass,time)` dimension receiver | source and receiver time factors remain distinct before an exact additive receiver sums their exponents; both speed factors return the conventional speed dimension while their nonzero origin difference lies in the receiver kernel; `c²`, force, stress--energy, `G/c⁴`, curvature, and `Λ` compose with exact typed dimensions; the Einstein source and cosmological term both return curvature type; primal edge, dual edge-cell, primal face, and dual face measures have exact `L`, `L³`, `L²`, `L²` types, so the four-dimensional geometric edge and face Hodge ratios return `L²` and the dimensionless line; common rebasing preserves differences; tensor self-product survives while self-wedge vanishes | attach typed material-response and calibration lines to the geometric Hodge construction, mass, and Einstein carriers; construct unit/chart transports and preserve every origin fibre through source-specific continuum reconstruction |
| `proved-derived; formal-checked` | `Millennium/HolonicFourForceSectorCarrier.lean` | the rank-four period lattice, exact exterior-square transport, addressed four-axis cell carrier, and common two-route connection return | constructs the alternating cycle interaction `x_i y_j - x_j y_i`; proves it is alternating and natural under every integral rank-four transport; identifies the plane names with the six exterior coordinates; installs electromagnetic, weak, strong, and gravity as dependent internal fibre families over one base-dependent edge connection; every square retains its two joined edge routes, their targets commute by the swing cell, and sector curvature is exactly the common addressed return, hence is flat exactly when the two complete route transports agree; reversed routes invert it | instantiate physical `U(1)`, chiral electroweak/Higgs, `SU(3)`, and frame/Spin fibres with their representations, matter, actions, Hodge/constitutive laws, anomaly/quotient data, calibration, continuum passage, and source-specific mass receivers |

[proved-derived; formal-checked] The new scalar correction is a composition law, not a slogan:
`DifferenceReceiver` stores the chart and the reading separately; `returnedDifference` precedes
`face`; `reconstructionFiber` retains every addressed pair returning one scalar.  The binary
exponential theorem proves

```text
exp(y) / (exp(x) + exp(y)) = exp(y-x) / (1 + exp(y-x)),
```

so the common potential is an exact null direction of that receiver.

### 3.1 The shared directed-passage target across the official worktracks

[definition] The table below is a source-allocation blueprint for the checked carrier in
`HolonicDirectedPassage.lean`.  It does not assert that the listed nullity or constitutive laws
already hold.

| Worktrack | Directed occurrences/course | Receiver current or returned defect | Exact closure condition |
|---|---|---|---|
| Riemann hypothesis | admissible contour and test-function refinements, directed cofinally | explicit-formula boundary return together with the Weil quadratic-form receiver | the boundary current is null, the reconstructed form is nonnegative on the admitted family, and the existing Weil receiver puts every nontrivial zero on the seam |
| Birch--Swinnerton-Dyer | prime localization, descent, height, and model-refinement passages | the paired algebraic-rank and analytic-order state, followed by the leading-coefficient ledger | the discrete rank pair is eventually identical and the complete arithmetic/analytic ledger reconstructs with zero defect for every official elliptic curve |
| Hodge conjecture | chart-cover, cycle, and cohomology refinement | the class in `H² / algebraicSpan`, with every overlap composition defect retained | the reconstructed quotient class is zero for every rational Hodge class on every admitted smooth projective carrier |
| Navier--Stokes | the incoming finite-time filter and spatial/scale refinement filters | the high-order state together with signed stretching, dissipation, and forcing currents | the source-specific current is null in a continuation-complete receiver and the reconstructed trace satisfies the PDE compatibility/restart law |
| Yang--Mills and mass gap | lattice spacing, volume, gauge, and continuum reconstruction refinements | gauge-invariant state transport plus the vacuum-quotient spectral separator | the continuum current reconstructs while one exact positive lower separator is uniform over the complete scaling course |
| P versus NP | addressed computation/reduction passages ordered by instance families and resource aperture | successor/interchange defects together with a receiver separating accepting witnesses from bounded deterministic realization | either a uniform polynomial realization is constructed or a receiver-insufficiency/lower-bound separator survives every admitted polynomial passage |
| Poincaré theorem | triangulation, surgery, and chart-refinement passages | loop return and gluing defects in the simply-connected closed-three-manifold carrier | this row is a transport target for the already solved theorem, not an unsolved official obligation |

[open] The shared law removes repeated filter, telescoping, and reconstruction work.  It does not
make source currents null.  The scientifically decisive deed in each unsolved row is therefore a
source-owned constitutive or uniform-scale theorem that enters the checked common carrier without
discarding its reconstruction fibre.

### 3.2 The entropy/action/induction successor carrier

[proved-derived; formal-checked] `HolonicEntropyActionInduction.lean` closes the common finite
successor-current edge.  From the local returned-difference law
`coordinate(successor x)-coordinate(x)=source(x)`, structural induction reconstructs the exterior
difference as the exact sum of every addressed local source.  The existing Faraday history is an
inhabited source realization with flux as coordinate and negative face circulation as source.

[proved-derived; formal-checked] The same owner separates three facts which had previously been
compressed into the word entropy: the exact storage/side-flux/interior-production balance, the
nonnegative material production premise, and the receiver reading of stored entropy.  Closed-system
monotonicity follows only after the side flux is zero and production is nonnegative.  A source pair
with equal entropy readings and different successors proves that a scalar entropy quotient cannot
govern microscopic continuation in general.

[proved-derived; formal-checked] The owner also supplies the constitutive algebra needed downstream:
the inverse-temperature derivative splits into symmetric stretch and antisymmetric turn; a monotone
response pairs with an oriented occurrence difference to produce a nonnegative interaction grain;
under a strictly monotone constitution that grain is zero exactly at zero returned difference and
is strictly positive exactly when a difference remains; two four-torus winding currents return the
alternating face current `J_i K_j - J_j K_i`, which reverses under either orientation swap and
vanishes on aligned currents while retaining an explicitly nontrivial zero-cross reconstruction
fibre;
an alternating turn self-pairs to zero while positive dissipation remains; and physical free energy
is typed as `E-Theta(S)` for an explicit additive entropy-to-energy map.  The complete source audit
and its falsifiers are deposited in
`research/records/2026-08-26_ENTROPY_IS_A_TYPED_INTERIOR_TURN_CURRENT_FREE_ENERGY_IS_A_CONSTITUTIVE_DIFFERENCE_AND_INDUCTION_PROMOTES_A_LOCAL_LAW.md`.

[proved-derived; formal-checked] The same owner now proves the receiver-relative strengthening.
If an additive receiver kills the complete boundary current, received storage difference is
exactly received production; nonnegative received grains imply monotonicity, and a null total is
equivalent to every received local grain being null.  For the torus interaction, a nonzero plane
cross-current rules out alignment on that plane, while over a field and away from the zero
reference current, all six plane currents vanish exactly when one scalar reconstructs the second
four-current from the first.  The returned cross-current also obeys an exact discrete Leibniz law
when both currents change.  These results formalize conditional entropy increase and aligned
cross-entropy nullity without deleting the zero fibre.

[open] This removes another generic telescoping target from all six worktracks.  Their shortest
remaining edge is source realization: construct the actual source successor, storage/current/
production map, positive or coercive constitutive form, and official receiver square.  Repeating
the abstract successor theorem at finer scales no longer advances the catalog.

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

[established-bounded; measured] The 2026-08-27 exact eta campaign constructs rational interval
enclosures on all 988 unit-height bands from 12 through 1000, derives rather than authors the
Euler--Maclaurin start from the receiver box and grain, and returns 649 reflection-symmetric
winding-one closures.  The 2026-08-28 exact tide campaign returns 989 rational intervals with
`max |S(T)| ≤ 970/1000`; its derivative atlas returns zero left-half winding in every audited band
and 539 right-half saddles.  These receipts are source-specific bounded evidence over the eta/xi
atlas; they are not a cofinal contour theorem and do not inhabit `RiemannHypothesis`.

[open] Those bounded returns sharpen the global RH defect to three named edges: construct the
source-specific explicit-formula pairing on an admitted cofinal test-function family; realize its
Weil form rather than postulating a `sourceObligation`; and prove that form nonnegative with no
off-seam null direction.  Another finite zero census, symmetry restatement, or tide aperture leaves
all three edges unchanged.

## 5. Birch--Swinnerton-Dyer

| Grade | Layer | Principal owners and returns | Provenance | Open fibre |
|---|---|---|---|---|
| `definition` | official pose | `BirchSwinnertonDyer.lean`, `UniversalBSD.lean`, `UniversalBSDLedger.lean`: point-count coefficients, analytic data, rank predicates, height/regulator data, rank and leading-coefficient clauses for the family and arbitrary integral models | local pose using Mathlib Weierstrass curves, `LSeries`, analytic order, Gamma, integration, and matrices | the universal conjecture is not inhabited by a universal proof |
| `proved-derived; formal-checked` | arithmetic family | `Family*`, `Five*`, and `General*`: torsion faces, descent cells, collision/halving laws, height contraction, finite generation on full-two-torsion curves, logarithmic family rank bounds, and prime-modulus rank bounds including `FamilyPrimeRank.theRankIsAtMostFourAtEveryPrimeModulus` | project-specific composition of standard elliptic-curve, finite-group, height, and lattice ingredients | these bounds do not identify analytic rank or the complete BSD ledger |
| `proved-derived; formal-checked` | analytic instance | `HeckeTheta.lean`, `HeckeEuler.lean`, `HeckeWitness.lean`: theta construction, entire completed function, Euler coefficients, complete `LDatum 1`, analytic rank zero, algebraic rank zero, and `theRankClauseHoldsAtOne` | local derivation built from Mathlib analysis/number theory and classical Gaussian/Hecke ingredients | the complete rank-zero leading coefficient at one still requires its ledger identity |
| `proved-derived; formal-checked` | universal instance | `MillenniumInstance.theMillenniumRankClauseIsProvedAtOne` and `theUniversalRankClauseIsSatisfiedSomewhere` | project-specific composition of the family witness with the universal pose | one satisfied curve is not the universal theorem |
| `proved-derived; formal-checked` | prime family analytic/arithmetic gate | `FamilyWaldspurgerGate.lean`, `FamilyThetaWaldspurgerBridge.lean`, `FamilyTunnellThetaCarrier.lean`, `FamilyTunnellShimuraLift.lean`, `FamilyTunnellHeckeIntertwining.lean`, and `FamilyWaldspurgerRealDifference.lean`: canonical signed ternary populations; the complete level-128 Jacobi-theta product with its level-four correction, formal integral `q`-expansion, odd-coefficient projection, and exact coefficient/source fibres; the exact divisor/Jacobi-symbol Shimura coefficient transport; equality with the constructed level-32 Hecke coefficients through the full Sturm aperture `1..8`; an explicitly constructed weight-`3/2` `T(p²)` coefficient operator; exact identification of every prime-power Shimura coefficient with its local character current; and a proof that every half-integral eigen-current returns the ordinary weight-two Euler recurrence at all prime-power depths; plus the real Waldspurger--Tunnell difference whose zero implies the positive-sign prime-family rank clause | local finite census, constructed holomorphic translation-returning Tunnell theta carrier, exact coefficient-level Shimura passage, uniform Shimura--Hecke prime-power intertwining, analytic family theta composition, and exact nonzero-period chart removal | prove the source-specific complete Tunnell theta eigen-current law at every odd prime (via its lattice Hecke correspondence), use the resulting uniform coefficient system to identify the level-32 newform, then prove the Waldspurger norm/period square returning `2L_p(1)/Ω_p-c_p²=0` |
| `proved-derived; formal-checked` | completed Jacobi--Euler, Gauss factor, and exact theta-scale passage | `JacobiFiniteDiagonalBridge.lean`, `FamilyTunnellJacobiEulerCube.lean`, `PowerSeriesExactDilation.lean`, `FamilyTunnellThetaDilation.lean`, and `FamilyTunnellJacobiGaussFactor.lean`: the finite differentiated Jacobi source crosses an explicit diagonal-address bijection, stabilizes coefficientwise to the completed Euler cube, and regrades to the weighted Tunnell orientation current; exact substitution `X ↦ X^k` returns a singleton coefficient fibre at `n/k` or the empty fibre; doubling the complete finite square-root population proves `θ₃(X⁴)=A+C` and `θ₄(X⁴)=A-C`; the positive diagonal reconstructs the Gauss triangular factor; the finite distinct/odd product recurrence completes coefficientwise; its scale-two fixed point is proved to be the unit series by strong induction; and the resulting exact product cancellation proves `B·(A+C)·(A-C)=weightedQuarterSquareTheta 1` and `hopfHeckeThetaCurrent = 8·heckeCoefficientSeries` unconditionally | source-specific finite support, polynomial-to-series commuting squares, exact occurrence bijections, coefficient stabilization, exact dilation, and a well-founded halving return; no analytic limiting estimate or packaged Jacobi derivative theorem | the Hopf factor seam is closed; the surviving prime Brandt source edge is the odd-prime Jacobi four-square/Lambert coefficient identity |
| `proved-derived; formal-checked` | quaternionic Hopf/Jacobi source closure | `FamilyTunnellQuaternionHopf.lean`, the `FamilyTunnellHopf*` and `FamilyTunnellJacobiFourSquare*` chain, `FamilyTunnellJacobiHuardLevelTwoSource.lean`, `FamilyTunnellJacobiHuardCarrierBridges.lean`, `FamilyTunnellJacobiHuardBoundaryEvaluation.lean`, `FamilyTunnellJacobiHuardEvaluation.lean`, and `FamilyTunnellJacobiHuardClosure.lean`: the primitive/imprimitive Hopf fibres, completed Lambert receiver, divisor-convolution reduction, six-term positive-quadruple source, off-diagonal affine cancellation, diagonal boundary bijection, exact boundary evaluation, and unconditional Huard/Jacobi composition are constructed; the terminal return proves every positive four-square shell/divisor law and zero norm-one odd-prime Brandt defect | finite quaternion/Gaussian factorization, exact source fibres, formal differentiation, source-faithful affine reindexing, boundary conservation, exact parity/scale transport, and integer cardinality algebra | the Jacobi source is closed; the remaining prime-family edge is the source-specific Brandt destination classification that propagates the norm-one calibration uniformly in the coefficient address |
| `proved-derived; formal-checked` | actual rank-three two-class Brandt carrier and exact cyclic quotient | `FamilyTunnellBrandtTwoClassInterchange.lean`, `FamilyTunnellBrandtCalibratedInterchange.lean`, `FamilyTunnellBrandtNeighborWorldTube.lean`, `FamilyTunnellBrandtDestinationClassification.lean`, `FamilyTunnellBrandtRelationKernel.lean`, `FamilyTunnellBrandtNeighborQuotient.lean`, `FamilyTunnellBrandtNeighborRankThree.lean`, `FamilyTunnellBrandtNeighborQuadraticQuotient.lean`, `FamilyTunnellBrandtNeighborGram.lean`, `FamilyTunnellBrandtNeighborDiscriminant.lean`, `FamilyTunnellBrandtNeighborCommonIndex.lean`, `FamilyTunnellBrandtDistinctNeighbors.lean`, `FamilyTunnellBrandtGlobalSeparation.lean`, `FamilyTunnellBrandtGenusInvariants.lean`, `FamilyTunnellBrandtMinkowskiBounds.lean`, `FamilyTunnellBrandtDestinationReduction.lean`, `FamilyTunnellBrandtUnitWeights.lean`, and `FamilyTunnellBrandtStabilizerWeights.lean`: weighted two-class interchange and unconditional Jacobi calibration; both actual `p+1` source apertures; explicit additive `ℤ⁴ →+ ℚ³` charts; exact one-generator zero fibres with fourth coordinate `p`; additive equivalences `ℤ⁴/ℤg ≃+ actualNeighbor`; reciprocal exact injections with `ℤ³` proving every actual neighbor finite free of rank three and returning a `Fin 3` basis; an integral positive-definite descended quotient receiver and symmetric bilinear integer full-polar Gram law; exact change-of-coordinates formula `det(actualFullGram)=512·covolume²`, exact integral-to-rational basis closure, absolute covolume one, and unconditional determinant `512`; surjective source-polar and neighbor-fourth-coordinate residue maps, equality of the resulting common core with exact relative index `p` on both sides, and exact injectivity of both projective-direction-to-neighbor maps; the local/global class separator; determinant-64 positive target Gram matrices and determinant-512 full-polar matrices; exact `Q₁` and completed-square `Q₂` bounded-slice reductions; exhaustive eight-element additive integral automorphism groups for both target forms; and abstract weighted interchange | exact projective/integral neighbor construction, polar-kernel normal forms, self-polar and `p²` divisibility, first-isomorphism quotient, reciprocal lattice injections, integral quadratic/full-polar reconstruction, rational coordinate pullback, exact common-index/covolume cancellation, normalized-direction separation, coefficient bounds, exhaustive automorphism fibres, and source-weighted interchange | reduce the retained source-specific local/genus incidence to exactly one of the two target classes, and return reverse-neighbor incidence/population double counting on the ordinary two-class Kneser graph; a quaternion right-order realization is a separate later passage |
| `proved-derived; formal-checked` | collision-free Kneser populations and reverse source-direction fibre | `FamilyTunnellBrandtDistinctNeighbors.lean` and `FamilyTunnellBrandtKneserReverse.lean`: both projective-direction maps are injective; each source returns exactly `p+1` distinct actual neighbors; every population member has a unique normalized source direction and carries equal-index-`p`, determinant-`512`, and covolume-pullback receipts | exact fractional-generator reconstruction, normalized affine/infinity pivots, common-core cancellation, and finite image cardinality | reversal after quotienting by global destination class still requires the Jones--Pall classifier |
| `proved-derived; formal-checked` | actual Jones--Pall packet, local form passage, and rational source-genus transport | `FamilyTunnellBrandtJonesPallReduction.lean` and `FamilyTunnellBrandtLocalizeAtPrime.lean`: every actual quotient carrier is integral, positive definite, nondegenerate, has full-Gram determinant `512`, excludes `Q₃`, and has the same `p`-power saturation as its source; `FamilyTunnellBrandtPadicHensel.lean`, `FamilyTunnellBrandtPadicIsotropicLift.lean`, `FamilyTunnellBrandtLocalReflection.lean`, `FamilyTunnellBrandtPadicHyperbolicPair.lean`, `FamilyTunnellBrandtPadicIntegralRepresentatives.lean`, `FamilyTunnellBrandtPadicPolarKernelBaseChange.lean`, and `FamilyTunnellBrandtPadicCarrierImage.lean`: an exact isotropic lift, integral hyperbolic pair, form-preserving ambient `Q_p` equivalence, reverse kernel base change, and equality between its completed-source image and the actual completed neighbor; `occurrence_jonesPall_local_genus_passage` consumes the equality; `FamilyTunnellBrandtJonesPallNormalForm.lean` now returns the actual determinant-64 half-polar coefficient carrier, exact coordinate/profile equivalences, and `occurrenceRationalGenusTransport`, with denominator `p` or `3p` coprime to `128`, oriented determinant one, and exact Gram pullback | source-specific common-index/covolume determinant, exact Hensel transport, complete polar-form preservation, integral numerator reconstruction, completed carrier-image equality, proper source/companion rebases, and exact rational matrix composition | prove the finite Eisenstein coefficient reconstruction and return a proper integral equivalence to `Q₁` or `Q₂` |
| `receiver-insufficiency-counterexample; formal-checked` | determinant-only Brandt destination receiver | `FamilyTunnellBrandtDestinationReduction.lean`: `Q₃=x²+y²+64z²` is positive definite with half/full determinant `64/512`, has an exact four-point norm-one fibre, and admits no arbitrary receiver equivalence to `Q₁` or `Q₂`; ordered positive diagonal determinant-64 coefficient triples are exactly seven | exact finite coefficient classification and norm-one fibre separation | determinant, rank, integrality, and positivity are insufficient; the destination theorem must retain actual local/genus incidence from the Brandt construction |
| `proved-derived; formal-checked` | exact two-adic Brandt destination receiver | `FamilyTunnellBrandtModFourReceiver.lean`: exact `p²` passages prove complete modulo-four profile equality and exclude `Q₃`; composing two passages proves complete modulo-sixteen source/neighbor profile equality | explicit coordinate transports, integral numerator reconstruction, `p² ≡ 1 (mod 4)`, and `p⁴ ≡ 1 (mod 16)` for odd prime `p` | the depth-four profile leaves exactly the two source-genus reduced classes once the finite Eisenstein reconstruction is proved |
| `proved-derived; formal-checked` | quaternion population separation | `FamilyTunnellAdmissibleOrderUnits.lean` classifies the constructed admissible order's units as exactly `±1,±i`, of cardinality four; `FamilyTunnellBrandtRightOrderBridge.lean` classifies the eight Lipschitz integral norm-one occurrences and exposes the absent action-compatible order/ideal transport | exact norm-square and congruence classification, finite equivalences, and a typed obstruction record | neither population is identified with a quaternion Brandt weight; the current BSD route instead uses the ordinary Kneser graph and equal full-orthogonal class weights |
| `proved-derived; formal-checked` | exact prime/radix face | `PrimeIndex.lean` and `PrimeRadixAtlas.lean`: `17 = P 6`; the maximal binary charts `34 = 2^1*17` and `2 = 2^1*1`; subtracting the normalized branch equations returns `v^2 - 17*u^2 = 1` | project-specific composition of prime indexing, exact factorization, and the existing congruent-seventeen descent | the prime index is an ordering receiver; the arithmetic load is carried by the valuation/residual face, and this normalization alone does not prove the BSD rank or ledger clauses |
| `proved-derived; formal-checked` | measured differences | `MillenniumDifferenceAtlas`: finite rank equality is zero integer difference after finiteness; the rank-zero ledger is zero complex central-value difference | project-specific composition | the rank carrier remains `ℕ∞` until finiteness is supplied, and the ledger zero is still a theorem obligation |

[open] The sharp BSD pressure is two-pronged: close the displayed Waldspurger--Tunnell defect on
the remaining prime family, and construct the universal arithmetic/analytic passages needed beyond
the congruent-number family.  The catalog deliberately keeps the extensive algebraic descent,
the complete witness at one, and the universal conjecture separate so none is forgotten or promoted
into the others.

[proved-derived; formal-checked] The prime-family port is now a single exact real equality rather
than a complex or normalization-valued ambiguity.  `FamilyWaldspurgerRealDifference.lean` proves
that `2L_p(1)/Ω_p-c_p² = 0` is equivalent to the named Waldspurger--Tunnell defect and transports
its zero directly into `TheRankClause` on every prime `p ≡ 3 (mod 8)`.  The next analytic deed must
therefore prove this real theta/period-to-ternary-square identity.  The half-integral source is no
longer only a citation: `FamilyTunnellThetaCarrier.lean` constructs its complete level-128 analytic
Jacobi product, including the level-four correction whose absence is invisible on odd coefficients;
proves unit-translation return, upper-half-plane holomorphy, the formal integral `q`-expansion,
exact source fibres, and the nonzero prime-branch coefficient.  `FamilyTunnellShimuraLift.lean`
then constructs the exact divisor/character coefficient transform and proves that the returned
level-32 coefficients match the existing Hecke witness through the entire Sturm aperture `1..8`.
The next uniform theorem is modularity plus Sturm descent, followed by the norm/period square—not
another coefficient census, complex rephrasing, or floating evaluation.

## 6. Hodge conjecture

| Grade | Layer | Principal owners and returns | Provenance | Open fibre |
|---|---|---|---|---|
| `definition` | official boundary | `HodgeConjecture.Datum`: cycle space, rational cohomology, cycle-class map, rational `(p,p)` submodule, and an explicit `Official` admission predicate | local pose over Mathlib rational modules and submodules | actual smooth projective complex varieties, singular cohomology, Hodge decomposition, and cycle realization |
| `proved-derived; formal-checked` | open population | `theHodgeConjecture_iff_noOpenHodgeClass` | local derivation | emptiness of the open population remains unproved for official realizations |
| `proved-derived; formal-checked` | index geometry | `HodgeIndex.lean`: ample positive direction and negative-definite orthogonal complement in the declared receiver form | project-specific Hilbert-space realization of the signature mechanism | no typed transport currently identifies this model with the intersection form of an admitted variety |
| `proved-derived; formal-checked` | geometric difference | `MillenniumDifferenceAtlas.hodgeQuotientDifference`: a class is sent to `Cohomology / algebraicSpan`; it vanishes exactly on algebraic classes; open Hodge classes are precisely nonzero quotient differences | project-specific composition of the official pose with Mathlib quotient modules | the quotient is intentionally not condensed to a scalar without a separating receiver theorem |
| `proved-derived; formal-checked` | constructive reconstruction and finite gluing | `HodgeConstructivePassage.lean`: the Hodge conclusion is equivalent to inhabiting the complete cycle-class reconstruction fibre for every rational Hodge occurrence; every inhabited fibre is equivalent to the cycle-class kernel; one nonzero algebraic generator closes every rank-one codimension-one carrier; addressed cycles over any finite Hodge basis glue by exact rational coordinates to a global source cycle | project-specific composition of the official pose, common transport-lift owner, finite basis reconstruction, and cycle-class linearity | instantiate the basis cycles on an actual admitted smooth projective carrier; the current theorem constructs the global witness once those source cycles and the official comparison package are present |
| `proved-derived; formal-checked` | universal primitive staircase and algebraic interaction cut | `HodgeConstructivePassage.lean`: `PrimitiveHodgeStep.hodgeConclusion_of_lower_of_primitiveLiftable` reconstructs every upper cycle as primitive source plus transported lower source; `hodgeConclusion_iff_primitiveLiftable_of_lower` proves primitive liftability is the exact new obligation; `primitiveHodgeStaircaseConclusion` propagates it through every finite codimension. `transportedLowerClasses` is the exact range of the lower Hodge current, and `primitive_mem_transportedLowerClasses_iff_eq_zero` proves under the standard transverse primitive splitting that no nonzero primitive occurrence can be manufactured by repeating that current. `PolarizedHodgeReceiver.hodgeConclusion_iff_algebraicallyDetected` identifies the conclusion with nullity of the algebraic orthogonal; `PrimitiveAlgebraicInteraction.primitiveLiftable` derives actual primitive cycle fibres from the law that every nonzero primitive class has nonzero intersection with an algebraic primitive class | exact cycle-class naturality, returned primitive decomposition, finite-dimensional polarized bilinear orthogonality, and source reconstruction fibres | construct the genuine smooth-projective Lefschetz/intersection realization and prove the algebraic primitive detector law; another lower-degree transport, common-star singular filling, rank recoding, or finite census cannot supply the missing algebraic primitive source |
| `proved-derived; formal-checked` | smooth-projective receiver skeleton and irreducible-generator fundamental current | `HodgeSmoothProjectiveReceiver.lean`: a projective presentation is an actual closed immersion into Mathlib `Proj` over `Spec ℂ`; codimension-`p` sources are genuine locally finite integral algebraic cycles at coheight `p`, rationalized by `ℚ ⊗[ℤ] -`; cohomology is the rational dual of genuine singular homology; and the rational `(p,p)` submodule is the kernel of the exact non-middle defect. Projectivity derives compactness, so every locally finite algebraic cycle has finite support. `CodimensionPoint`, `integralCycleGenerator`, `extendCodimensionPointCurrent`, and `rationalizeIntegralCycleCurrent` prove that one current on actual irreducible codimension occurrences extends over every rational cycle; its value on a generator is the original current and its complete range is exactly the rational span of those irreducible currents. The universal analytic interface is one continuous bijective chart into the typed space of closed complex scheme points; projection to the Zariski carrier, pointwise closedness, and the population bijection are derived. `FundamentalClassPoincarePassage` retains complex dimension and, exactly when `p ≤ dimℂ X`, an exact Poincaré isomorphism, then accepts only one Hodge-typed fundamental current per irreducible occurrence and derives the whole cycle current, its ordinary homology face, and `cycleClass`; above dimension the total cycle current is definitionally zero. `cycleClass_range_of_le` identifies the official image with the span of Poincaré-dual irreducible currents, and `conclusionAt_iff_irreducibleCycleClass_span` makes equality of that span with the rational middle Hodge receiver the exact source-determined conclusion. Thus `SourceDeterminedHodgeTheory` stores no arbitrary semantics, independent analytic/Zariski proof family, fake duality map, arbitrary whole-cycle map, independent cycle map, or free `(p,p)` range proof | Mathlib schemes, `Proj`, smooth/proper morphisms, compact locally finite support, typed closed-point incidence, actual generic-point generators, tensor rationalization, singular homology, internal Hodge sums, categorical isomorphisms, submodule spans/preimages, dimension-bounded Poincaré typing, quotient kernels, and the checked primitive passage | construct the continuous bijective analytification-to-closed-point chart, Hodge splitting, exact in-range Poincaré isomorphism, and the closed complex-oriented fundamental current of each irreducible occurrence; instantiate dimension-aligned hard Lefschetz; then prove that the resulting irreducible current span fills every higher primitive rational Hodge receiver |
| `proved-standard; formal-checked` | completed projective-zero Hodge realization | `HodgeProjectiveZeroAmbient.lean`: for the standard grading on `ℂ[X]`, every homogeneous degree-`n` occurrence is one coefficient times `Xⁿ`; the degree-zero ring is exactly `ℂ`; `D₊(X)=⊤`; `Away(X)` is equivalent to the degree-zero ring; `Proj.toSpecZero` is an isomorphism; and the identity closed immersion packages a proper, smooth, nonempty `SmoothProjectiveComplexScheme`.  Its underlying scheme and closed-point population are proved unique; `PUnit` supplies the exact analytic point chart; its singular simplicial set is terminal, giving `H₀≃ℚ` and zero positive even homology; genuine codimension-zero algebraic cycles are `ℤ` and all positive-codimension cycle sources vanish; exact rationalization, the point Hodge splitting, and the fundamental cycle-class equivalence give a complete `HodgeSemantics`, a `Realization`, and `projectiveZeroTheHodgeConjecture` for the nonempty canonical point family | Mathlib homogeneous polynomials/localization, `Proj`, scheme isomorphisms, terminal simplicial sets, normalized singular chains, rational tensor transport, locally finite algebraic cycles, internal Hodge splittings, and the source-indexed official receiver | enlarge the canonical family by constructing the same scheme/analytic/cycle-class passage for positive-dimensional smooth projective sources; the complex point calibration does not discharge universal primitive algebraicity |
| `proved-standard; formal-checked` | genuine positive-dimensional algebraic carrier and continuous analytic closed-point receiver | `HodgeProjectiveSpaceAmbient.lean` constructs the finite standard homogeneous-coordinate ambient uniformly: its degree-zero ring is exactly `ℂ`, the coordinate population generates the complete algebra, the coordinate basic opens cover `Proj`, the structure map is finite type and proper, and the identity closed immersion supplies an actual projective presentation. `HodgeProjectiveLineScheme.lean` specializes to two coordinates, proves both degree-zero homogeneous localizations are exactly `ℂ[X]` by homogenization/dehomogenization, derives the opposite chart through the exact coordinate-polarity involution, proves both chart structure maps smooth, glues them over the complete basic-open cover, and packages a nonempty `SmoothProjectiveComplexScheme`. `HodgeProjectiveLineAnalyticComparison.lean` constructs actual `Spec ℂ`-valued chart points over that carrier and uses Mathlib's algebraically-closed-field comparison with closed scheme points. It proves finite-coordinate retention and infinity separation, lifts every scheme point through one of the two exact affine opens, reconstructs each lifted ring map as polynomial evaluation at its recovered coordinate, proves the complement of the first chart is precisely the second-chart origin, and returns explicit equivalences among the one-point analytic normal form, actual complex-valued scheme points, and closed points of the genuine `Proj`. It further proves the analytic-to-closed-point map continuous: homogeneous basic opens pull back to polynomial nonvanishing loci on the finite chart, and those containing infinity have finite-root compact complements; the projective basic-open basis closes arbitrary Zariski opens | Mathlib `MvPolynomial`, homogeneous localization, `Proj`, scheme-local smoothness, open-immersion lifting, algebraically closed points, exact ring equivalences, polynomial root finiteness, the one-point compactification topology, and source-authored coordinate transport | consumed by the genuine cycle-source and reduction-parametrized receiver row below |
| `proved-standard; formal-checked` and `proved-derived; formal-checked` | genuine projective-line cycle sources and filling-parametrized complete receiver | `Foundation/CycleFilling.lean` defines a source-retaining linear filler current and proves its exact boundary return implies exactness and zero homology in the addressed degree. `HodgeProjectiveLineRealization.lean` proves every point of the actual projective-line scheme has coheight at most one; hence all integral and rational codimension sources above one vanish. It constructs genuine generic and closed-point cycles, exact coefficient currents, genuine `H₀` and `H₂` Betti duals, and surjective codimension-zero/one cycle classes. Its minimal residual `SphereHigherEvenCycleFillings` asks only for exact fillers of closed sphere chains in degrees `2p`, `p ≥ 2`; from that family it packages a complete `HodgeSemantics`, source-faithful `Realization`, all-codimension Hodge conclusion, and official canonical-family theorem. `SphereTetrahedralReduction` remains a strictly stronger sufficient route | actual locally finite algebraic cycles and coheight, tensor rationalization, exact analytic/Zariski closed-point comparison, genuine singular homology, checked sphere `H₀`/`H₂` equivalences, and retained filler currents with exact boundary returns | construct `SphereHigherEvenCycleFillings`; existing common-star theorems are cycle-indexed or low-degree, while the full tetrahedral `HomotopyEquiv` would additionally demand an unnecessary reverse map and two all-degree homotopies |
| `proved-derived; formal-checked` | elementary holonic primitive cut | `HodgeHolonicPrimitiveCut.lean`: the cycle-class candidate is an actual source-retaining `Holon`, and its `ReconstructionFibre` is equivalent to the complete `CycleLiftFibre`; `SignedDefinitePrimitivePolarization` carries the Hodge--Riemann polarity, proves every nonzero primitive self-pairing is nonzero, and derives nondegeneracy after restriction to every primitive subspace; occupation of every nonzero `primitiveDetectionHolon` receiver fibre is equivalent to `PrimitiveLiftable`; after reconstructing the staircase from source-indexed injective Lefschetz transports, `hodge_iff_primitiveDetection` proves both directions over the explicitly canonically admitted family | the shared `Holon` occurrence/reconstruction owner, actual algebraic-cycle sources, exact cycle-lift fibres, source-indexed Lefschetz transports, rational bilinear forms, polarized positivity, and derived primitive kernels | construct canonical source data and prove every nonzero primitive rational `(p,p)` receiver face has an occupied algebraic-cycle reconstruction fibre, or close it by the monodromy propagation row below |
| `proved-derived; formal-checked` | dimension-bounded Lefschetz and one universal graded residual | `HodgeDimensionBoundedLefschetz.lean` replaces the impossible all-degree injective staircase by the actual finite geometry of a complex `n`-fold. Although source Lefschetz squares remain available throughout the injective range `2p<n`, primitive algebraicity is requested only when the target stays in the closed lower half, `2(p+1)≤n`; thus the exact index carrier has `floor(n/2)` occurrences and deletes the redundant first-upper-half step in every odd dimension. Upper codimensions return from `n-p` through source-bearing surjective hard-Lefschetz transport, codimensions above `n` close through actual zero cohomology, and dimensions zero and one emit no primitive source obligations. `SourceDeterminedHodgeTheory.conclusion_iff_finiteLowerPrimitiveLiftable` binds this once to the universal source current: every `H_{i-1}`, `H_i`, and `H_{i+1}` face is a specialization of the same induction/reflection theorem and schedules no separate computation. `HodgeDimensionBoundedPrimitivePropagation.lean` identifies the remaining source occupation law with the universal conclusion | the genuine source-indexed cycle/Hodge transports, derived primitive kernels, actual cycle-lift/Holon reconstruction fibres, hard-Lefschetz reflection, zero cohomology, signed Hodge--Riemann polarity, and monodromy source transport | construct the one source-determined geometric semantics current and its standard dimension-bounded Lefschetz system, then construct the higher primitive algebraic source current. No further degree census, finite sphere power, coordinate-pair population, or redundant odd-middle step is scheduled |
| `proved-derived; formal-checked` | exact divisor exponential source passage and higher-cycle residual | `HodgeDivisorExponentialPassage.lean` retains rational Picard, rationalized integral cohomology, and analytic-obstruction carriers; first-Chern and obstruction currents; exactness at the integral carrier; an obstruction-null integral-rational lift of every rational `(1,1)` occurrence; an actual divisor-cycle current; and the cycle-class commuting square. Exactness derives the Picard antecedent and the square reconstructs its complete cycle-lift fibre. On a dimension-bounded realization below complex dimension four, the only retained primitive step is the divisor step `p=0`, so this passage plus reflection and vanishing closes every codimension. In every dimension, `HigherPrimitiveIndex n = Fin (n/2-1)` removes the divisor index, and the official Hodge statement is equivalent to the resulting finite codimension-at-least-two source population once the divisor passage is supplied. With finite primitive carriers fixed, the same official receiver is equivalent to exactly `floor(n/2)-1` algebraic/full primitive rank equalities. `HigherFiniteRankPrimitiveSources` retains an actual cycle current, primitive-class current, commuting square, injection, and equal-rank return at each address and therefore closes the receiver without identifying its numerical shadow with its source | linear exactness as the local-to-global kernel law, addressed rationalization charts, genuine Picard/divisor and higher-cycle sources, cycle-class squares, finite-rank reconstruction, and the minimal dimension-bounded Lefschetz receiver | construct the passage from the exponential sheaf sequence, genuine first Chern class, and divisor/line-bundle correspondence on every canonical realization; then construct the residual source packages, beginning with codimension two in dimension four. The abstract structures store exactness and source transport, not the desired Hodge surjectivity |
| `proved-derived; formal-checked` | binary residue--winding reconstruction of the primitive index | `Foundation/EuclideanResidueTransport.lean` constructs lossless natural and signed integer charts `source ≃ ZMod m × winding`; `HodgeDivisorExponentialPassage.lean` instantiates modulus two and proves `dim X = parity + 2*winding`, identifies `floor(dim X/2)` with the exact winding coordinate, reconstructs `ceil(dim X/2)` as winding plus parity, and identifies divisor removal with one addressed winding | exact Euclidean quotient/remainder equivalences, complete receiver reconstruction fibres, `ZMod 2`, and the dimension-bounded Hodge index | consumed by the coordinate-pair source row; no floor, ceiling, quotient, or remainder is used as an approximation or as division of a holon |
| `proved-derived; formal-checked` | whole graded sphere-power carrier and first codimension-two source | `HodgeSphereProductFiniteComplex.lean` computes every degree of the zero-differential surface cell complex in one theorem. `HodgeSpherePowerRulingHomology.lean` generalizes this to every finite power: a degree-`d` cell is the exact subset of sphere factors whose cardinal satisfies `2·card=d`; all differentials vanish, `H_{2k}` has the cell-current carrier of rank `choose(n,k)`, odd degrees have rank zero, and adjoining one sphere obeys the exact Pascal induction law. One `SpherePowerCellularReduction n` transports this complete graded result to genuine rational singular homology at every degree. `HodgeSpherePowerPairHomology.lean` specializes the same incidence at `n=4,k=2`: its six continuous coordinate-plane insertions and matching projections separate the complete class population, and the surface plus whole-power reductions upgrade the coordinate-pair map from injective to a linear equivalence in one theorem. `HodgePowerComparison.lean` transports that equivalence through the global `(P¹)^4 ≃ (S²)^4` topology, dualizes it, and returns a six-address basis and one exact reconstruction theorem for every genuine rational degree-four singular-cohomology class | genuine singular chain complexes and homology, exact subset incidence, chain-homotopy coarse graining, coordinate transport and projections, global topological transport, algebraic duality, and the binary winding/parity index | construct the surface and whole-power chain-homotopy reductions; then realize the six addresses as genuine codimension-two algebraic cycles, construct the analytic rational `(2,2)` submodule, and prove the cycle-class commuting square. The checked coordinate currents are a conditional topological/cohomological basis, not yet algebraic-cycle sources. No degree-wise `H_i` census remains scheduled |
| `proved-derived; formal-checked` | finite primitive rank cut with retained cycle source | `HodgeFinitePrimitiveRank.lean` proves that, on each finite primitive carrier, complete primitive cycle-lift occupation is equivalent to equality between the actual algebraic primitive finrank and the full primitive finrank. `FiniteRankPrimitiveSource` retains a finite source module, an actual cycle-source current, its primitive-class current, the cycle-class commuting square, injectivity, and exact source/receiver finrank equality; these data derive surjectivity, a linear equivalence, and an explicit reconstructed cycle lift for every primitive occurrence. The dimension-bounded universal receiver is consequently equivalent to the finite population of lower-half algebraic/full primitive rank equalities, and the divisor passage deletes its first address so only the `floor(n/2)-1` higher-cycle tail remains | actual algebraic-cycle sources and cycle-class naturality, elementary Holon reconstruction fibres, finite-dimensional linear algebra, and the finite lower-half Lefschetz receiver | construct the source current and commuting square on every canonical higher primitive carrier, then prove injection and the exact rank return; rank equality alone remains only a receiver shadow and does not manufacture cycles |
| `proved-derived; formal-checked` and `counterexample; formal-checked` | source-determined semantic aperture audit | `HodgeSmoothProjectiveReceiver.lean` replaces arbitrary per-realization admission by one dependent source current. A single typed closed-point chart derives the Zariski map, closedness, and bijection. Its fundamental-class current lands in the exact Poincaré preimage of `(p,p)`, so the underlying fundamental class, cycle map, and algebraic-cycle Hodge typing are also derived. `HodgeSemanticsFaithfulness.lean` proves source equality rejects erasure whenever that geometric composite is nonzero. Thus arbitrary admission, an unconstructed semantics field, three independently varying point-chart fields, an independent `cycleClass`, and a free `cycleClassesAreHodge` proof have all been removed | rational complexification, internal Hodge splitting, typed closed-point topology, exact middle-defect kernel, Hodge-typed source homology, Poincaré duality, dependent equality, and an exact zero-current deformation | construct the typed geometric currents on every source and then the higher primitive algebraic source passage; do not add another receiver wrapper |
| `counterexample; formal-checked` | polarized-source insufficiency cut | `HodgeHolonicCutFalsifier.lean` constructs a finite-dimensional negative-definite primitive carrier whose second nonzero direction has an empty cycle-class and elementary-Holon reconstruction fibre, proving that signed Hodge--Riemann definiteness does not imply `DetectsEveryNonzero` | a two-direction rational primitive form, complete reconstruction fibres, and the signed primitive cut | construct actual algebraic source occurrences; positivity alone may not be reused as that source construction |
| `proved-derived; formal-checked` | source-bearing Mestre primitive passage | `HodgeMestrePrimitivePassage.lean` polarizes the exact rank-twelve Mestre height quadratic into a symmetric bilinear form, proves its diagonal is the checked `Q`, retains section combinations as occurrences of an elementary Holon, and proves every nonzero direction has an occupied height-detector fibre; `PrimitiveComparison` retains an actual section-cycle map, a primitive-class transport into an exact rank-twelve target, the cycle-class square, and Shioda's negative-height/intersection square. Height anisotropy derives injectivity, after which the comparison instantiates the generic `FiniteRankPrimitiveSource`; exact source/receiver rank derives surjectivity and an explicit cycle reconstruction, while the same source independently occupies every signed primitive detector fibre | Fable's exact `MestreHeightLattice` sum-of-squares/anisotropy result, the elementary `Holon`, the generic finite primitive rank cut, cycle-lift fibres, and signed Hodge primitive detection | construct `PrimitiveComparison` on the actual Mestre K3 realization; `6804` is presently the proved pivot product for the twelve-section lattice, while the claimed full Néron--Severi discriminant `756` remains exterior until its index and discriminant comparison are derived |
| `proved-derived; formal-checked` | irreducible Hodge-preserving monodromy seed propagation | `HodgeMonodromyPrimitivePropagation.lean`: one primitive Hodge action is paired with a genuine representation on algebraic-cycle sources and a commuting cycle-class square. Applying a loop and its inverse derives an exact equivalence of complete cycle-lift fibres and hence invariance of the actual algebraic primitive subspace. If the primitive representation is irreducible and one nonzero occurrence has an occupied algebraic-cycle fibre, the invariant subrepresentation cannot be bottom and therefore is top. The file returns `PrimitiveLiftable` and occupies every signed detector fibre | Mathlib representations and subrepresentations, actual cycle-source actions, exact cycle-lift fibres, the elementary holonic primitive cut, and dimension-bounded source-indexed Lefschetz systems | construct a geometric Hodge-locus action on both primitive classes and actual cycles, prove the cycle-class square and irreducibility (or use an orbit cover), and provide one nonzero algebraic seed on every lower-half block; ordinary ambient Gauss--Manin monodromy is not silently treated as Hodge-preserving |
| `proved-derived; formal-checked` | source-bearing Hodge-monodromy orbit-cover audit | `HodgeMonodromyPrimitivePropagation.lean`: a `PrimitiveOrbitSourceCover` retains primitive algebraic seeds, their complete cycle-lift fibres, a cycle-source group action commuting with the primitive action, and an orbit-spanning equality. These data imply `primitiveAlgebraicClasses = ⊤`. The converse audit constructs such a cover from `PrimitiveLiftable` itself by taking every primitive occurrence as a seed and using the identity action; therefore `Nonempty PrimitiveOrbitSourceCover ↔ PrimitiveLiftable`. Unrestricted cover existence is exactly the conjectural primitive source law, not an independent compression of it | exact reconstruction fibres, paired source/receiver representations, the commuting cycle-class square, submodule span, and the identity-action counter-construction | do not use unrestricted orbit-cover existence as progress toward Hodge. Construct a source family fixed independently of the target primitive occurrence together with its geometric transport and a proved spanning law, or construct an actual irreducible geometric variation with one pre-existing nonzero algebraic seed |
| `proved-derived; formal-checked` | projective-line product holonic primitive realization | `HodgeProjectiveLineHolonicPrimitive.lean`: the ample ruling sum and its orthogonal primitive difference line instantiate an exact `PrimitiveHodgeStep`; the existing intersection matrix supplies the negative signed polarization; every nonzero primitive direction is detected by its own reconstructed ruling-cycle occurrence; the occupied primitive holon returns the complete two-ruling Hodge conclusion | exact ample/primitive decomposition, ruling intersection form, finite source reconstruction, and the elementary holonic primitive cut | transport this complete validation through a genuine Segre scheme/analytic/cycle-class realization; no synthetic bidegree identity may stand in for that remaining comparison |
| `proved-derived; formal-checked` | rank-two projective-line product passage | `HodgeProjectiveLineProduct.lean`: constructs the actual body `Projectivization ℂ ℂ² × Projectivization ℂ ℂ²`, addresses its two projection-fibre supports, proves the bidegree decomposition and intersection matrix `[[0,1],[1,0]]`, diagonalizes it into ample square `2` and primitive square `-2`, builds a two-cycle Hodge basis, reconstructs every modeled rational Hodge occurrence, and transports every source cycle through a variety/cycle/Hodge/cohomology comparison satisfying the two naturality squares | source-specific composition of projectivization, the finite-basis Hodge passage, and exact rational intersection algebra | consumed by the completed geometric, singular, and analytic product-surface owners; generalize the construction to a strictly larger admitted family |
| `proved-derived; formal-checked` | geometric surface realization and divisor source | `HodgeProjectiveLineAtlas.lean`, `HodgeProjectiveLineDivisors.lean`, `HodgeProjectiveLineHolomorphicAtlas.lean`, and `HodgeProjectiveLineSegre.lean`: construct the two quotient-level affine charts and four product charts; prove exact reconstruction, inversion on overlaps, and complex differentiability with derivative `-z⁻²`; identify the two cycles as rational combinations of actual projection fibres; prove parallel fibres disjoint, transverse fibres intersect in one point with determinant one, and construct the divisor-to-bidegree equivalence; construct an injective homogeneous quadratic Segre map into `ℙ³` whose image satisfies `X₀₀X₁₁-X₀₁X₁₀=0` | source-specific quotient, complex-calculus, set-incidence, and homogeneous-coordinate construction on the actual carrier | prove the constructed algebraic atlas/Segre realization agrees with a full scheme/smooth-variety owner when that richer receiver is requested; no such agreement is needed for the checked divisor incidence |
| `proved-derived; formal-checked` | cellular and singular reduction | `HodgeProjectiveLineCellularCohomology.lean`, `HodgeProjectiveLineTopology.lean`, and `HodgeProjectiveLineSingularReduction.lean`: prove `ℙ¹={∞}⊔ℂ`, construct the four even product cells and the two actual two-cell closures, prove the degree-two incoming and outgoing cellular coboundaries vanish, construct cellular `H²` and its cycle-class map from geometric ruling divisors, close the complete cellular Hodge reconstruction, transport the projectivization topology from `OnePoint ℂ`, prove `ℙ¹≃ₜS²` and the surface `≃ₜS²×S²`, and functorially reduce every actual rational singular-homology degree to the sphere product; the complete populations of degree-two cellular-to-singular comparisons are equivalent on the two targets | exact cell support, zero-coboundary, homeomorphism, and Mathlib singular-homology functoriality; no numerical or chosen inverse collapse | consumed by the completed product decomposition, singular dual, and analytic period passage |
| `proved-derived; formal-checked` | explicit singular cycles and projection separation | `HodgeSphereProductFiniteComplex.lean`, `HodgeProjectiveLineCellFiltration.lean`, `HodgeTwoSphereFundamentalCycle.lean`, `HodgeTetrahedralSphereComplex.lean`, `HodgeSphereProductRulingCycles.lean`, `HodgeSphereProductRulingHomology.lean`, and `HodgeSphereProductRulingProjections.lean`: construct the complete even finite complex and geometric cell filtration; construct four radial tetrahedral face simplices on `S²`; compute the finite tetrahedral top kernel as `ℚ` with a nonzero fundamental class; prove all six oriented edge gluings and the finite-to-singular boundary naturality square; push the cycle into both geometric rulings of `S²×S²`; lift both through the categorical cycle kernel into genuine rational singular-homology classes; and prove matching projections return the sphere class while crossed projections vanish already at chain level | explicit continuous simplices, finite incidence, categorical singular chains, kernel/homology quotients, functorial retractions, and exact alternating cancellation | consumed by the nonboundary, decomposition, and analytic period owners |
| `proved-derived; formal-checked` | visible-cycle receiver and exact Hodge detector interface | `Foundation/BoundaryReceiver.lean` proves source-neutrally that a boundary-annihilating receiver with a nonzero cycle reading separates that cycle from the boundary image; `HodgeSphereFundamentalDetector.lean` types the exact normalized singular detector and stronger tetrahedral retraction sufficient for the present source, proves the detector separates `sphereFundamentalCandidate` from the singular three-boundary image, descends it to genuine rational singular homology, and derives nonvanishing plus injectivity of the tetrahedral and ruling realizations; the same foundation theorem now carries the concrete polygonal-torus and four-torus nonboundary proofs | generic additive receiver theorem, categorical homology descent, and exact source adapters; no constructed singular detector is assumed | closed as a free interface; the remaining construction is sharpened by the next row to one genuine chain map and one retraction square |
| `proved-derived; formal-checked` | complete finite tetrahedral target and local-to-global detector composition | `HodgeTetrahedralChainComplex.lean` adds the four addressed vertices to the existing six edges and four faces, proves every edge boundary is terminal minus initial, proves `∂₁∂₂=0`, and packages the exact rational complex `C₂ → C₁ → C₀` with zero carrier above degree two; `HodgeTetrahedralRealizationChainMap.lean` proves equality of nested vertex occurrences from their complete face-inclusion words, proves the realized edge-to-vertex square, and assembles the four radial faces, six shared edges, and four vertices into one genuine geometric chain map; `HodgeTetrahedralReduction.lean` proves a chain retraction returns the detector; `HodgeTetrahedralCarrierAssembly.lean` proves that a face-natural local assignment on every addressed singular simplex linearizes over the singular-chain coproduct to the required global reduction, and that returning the four radial faces to their matching finite atoms proves the retraction square | explicit finite incidence, exact nested face transport, Mathlib coproduct and chain-complex naturality, the existing singular realization, and detector descent | construct one `FaceNaturalCarrier` normalized on the four radial faces; this is the exact subdivision/carrier theorem, and it must retain seam testimony rather than assigning arbitrary seam-crossing singular simplices to faces by point sampling |
| `proved-derived; formal-checked` | geometric star subdivision and uniform seam conservation | `HodgeStellarSubdivision.lean` constructs the exact barycentre of the standard triangle, three affine cone maps as genuine continuous self-maps of the simplex, the three paired interior spokes, and the resulting subdivision of every addressed singular two-simplex; it proves the internal spokes cancel, the original exterior boundary is returned, the construction extends linearly to every rational singular two-chain, and every finite iteration has exactly the same boundary | standard-simplex affine geometry, complete singular-simplex face words, coproduct linearization, and the alternating boundary law | retain this operator for its exact seam/homotopy laws; the later mesh counterexample proves it is not a cover-small refinement and the barycentric owner supplies that distinct consequence |
| `proved-derived; formal-checked` | geometric tetrahedral subdivision and six-seam cancellation | `HodgeTetrahedralStellarSubdivision.lean` constructs the exact barycentre of the standard tetrahedron, four affine cone maps, all six addressed internal triangular pairings, and the induced subdivision of every singular three-simplex; it proves the signed four-cone population has exactly the original exterior boundary, linearizes the operation to all rational singular three-chains, and proves boundary invariance at every finite iteration | standard-tetrahedron affine geometry, complete singular-simplex face words, coproduct linearization, and the alternating boundary law | the basic four-cone operator is now retained as the exterior-preserving term of the recursive operator in the next row |
| `proved-derived; formal-checked` | explicit subdivision homotopy and recursive chain-map square | `HodgeStellarSubdivisionHomotopy.lean` cones every stellar subtriangle and the identity triangle to the exact barycentre, proves all six coned edge seams pair with opposite orientation, constructs a singular three-chain whose boundary is `stellarSubdivision σ - simplexGenerator σ`, linearizes it to `P₂` with `P₂∂ = S₂-id`, defines the corrected degree-three operator `S₃rec = S₃ + ∂P₂`, proves `S₃rec∂ = ∂S₂`, and proves the synchronized equality after every finite refinement depth | explicit affine cone geometry, addressed singular-simplex faces, coproduct linearization, exact chain homotopy, and additive category composition | reuse the checked recursive pattern for the contracting barycentric operator; stellar class preservation survives even though its separate geometric cover-smallness claim was refuted |
| `counterexample; formal-checked` | three-cone mesh obstruction | `HodgeStellarSubdivisionMeshObstruction.lean` exhibits the all-zero descendant branch, proves it fixes both endpoints of one complete exterior edge at every finite scale, constructs two exact open coordinate apertures covering the standard triangle with no member containing both endpoints, and proves that branch is never subordinate at any scale | source-simplex topology, exact rational apertures, persistent addressed vertices, and an explicit open-cover receiver | the three-cone operator remains valid for its chain-homotopy laws but cannot supply cover-smallness; construct an edge-refining barycentric successor and prove its uniform contraction before building the normalized carrier |
| `proved-derived; formal-checked` | edge-refining barycentric current | `HodgeBarycentricEdgeSubdivision.lean` constructs the exact segment midpoint, two affine half-edge maps, their paired midpoint seam, the signed subdivision of every singular one-simplex, its linear extension, and the degree-`1 → 0` chain square; each addressed half contracts the retained source parameter distance by exactly `1/2` | exact standard-simplex affine geometry, addressed endpoint faces, coproduct linearization, and the singular boundary law | compose this degree-one current with the six-cell triangle current and its recursive homotopy; do not quotient reversed parametrizations into coefficient signs |
| `proved-derived; formal-checked` | six-cell barycentric triangle and contracting transport words | `HodgeBarycentricTriangleSubdivision.lean` constructs six affine subtriangles indexed by an exterior face and half-edge, proves all three midpoint seams and all three barycentre-to-vertex seams pair, proves the exact degree-`2 → 1` chain square with edge subdivision, and proves every descendant word contracts squared coordinate distance by the exact factor `(4/9)^word.length`; concatenated words are proved to be literal serial composition | exact rational barycentric weights, complete seam population, singular face naturality, and an algebraic quadratic contraction proof | compose the checked recursive degree-three current with support synchronization and the finite-face receiver |
| `proved-derived; formal-checked` | twenty-four-cell barycentric tetrahedron chain square and cover-small transport | `HodgeBarycentricTetrahedron.lean` constructs the twenty-four complete flags `tetrahedron ⊃ face ⊃ edge ⊃ vertex`, proves every exterior face is the existing six-cell barycentric descendant, pairs all thirty-six internal triangular seams, proves `∂S₃^bar=S₂^bar∂` and its finite-depth iterate, and proves exact squared-distance contraction by `9/16` per cell and `(9/16)^word.length` per lineage word; `HodgeBarycentricTetrahedronCoverSmallness.lean` supplies uniform cover-smallness through each singular tetrahedron and every finite occurrence population | exact standard-simplex affine geometry, nested barycentres, complete singular-face lineage, rational sum-of-squares contraction, compactness, and the metric Lebesgue-number theorem | construct a face-compatible star labeling on the finite refined occurrence complex; independent cell labels do not yet preserve shared-face cancellation |
| `proved-derived; formal-checked` | source-specific cover-smallness and finite synchronization | `HodgeBarycentricCoverSmallness.lean` combines the exact `(4/9)^n` law with compactness and the metric Lebesgue-number theorem to prove that every open cover of the triangle receives all descendant images at one finite depth; it pulls that theorem through every singular `S²` simplex, proves every deeper word remains subordinate by retained suffix factorization, and synchronizes one exact scale across any finite addressed simplex family | compact standard simplex, exact metric contraction, open-cover pullback, transport-word factorization, and finite occurrence indexing | compose the synchronized depth with the actual-chain support chart and the seam-compatible finite-face return |
| `proved-derived; formal-checked` | explicit degree-one barycentric homotopy and isolated degree-two filling current | `HodgeBarycentricSubdivisionHomotopy.lean` constructs a main midpoint sweep, a folded source triangle retaining reversed parametrization, and a constant triangle retaining the degenerate seam; their signed boundary is exactly edge subdivision minus the original edge, and coproduct linearization proves `P₁∂ = S₁-id`; it then constructs `R₂=S₂-id-∂P₁`, proves `R₂∂=0`, packages the sole remaining geometric datum as a filling `P₂` with `P₂∂=R₂`, and proves every such filling automatically corrects the degree-three current to satisfy the required chain square | exact affine source maps, complete singular parametrization lineage, explicit degeneracy cancellation, coproduct linearization, and chain-complex `∂²=0` | the next row inhabits the exposed field without quotienting source maps |
| `proved-derived; formal-checked` | source-faithful affine filling and unconditional recursive degree-three square | `HodgeBarycentricDegreeTwoFilling.lean` retains the explicit common-apex sixteen-term candidate; `HodgeBarycentricAffineSourceComplex.lean` constructs free rational chains on triangle and edge source maps, proves the six barycentric, identity, and nine prism occurrences form a closed source current before any sphere receiver is applied, proves the common-apex cone contraction identity on every affine source triangle, identifies source realization with `R₂`, linearizes the cone to `P₂`, inhabits `BarycentricDegreeTwoFilling`, and proves the unconditional corrected square `S₃rec∂=∂S₂` | exact free source-map populations, affine reconstruction, common-apex edge-cone realization, source boundary cancellation, categorical coproduct linearization, and the checked recursive correction theorem | closed for one-step and recursive subdivision; the iterated homology return is constructed below |
| `proved-derived; formal-checked` | actual rational-chain support and exact reconstruction | `HodgeBarycentricChainSupport.lean` transports the categorical singular-chain coproduct to its concrete dependent direct sum, returns the genuine finite support and coefficient at every addressed simplex, reconstructs the original chain exactly as the support sum, and applies the synchronized cover theorem to that support | categorical coproduct/direct-sum comparison, finite-support coefficients, exact generator reconstruction, and source-specific barycentric cover-smallness | extend the support chart to the finite face closure of a hypothetical degree-three boundary witness and synchronize the boundary and radial-cycle refinements |
| `proved-derived; formal-checked` | oriented tetrahedral label current and exact carrier interface | `HodgeTetrahedralLabelCarry.lean` constructs oriented vertex, edge, and face currents from ordered tetrahedral labels, proves terminal-minus-initial and triangle boundary laws, proves cancellation under repeated labels, and packages face-compatible labels with an explicit degree-three admissibility law into `FaceNaturalCarrier`; canonical complement labels return the four radial face atoms and hence construct the actual degree-two receiver | exact finite tetrahedral incidence, source-face naturality, explicit radial normalization, and a checked all-distinct-label falsifier | the global label field is sufficient but overstrong for the active proof; construct only the boundary-witness-relative finite face-closed label population after synchronized subdivision, then derive nonboundary directly |
| `proved-derived; formal-checked` | sequential coherent-history law and holonomy separator | `HolonicDirectedPassage.lean`: a base occurrence and surjective successor restriction construct an exact coherent section through all natural depths; the bijective Boolean reversal loop has no coherent fixed section | dependent recursion with retained restriction equalities, plus an exact finite loop counterexample | instantiate the law only after the source proves its extension maps; Hodge presently needs finite face-closed compatibility, while general finite cofiltered systems reuse Mathlib's existing section theorem |
| `proved-derived; formal-checked` | finite boundary-witness carrier and nonboundary reduction | `HodgeFiniteCarrier.lean`: for the genuine finite support of any rational singular three-chain, the complete coefficient-weighted alternating tetrahedral face current vanishes under local empty-fourfold admissibility; it cannot simultaneously return the nonzero fundamental face current; constructing that finite return from every alleged radial-cycle boundary proves the radial cycle is outside the singular boundary range | actual dependent direct-sum support, retained coefficients, exact tetrahedral incidence, and coordinate-zero separation of the finite fundamental current | construct the conditional return on the finite face closure by synchronized barycentric refinement, explicit shared-seam conservation, and radial normalization |
| `proved-derived; formal-checked` | global-vertex closed-star labeling and radial exclusion | `HodgeFiniteClosedStarLabeling.lean` replaces cell-local choices by one global vertex population, proves closed-star labels give every incident tetrahedron a common-star witness and admissible four-label word, and constructs such labels from exact radius-third cell balls under a uniform star Lebesgue aperture; `HodgeRadialSpernerCarry.lean` proves the radial face opposite `f` never enters `vertexStar f`, so every carried radial label avoids the omitted vertex | retained global incidence, compact metric star refinement, a three-leg triangle inequality, and exact normalized tetrahedral coordinates | instantiate the mixed refined bulk/boundary incidence complex; prove relative edge telescoping and face carry, then derive rather than assume `returnsRadial` |
| `proved-derived; formal-checked` | point-natural radial edge and face reconstruction | `HodgePointCarry.lean`, `HodgeRefinementWords.lean`, and `HodgeRadialCurrent.lean` pull one actual-point label through every shared simplex vertex, retain every fixed-depth edge/triangle/tetrahedron word, prove refined radial edges and faces return their addressed finite atoms, extend the edge return to arbitrary six-edge chains, and prove every refinement of the four-face radial sphere returns `fundamentalFaceChain` exactly | point identity across seams, exact word lineage, low-degree chain naturality, radial support, finite boundary rigidity, and complete four-face gluing | closed for the radial source; the arbitrary-cycle passage is closed by the common-star normalization row below |
| `proved-derived; formal-checked` | refined bulk obstruction and singular nonboundary | `HodgeRefinedBoundaryObstruction.lean` chooses one exact refinement depth for the genuine support of every proposed singular three-boundary, proves each refined tetrahedral boundary has zero point current, contradicts the nonzero refined radial return, proves `sphereFundamentalCandidate` is not in the singular boundary range, and derives the nonzero sphere homology class plus injectivity of the tetrahedral and two-ruling realizations | finite support reconstruction, exact subdivision words, radius-third cover transport, local four-label admissibility, quotient exactness, and projection retractions | the former `GeometricBoundaryReturn` assumption is removed; prove surjectivity rather than repeating nonvanishing |
| `proved-derived; formal-checked` | fixed-depth subdivision homology return | `HodgeIteratedBarycentricHomology.lean` composes the source-faithful affine cone through every declared refinement depth and proves that, for every genuine singular two-cycle, the accumulated addressed three-current has boundary exactly `iteratedSubdivision(scale, z) - z` | unconditional one-step affine filling, exact triangle/edge boundary squares, and finite serial composition of the retained homotopy currents | consumed by the common-star normalization composition below |
| `proved-derived; formal-checked` | refined-cycle finite coordinate return | `HodgeRefinedCycleCarrier.lean` proves the point current of every fixed-depth refinement of a genuine sphere two-cycle has zero complete six-edge boundary, applies the computed finite top kernel to identify it with its face-zero coordinate times `fundamentalFaceChain`, and realizes it as the same scalar multiple of `sphereFundamentalCandidate` | point-current boundary naturality, exact refined boundary transport, and tetrahedral cycle coordinates | consumed by the common-star normalization composition below |
| `proved-derived; formal-checked` | globally addressed refined-triangle star carrier | `HodgeRefinedTriangleClosedStar.lean` presents every supported fixed-depth triangle word as a degenerate tetrahedral occurrence, identifies vertices by their actual sphere points across all local copies, constructs one exact radius-third presentation at a synchronized depth, and returns a coherent closed-star label on the complete incident population | actual finite support, exact refinement words, simplex codegeneracy, metric cover smallness, and the standing global-vertex closed-star owner | construct the local path/edge/triangle fillings inside the one-, two-, and three-label star intersections and prove their addressed seam cancellation |
| `proved-derived; formal-checked` | fixed-chart normalization, common-star reduction, and sphere `H₂` equivalence | `HodgeLabelWordContraction.lean` represents the complete normalization defect in one fixed omitted-coordinate chart, proves its free boundary vanishes through the tetrahedral face/edge chain-map square, maps the generic prefix contraction to an explicit singular three-current, and packages the return as `affineLabelSimplexNormalizationHolon`; `HodgeCommonStarNormalization.lean` sums those fillers, cancels the addressed edge seam, and composes refinement plus prism minus normalization into one current with boundary `q • sphereFundamentalCandidate - z`; `HodgeSphereHomologyEquivalence.lean` descends that exact boundary through the genuine homology quotient and proves `tetrahedralHomologyRealization` bijective | ordered words with repetitions retained, one fixed chart per summed current, exact singular realization, familywise seam factorization, quotient exactness, and the independent radial nonboundary theorem | consumed by the checked product-ruling decomposition |
| `proved-derived; formal-checked` | genuine sphere-product decomposition and cohomology dual | `Foundation/DiagonalChainTransport.lean`, `HodgeProductDiagonal.lean`, the sphere low-degree owners, `HodgeProductMixedFilling.lean`, and `HodgeProductRulingDecomposition.lean` separate, contract, and rejoin every genuine closed product two-cycle, returning an actual degree-three witness to its difference from the two rulings; the ruling map is an equivalence; `HodgeProductSingularCohomologyDual.lean` transports its dual to the actual surface with the fixed-factor/varying-factor evaluation law | exact diagonal-chain homotopy, low-degree sphere fillers, coupled axis contraction, quotient exactness, and source topology | closed for the product surface; consumed by the analytic period passage |
| `proved-derived; formal-checked` | analytic `(1,1)` source and singular period identification | `HodgeProjectiveLineType11Form.lean` constructs the Fubini--Study carrier both as a pointwise real alternating form and a smooth continuous differential two-form, proves the two presentations equal, proves closedness from the exact `3 > dim_ℝ ℂ` alternating-form obstruction, proves `I`-invariance and exact inversion pullback under derivative `-z⁻²`, and carries unit transition winding with a rational integral witness; `HodgeSurfaceType11Period.lean` pulls that one source through either factor by a single `Fin 2`-indexed operation, proves crossed restriction zero, derives the period functional from the carried integral winding, constructs `rationalType11` as the analytic period range, identifies it with the singular divisor cycle classes, and proves `surfaceType11Conclusion` | exact complex area and exterior-calculus algebra, finite-dimensional alternating-form vanishing, atlas overlap transport, circle integral, the genuine ruling homology equivalence, and divisor-cycle naturality | the complete `ℙ¹×ℙ¹` validation instrument is closed; enlarge the admitted family rather than adding another adapter for this surface |
| `proved-derived; formal-checked` | finite-power analytic family, uniform genuine ruling equivalence, global period/divisor comparison, and equation-only Segre image realization | `HodgeProjectiveLinePowerType11.lean` constructs the `Fin n`-addressed analytic factor currents on every `(ℙ¹)^n`, with smoothness, closedness, exact `(1,1)` and overlap laws, normalized periods, and coefficient reconstruction. `HodgeSpherePowerRulingHomology.lean` realizes every sphere-power successor as an exact product-simplex chart, recursively transports the low-degree current datum, decomposes every closed successor two-cycle with a degree-three source witness, and proves `(Fin n → ℚ) ≃ₗ[ℚ] H₂((S²)^n;ℚ)` for every positive `n`. `HodgePowerComparison.lean` constructs global topology/duality, exact analytic-period/divisor-cycle-class naturality, and `powerType11Conclusion`. `HodgePowerSegre.lean` constructs the finite Segre map, proves its coordinates equivalent to binary factor words, and defines a homogeneous equation population at every recursive binary cut which stores no factor witness. From those equations alone, repeated nonzero-section reconstruction returns every ordered projective factor and proves the global Segre range exactly equal to the recursive minor locus for every finite power | continuous alternating pullback, normalized winding, exact product-current normalization, recursive source witnesses, genuine singular-chain functoriality, powerwise topological transport, algebraic duality, actual projection-fibre incidence, exact receiver evaluation, projective tensor reconstruction, nonzero-pivot factorization, scale reversal, and homogeneous minor cancellation | prove closedness and nonsingularity/global atlas transport, prove coordinate fibres are hyperplane pullbacks, and package the conclusion-free smooth-projective admission |
| `proved-derived; formal-checked` | constructed geometric/cellular admission | `HodgeProjectiveLineGeometricAdmission.lean`: packages the independently proved holomorphic atlas, `S²×S²` topology, injective Segre map, nonvanishing quadric Jacobian, geometric divisors, transverse intersection, and cellular datum without storing a conclusion or surjectivity field; proves the resulting admitted family inhabits `TheHodgeConjectureIn` and returns an actual ruling-divisor lift for every cellular Hodge occurrence | exact composition of the source owners above and finite-basis cycle reconstruction | superseded as the strongest product-surface result by the singular analytic datum; retained as the cellular admission face |

[proved-derived; formal-checked] The complete `ℙ¹ × ℙ¹` singular/analytic passage is now closed:
every genuine product two-cycle has an exact ruling decomposition with retained boundary witness;
the ruling classes form the complete rational singular `H₂`; their dual has the exact divisor
evaluation law; and two independently constructed Fubini--Study factor currents are smooth,
closed, globally overlap-compatible, type `(1,1)`, integrally normalized, and identified with the actual ruling
divisor cycle classes.  The rational `(1,1)` submodule is the analytic period range and only then
is proved equal to the complete degree-two cohomology receiver.

[open] The analytic, topological, singular-homology, cohomology-dual, period, and coordinate-divisor
passages are now all closed for every positive finite power `(ℙ¹)^n`; `powerType11Conclusion` is the
source-specific codimension-one Hodge return.  This still does not inhabit the universal Hodge
receiver.  The exact remaining finite-family proposition is a conclusion-free geometric
admission certificate proving that the global carrier is smooth projective and that the coordinate
fibres used by `PowerRulingDivisor` are algebraic cycles.  The finite Segre tensor embedding and
its injectivity are now constructed, with homogeneous coordinates exactly indexed by binary factor
words.  The complete homogeneous rank-one minor population is returned: the generic two-factor
image equals its common-zero locus by explicit nonzero-pivot factorization, and the equation law is
transported through every recursive binary cut.  Its equation-only common-zero locus is proved
exactly equal to the finite Segre range.
Closedness, nonsingularity/global atlas transport, and the coordinate-hyperplane pullback law remain.
After that admission, the universal receiver still ranges over arbitrary smooth
projective varieties and all codimensions; further movement must enlarge the carrier or codimension
rather than rename the closed finite-power datum.

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
| `counterexample; formal-checked` | sign-bearing strain difference | `NavierStokesVorticityStrainDifference.lean` proves that the canonical skew jet reconstructed from vorticity annihilates that same vorticity, so the signed stretching reading is carried exactly by symmetric strain; explicit trace-free jets have equal curl and divergence but stretching readings `+1` and `-1` | source-specific composition of the actual `Matrix3` curl, divergence, Hodge jet split, and inner-product action owners | curl, divergence, and vorticity magnitude cannot factor the remaining integral; construct the symmetric Hodge/Biot--Savart strain passage with its vorticity-direction difference retained |
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
| `conditional; formal-checked` | infinite-depth spatial cross receiver | `NavierStokesVorticityDirectionKernelScaleLimit.lean` constructs the full spatial cross-coherence `tsum`, proves every finite word is uniformly bounded by it under the exact summability condition, proves dyadic cutoffs escape to infinity, sends the coefficient reconstruction fibre to zero on every strict-interior slice, and returns an infinite-depth bound for the literal real vortex-stretching integrand, including the zero-vorticity chart | exact limit composition of the spatial scale assembly, smooth-slice coefficient decay, dyadic cofinality, nonnegative `tsum` gluing, and the physical stretching bridge | the apparatus summability and fixed base are now inhabited below; construct a source distance-modulus coefficient with the required space-time control and integrate it to maximal time |
| `conditional; formal-checked` | modulus-to-kernel-moment constitutive passage | `NavierStokesVorticityDirectionKernelMoment.lean` defines a continuous nonnegative receiver-relative spatial cross modulus, constructs the matching physical Hodge kernel moments, proves the actual cross mass at every scale is bounded by `constant × moment`, and proves summable moments construct both the full cross-coherence summability carrier and a full-mass bound; integer powers of torus distance instantiate the modulus interface | exact spatial integral transport through the positive kernel-point-mass receiver, continuous compact integration, nonnegative comparison, and `tsum` gluing | the linear-distance kernel moments are inhabited below; prove the solution's oriented vorticity cross difference obeys that modulus with a terminal-time-integrable coefficient |
| `proved-derived; formal-checked` | distance-weighted Hodge-kernel localization | `Foundation/CoordinateHaarMomentReceiver.lean` proves the exact one-circle second-moment bound `1/(8R)`, interpolates it with Haar mass to obtain first moment `5/(8√R)`, and composes the three geometric fibre coordinates into distance moment `15/(2√R)`; `NavierStokesVorticityDirectionKernelMomentDecay.lean` transports all 27 actual Hodge entries through that receiver, proves their physical distance moments decay like `2^{-scale/2}`, proves the full scale population summable including the three low scales, and constructs cross-coherence summability from any source linear-distance law | source-specific composition of the eight exact Abel subset returns, centered circle geometry, product Haar/Fubini transport, dyadic-radius arithmetic, geometric-series summation, and the actual kernel point-mass owner | apparatus-side localization is closed; construct and time-control the source coefficient in `|omega(x) cross omega(x-y)|₁ ≤ C(t,x) dist(y,0)` |
| `proved-derived; formal-checked` | non-circular scale-zero energy descent | `NavierStokesVorticityDirectionBaseEnergy.lean` uses Parseval to bound every actual velocity coefficient by its component cube energy, transports the fixed unit-frequency population through exact curl and Hodge ascent, bounds the 27-mode base low pass by `1458π·sqrt(2E(t))`, and rebuilds the finite, infinite-depth, and literal physical vortex-stretching returns with ordinary periodic kinetic energy in place of the critical-vorticity payment | exact composition of componentwise Parseval, unit-cube lattice incidence, curl multiplier, modewise Hodge ascent, kinetic-energy inclusion, finite scale gluing, dyadic tail convergence, and the spatial cross receiver | the circular base term and apparatus kernel moments are removed; prove a terminal-time-integrable source direction-modulus coefficient, then integrate the resulting physical bound through the enstrophy/continuation receiver |
| `proved-derived; formal-checked` | physical source distance modulus | `NavierStokesVorticityDirectionSourceModulus.lean` constructs an exact centered Euclidean representative of every torus displacement, proves its norm is at most `3·dist(y,0)`, obtains a finite vorticity Lipschitz coefficient on the common radius-three compact chart from the actual `C¹` slice, and proves `|omega(x) cross omega(x-y)|₁ ≤ 9|omega(x)|₁ K(t) dist(y,0)`; this inhabits the infinite-depth spatial coherence carrier and removes the summability hypothesis from the physical stretching theorem | exact torus quotient transport, compact local Lipschitz extraction, cross-product difference cancellation, and the inhabited Hodge distance-moment population | the selected coefficient is finite for each `t<T`; terminal-time measurability and integrability are not consequences of strict-interior smoothness |
| `proved-derived; formal-checked` | unit-cube enstrophy closure | `NavierStokesVorticityDirectionEnstrophyClosure.lean` proves the reciprocal direction receiver cancels the fourth coordinate-`L¹` power by `‖(dot(omega,omega))⁻¹‖·|omega|₁⁴ ≤ 81‖omega‖²`, packages the complete Hodge distance-moment `tsum`, derives a spatially uniform pointwise enstrophy-density bound, integrates it over the actual periodic cube, and replaces the former uniform-Jacobian premise in the exact enstrophy-rate inequality by one constructed time coefficient | exact composition of the physical direction reconstruction, source modulus, summable kernel moment, real/complex chart, compact spatial integral, and periodic enstrophy identity | prove the constructed rate interval-integrable up to the maximal time or replace its full vorticity Lipschitz face by a sharper direction-only/scale-critical receiver and then connect the resulting enstrophy control to terminal restart |
| `proved-derived; formal-checked` | canonical derivative modulus | `NavierStokesVorticityCanonicalModulus.lean` replaces the arbitrary slice-wise Lipschitz witness by the norm of the actual continuous spatial-vorticity derivative population on the compact radius-three chart; it reconstructs the source distance law, all-scale coherence, pointwise stretching, cube-integrated stretching, and enstrophy-rate law with that canonical coefficient | exact compact-open receiver over the actual `fderiv`, mean-value transport, and the completed spatial Hodge passage | the coefficient is canonical and finite at every `t<T`; its terminal integral is not supplied by this spatial theorem |
| `proved-derived; formal-checked` | strict-interior time transport | `NavierStokesVorticityCanonicalTime.lean` proves joint space--time smoothness of actual vorticity on `ℝ³×(0,T)`, identifies each slice derivative with the joint derivative restricted to the spatial inclusion, curries the compact chart, and proves both the canonical derivative norm and complete enstrophy coefficient continuous on `(0,T)` and interval-integrable on every ordered `[a,b]⊂(0,T)` | exact joint derivative restriction, compact-open currying, norm transport, and compact-interval integration | obtain a terminal quantitative estimate; strict-interior continuity cannot close `[0,T]` |
| `proved-derived; formal-checked` | anchor-free critical-receiver reconstruction | `NavierStokesVorticityCanonicalCriticalBridge.lean` proves the zero Fourier mode of actual periodic vorticity vanishes by the exact curl multiplier, returns zero Haar mean in the real Euclidean carrier, transports every torus pair through one centered displacement of norm at most `3/2`, and proves `criticalVorticityRate(t) ≤ (3/2)·canonicalVorticityDerivativeRate(t)`; terminal integrability of that derivative rate constructs the exact critical integral and the compatible continuation carrier | source-specific composition of curl incidence, probability-Haar reconstruction, centered quotient transport, canonical Lipschitz control, and the completed BKM/Hodge restart owner | prove the canonical derivative rate interval-integrable through the maximal terminal time, or replace it by a weaker source rate whose terminal integral follows from the PDE |
| `counterexample; formal-checked` | energy-to-derivative scale separation | `NavierStokesTerminalEnergySeparation.lean` constructs one exact Fourier occurrence at each axial frequency, proves its order-zero mass is always `1`, proves its order-two mass is exactly `(1+(2π)²n²)²`, and separates every proposed scalar order-zero-to-order-two bound by an Archimedean choice of `n` | exact singleton `ℓ²` population, Sobolev weight, Stokes eigenvalue, and complete `tsum` receiver | kinetic energy alone cannot reconstruct the derivative-bearing scale population; the terminal deed must retain viscosity/dissipation, direction transport, or another scale-sensitive constitutive return |
| `proved-derived; formal-checked` | translation difference factors through physical vorticity dissipation | `NavierStokesTranslationDissipation.lean` proves `Σ_i ‖(χ_k(d)-1)ω̂_i(k)‖²_{ℓ²_k} ≤ 3‖d‖² D_ω(t)`: the actual vorticity components enter the complete H¹ coefficient carrier, the Stokes-weighted coefficient sum is identified exactly by Parseval with `periodicVorticityDissipation`, and the translated character difference is controlled through its derivative rather than a global Lipschitz supremum | source-specific composition of exact torus-character differentiation, three-coordinate frequency geometry, smooth-slice Parseval, genuine vorticity descent, and the physical enstrophy-dissipation receiver | insert this L² difference carrier before the reciprocal direction/Hodge collapse and prove the resulting stretching work can be absorbed by the viscous term or controlled by an integrable lower-order coefficient |
| `proved-derived; formal-checked` | physical translation current reconstructed from dissipation | `NavierStokesPhysicalTranslationDissipation.lean` proves translation acts diagonally on the genuine torus Fourier receiver, uses Parseval and the real/complex component chart to identify the complete coefficient mass with `∫|ω(q+y)-ω(q)|²dq`, and returns the centered bound `≤ 27 dist(y,0)² D_ω(t)` | source-specific composition of Haar translation invariance, torus characters, complete Fourier reconstruction, Euclidean component geometry, the centered quotient representative, and the preceding dissipation law | compose this physical `L²` difference current with aligned Hodge-kernel cancellation; the expected remaining receiver is a spatial fourth-power vorticity population or a sharper oriented replacement, not the discarded global Lipschitz scalar |
| `proved-derived; formal-checked` | dissipation enters the complete dyadic Hodge interaction | `NavierStokesDissipationHodgeInteraction.lean` inserts `ω(q-y)-ω(q)` by exact aligned cancellation, bounds the actual absolute kernel-reading population at every scale, glues it through the summable first-distance Hodge moment, and for every `ε>0` proves `Σ_s∫_y∫_q |H_s(y;ω(q),ω(q-y))| ≤ 27 M₁(27D_ω+ε²‖ω‖₄⁴)/(2ε)`; the explicit positive choice `ε=1+729M₁/ν` absorbs the dissipation branch by `(ν/2)D_ω` | source-specific composition of the physical translation current, parameterized Young square completion, exact aligned Hodge cancellation, real/complex coordinate comparison, nonnegative `tsum` gluing, and the complete first-distance kernel moment | attach this integrated high-frequency population and the already energy-paid scale-zero face to the signed physical enstrophy identity; the exposed nonlinear remainder is the exact spatial `L⁴` vorticity mass |
| `proved-derived; formal-checked` | absorbed Hodge interaction enters the signed enstrophy receiver | `NavierStokesDissipationHodgeEnstrophy.lean` integrates the exact finite dyadic word, pays the scale-zero strain by `26244π√(2E)·Enstrophy`, sends the addressed Fourier reconstruction fibre to zero, transports absolute torus stretching through the unit-cube chart to the signed physical vortex-stretching term, and proves `EnstrophyRate ≤ -(ν/2)D_ω + 26244π√(2E)·Enstrophy + C(ν,M₁)‖ω‖₄⁴ + CurlForcingWork` | exact finite reconstruction/gluing, Fubini at each addressed band, compact torus integration, weighted-`H³` tail decay, Haar/cube chart transport, and the periodic enstrophy identity | derive a source-specific time law for the exact spatial `L⁴` population, sharpen it through another oriented difference/scale receiver, or prove that the presently conserved energy and integrated dissipation receivers are insufficient |
| `counterexample; formal-checked` | quartic-amplitude receiver insufficiency | `NavierStokesVorticityFourthPowerAmplitude.lean` proves that the literal scalar action on an actual velocity world-sheet transports curl linearly, kinetic energy, enstrophy, and vorticity dissipation quadratically, the energy/enstrophy base cubically on a positive ray, and torus fourth-power vorticity mass quartically; whenever the source slice has positive fourth-power mass, no fixed pair of coefficients factors every positive-amplitude quartic occurrence through only the quadratic dissipation and cubic energy/enstrophy faces | exact scalar transport through `fderiv`, curl, gradient, compact Haar integration, and an Archimedean quartic-versus-lower-degree separator | this does not preserve the fixed Navier--Stokes equation data under amplitude rebase and does not refute regularity; it proves that a purely algebraic, amplitude-blind receiver cannot close the exposed `L⁴` term, so the next carrier must retain PDE evolution together with scale/time/orientation |
| `proved-derived; formal-checked` | complete official parabolic solution carrier | `NavierStokesParabolicRebase.lean` constructs `uλ(x,t)=λu(λx,λ²t)`, `pλ=λ²p(λx,λ²t)`, `fλ=λ³f(λx,λ²t)`, and the transported initial face; it derives every differential term, proves the one-sided time-derivative law at `t=0`, transports full half-cylinder smoothness, and constructs an actual official `SmoothSolution`; every positive natural cover degree also constructs an actual official `PeriodicSolution`, with its cover index retained | exact chain-rule transport through `derivWithin`, `fderiv`, the second iterated derivative, the canonical-covariant-tensor Laplacian, half-cylinder chart transport, and finite iteration of unit periodicity | the rebase/official-carrier packaging is closed; it preserves existing solutions and exposes their exact scale family, but supplies no new initial-data existence theorem or terminal regularity bound |
| `proved-derived; formal-checked` | parabolic vorticity current and scale-covariant absorption | `NavierStokesParabolicVorticityCurrent.lean` carries the actual curl and every scalar-component gradient through the PDE-preserving rebase, retains the transported spatial cell `λ⁻¹·unitCube`, identifies its derivative-square receiver definitionally with `periodicVorticityDissipation`, and proves exact integrated weights `1`, `3`, and `5` for enstrophy, dissipation, and fourth-power vorticity; consequently a quartic-to-dissipation coefficient transports with weight `2`, and the transported absorption inequality is equivalent to its source inequality; combining the independent amplitude and parabolic actions uniquely forces monomial powers `(1/2,3/2)`, and the resulting exact coefficient `sqrt(Enstrophy·Dissipation)` is proved to have weight `2` | exact curl/gradient chain transport, Haar change of variables on the retained cell, rational solution of the two receiver-weight equations, and the existing periodic viscous-dissipation receiver | the scale address and the only compatible monomial coefficient are now constructed; prove the corresponding source inequality with enough orientation-sensitive improvement for terminal control, or replace the quartic receiver by an oriented critical carrier whose time integral closes the existing restart passage |
| `counterexample; formal-checked` | parabolic scale repetition cannot remove the BKM obstruction | `NavierStokesParabolicCriticalCurrent.lean` composes the complete periodic cover carrier with the genuine torus `L∞` vorticity receiver; the pointwise critical rate carries exactly weight `n²`, the inverse quadratic chronology cancels that weight, the accumulated critical current is identical on source and returned lifespans, and terminal interval-integrability is preserved and reflected | exact periodic solution cover, complete pointwise characterization of the torus norm, inverse spatial-chart reconstruction, totalized open-lifespan receiver, and exact interval change of variables | this closes the scale-current law and proves that cover repetition alone can neither create nor remove critical concentration; the next theorem must retain an additional orientation/depletion or constitutive face that breaks the critical symmetry and yields terminal integrability |
| `proved-derived; formal-checked` | amplitude-normalized direction seam and subcritical current | `NavierStokesParabolicDirectionCurrent.lean` constructs the totalized normalized direction and its signed cross seam; proves magnitude times normalized direction reconstructs the source, the full cross interaction factors exactly into two magnitude faces and the oriented seam, and the real seam is exactly the existing complex cross-difference receiver; a linear direction-coherence law depletes the full cross population, is equivalent across the actual parabolic vorticity rebase with coefficient weight `1`, and its accumulated time current returns with exact weight `-1` | exact norm reconstruction, swing-derived cross bilinearity, real/complex chart transport, actual vorticity parabolic law, inverse spatial-chart reconstruction, and exact chronology change of variables | construct this direction law from the PDE on the high-vorticity source region and feed its two explicit magnitude faces into the existing dyadic Hodge kernel; unlike the weight-two BKM magnitude current, this carrier has a strict scale advantage, but terminal integrability is not yet derived |
| `proved-derived; formal-checked` | direction-depleted physical Hodge modulus | `NavierStokesDirectionDepletionModulus.lean` transports a linear normalized-direction law from the Euclidean vorticity slice to the literal torus cross-difference population; the receiving magnitude remains in the coefficient while the translated source magnitude and torus displacement form one continuous nonnegative modulus; this constructs the existing `OpenPeriodicSpatialCrossModulus` interface and proves the corresponding dyadic Hodge cross mass bound at every scale | exact centered torus representatives, periodic vorticity descent, the normalized real-to-complex cross bridge, physical displacement comparison, and the generic Hodge kernel-moment owner | derive the weight-one coherence coefficient from the PDE on the high-vorticity region, then control and sum the displayed source-magnitude-weighted kernel moments in space-time without replacing them by the critical `L∞` magnitude receiver |
| `proved-derived; formal-checked` | receiver-symmetric high/low vorticity direction gluing | `NavierStokesHighVorticityDirection.lean` proves normalization is exactly `2/m`-Lipschitz on an addressed magnitude-`m` region, bounds its signed cross seam by normalized-direction difference, derives restricted direction coherence from ordinary vorticity variation with coefficient `2L/m`, and proves this coefficient has exact parabolic weight `3-2=1`; it then glues every receiver/source pair without deleting either low complement: high/high uses the direction law, while a low endpoint returns its explicit threshold face; one continuous symmetric `OpenPeriodicSpatialCrossModulus` removes the earlier high-receiver hypothesis and enters every dyadic Hodge scale | exact norm decomposition into vector and amplitude differences, Euclidean cross geometry, positive-threshold reconstruction, centered torus transport, real/complex cross chart, symmetric endpoint case split, and the existing physical Hodge kernel-moment owner | the zero singularity and both low-endpoint complements are closed pointwise; derive a PDE-owned scale-uniform variation law on the dynamically selected high region and prove the symmetric glued kernel moments have a terminally summable spacetime return |
| `proved-derived; formal-checked` | exact direction-threshold balance | `NavierStokesDirectionThresholdBalance.lean` decomposes the symmetric modulus moment at every physical receiver and dyadic scale into a distance-bearing high/high population `A_s` and a low-endpoint population `B_s`, so the Hodge bound is exactly `9((2L/m)A_s+mB_s)`; it proves the complete square identity `a/m+mb-2√a√b=(√a-m√b)²/m`, constructs the positive balanced threshold `m=√a/√b`, proves the cost there is exactly `2√a√b`, and instantiates `L` by the actual canonical vorticity derivative on the common compact chart | exact integral linearity over the compact torus, retained nonnegative moment populations, positive square-root reconstruction, field arithmetic, canonical derivative transport, and the receiver-symmetric high/low carrier | the source-specific spatial variation law and threshold are closed; sum the returned balanced current over scale and then prove its terminal-time integrability |
| `proved-derived; formal-checked` | balanced direction current is summable across Hodge scales | `NavierStokesDirectionBalancedScale.lean` proves the high/high population is bounded by the square of the actual slice-vorticity supremum times the inverse-square-root distance moment, proves the low-endpoint population is bounded by twice that supremum times a uniform zeroth kernel moment, derives the exact fourth-root dyadic identity, and proves the resulting canonical balanced geometric-mean current is summable over every dyadic scale at every strict-interior time and torus receiver | exact compact-Haar integral comparison, the inhabited Hodge distance-moment decay, the returned product-Haar zeroth moment, canonical spatial-vorticity variation, exact square-root threshold balance, and geometric-series gluing | the infinite-depth spatial passage is closed; prove terminal-time integrability of the scale-summed current from the Navier--Stokes evolution and transport that return through the signed enstrophy and restart receivers |
| `proved-derived; formal-checked` | complete large-scale current and strict-interior time transport | `NavierStokesDirectionBalancedTime.lean` glues the balanced direction population into one actual `tsum`, separates a fixed inverse-fourth-root Hodge population from a receiver-independent temporal factor, proves the complete current is bounded by that exact envelope, proves every moment and scale current continuous in strict-interior time, and uses a uniform compact-interval Weierstrass population to prove the actual scale-summed current continuous and interval-integrable on every ordered `[a,b] ⊂ (0,T)` | exact scale summability, compact-Haar parametric integration, continuity of the torus-vorticity supremum and canonical derivative norm, complete `tsum` domination, and compact-interior uniform convergence | all spatial, infinite-scale, and strict-interior time gluing is closed; the source-specific residual is exactly terminal integrability through `T`, which requires an evolution estimate rather than another compact-interior or scale reconstruction theorem |
| `conditional; formal-checked` | critical accumulation terminal current | `NavierStokesTerminalCurrent.lean` turns the genuine nonnegative torus critical-vorticity rate into an oriented accumulated current, proves every finite time partition glues exactly, and proves that an `OpenAccumulatedCriticalVorticityBudget` makes the clipped accumulation monotone and bounded and therefore returns one unique finite terminal accumulated mass and a null terminal current | exact interval integration, monotone left-limit reconstruction, and the existing genuine critical-vorticity budget carrier | the budget is still a hypothesis, and its scalar terminal mass is not a terminal velocity or `H³` state; prove the PDE-owned budget and transport that return through the high-order reconstruction and restart seam |
| `conditional; formal-checked` | signed enstrophy terminal current | `NavierStokesEnstrophyTerminalCurrent.lean` proves on every strand-integrable interior interval that `ΔEnstrophy + ν∫D = ∫Stretching + ∫CurlForcing`; it retains the signed stretching/forcing side as the exterior current, and proves that terminal returns of the three actual accumulated strands reconstruct the exact terminal enstrophy value and put enstrophy in the terminal null cone | exact periodic enstrophy derivative, fundamental theorem of calculus, signed viscous/stretching/forcing decomposition, and the generic terminal-current reconstruction law | construct the terminal strand-return receipt from the PDE.  In particular, the signed scalar vortex-stretching current is not forced null by the scalar critical accumulation theorem, and its source fibre still retains amplitude, orientation, and scale; after that return, lift the enstrophy trace to the source state and compatible restart |
| `counterexample; formal-checked` | interior continuity versus terminal integrability | `strictInteriorContinuousNonnegative_not_sufficient_for_terminalIntegrability` exhibits the nonnegative population `‖(t-1)⁻¹‖`, continuous on `(0,1)` but not interval-integrable on `[0,1]` | Mathlib's exact inverse nonintegrability theorem composed with the norm receiver | any terminal continuation argument must exclude this pole class by a source-specific PDE estimate; no continuity-only promotion is lawful |
| `counterexample; formal-checked` | uniform scale bound versus summability | `NavierStokesVorticityDirectionKernelMoment.uniform_nonnegative_scale_bound_does_not_imply_summable` exhibits the constant nonnegative scale population `1`, uniformly bounded by `1` but not summable | exact real-series counterexample | the completed uniform kernel `L¹` law cannot close the infinite-depth direction carrier without a genuinely decaying localization/moment return |
| `counterexample; formal-checked` | coarse coefficient magnitude | `PrimeRadixAtlas.lean`: the declared intermediate bound faces sum to `412236000 = 2^5*3^3*5^3*11*347`; `347` is absent from both incoming terms and appears after addition | exact natural arithmetic and prime valuation | `420000000` is a rounded enlargement of this intermediate return; the separate `42*10^17` common-magnitude proposal is withdrawn because no complete assembly returns it |
| `proved-derived; formal-checked` | measured difference | `MillenniumDifferenceAtlas.dyadicHodgeSubsetMassExcess`: each subset obligation is exactly `mass - constant·scale ≤ 0`; `NavierStokesDyadicHodgeRemainingSubsetMasses.lean` proves one common constant and all those nonpositive excess returns over every scale `≥3`, all 27 Hodge entries, and all 8 faces | project-specific composition | the excess and restart receivers are closed; the next difference is the critical-vorticity integrability defect |

[proved-derived; formal-checked] The immediate coefficient target is closed.  The exact
zero-exterior prefix gluing reconstructs each removed coordinate with cost `N(N+1) ≤ 72R²`; the
full and `{0,1}` source faces therefore generate all eight scale-correct receiver faces.  The
common returned constant is `72·72·4119133228099520072`, and the named large-scale subset return
and uniform physical dyadic kernel carrier are inhabited without analytic hypotheses.

[proved-derived; formal-checked] The magnitude-only alternative has been falsified, and the
surviving fibre is retained through two exact receivers.  The complete Fourier receiver removes
the finite aperture.  The sharper spatial receiver reconstructs each dyadic strain band as a
convolution, cancels the aligned source at every displacement, retains the lossless oriented cross
difference, pays for its fixed base only through ordinary kinetic energy, and returns a summable
physical distance moment for the actual Hodge kernel.  The physical solution now supplies the
linear torus-distance law itself, and the complete scale population has been integrated into the
unit-cube enstrophy receiver.  The coefficient is the canonical norm of the actual compact spatial
derivative chart; joint smoothness makes it continuous, and hence integrable, on every strict
compact time window.  The curl multiplier kills the fixed Fourier mode, Haar reconstruction
removes the formerly retained anchor, and the actual critical vorticity rate is at most `3/2`
times this canonical derivative rate.  Terminal integrability of that one source population now
constructs the existing compatible continuation carrier directly.  The formal terminal-pole
separator proves that the integral cannot be promoted to `[0,T]` from interior continuity alone.
The remaining local-to-global edge is a PDE estimate excluding terminal concentration of the
canonical derivative rate, or a weaker direction-only source rate whose terminal receiver already
composes with continuation.  The exact single-frequency separator proves that kinetic energy by
itself cannot supply this scale-sensitive return: its order-zero reading stays `1` while the
order-two population escapes every uniform scalar factor.  The new translation law now retains the
missing scale face exactly: the complete actual vorticity translation difference is bounded by
`3‖d‖²` times the physical vorticity dissipation.  The next estimate must carry this L² difference
through the reciprocal direction/Hodge stretching receiver without replacing it by a uniform
derivative norm.

[proved-derived; formal-checked] `HolonicDirectedPassage.lean` now carries the common law at its
correct grain, and `HolonicTerminalCurrent.lean` is its incoming-real-time instance.  An arbitrary
local current returns its exterior current plus the complete composition-defect population; on a
closed path the loop return is exactly that defect ledger.  A state-induced current has zero defect.
Along any declared filter, null current is the exact Cauchy condition; completeness and separation
reconstruct one unique receiver return.  This law is reusable by every Millennium worktrack, but it
becomes a problem solution only after the problem's constitutive current is proved null and its
official receiver consequence is returned.

[conditional; formal-checked] The Navier--Stokes attachment now distinguishes two different
terminal returns.  A finite genuine critical-vorticity budget returns the unique terminal value of
its accumulated scalar mass.  The exact signed enstrophy passage instead returns
`ΔEnstrophy + ν∫D = ∫Stretching + ∫CurlForcing`; terminal traces of those three actual strands
return terminal enstrophy.  The first result does not prove the second.  The shortest open passage
is therefore a PDE-owned factorization from the critical accumulation carrier—or a sharper
orientation/scale carrier—into the signed stretching/dissipation strand return, followed by the
already exposed high-order state reconstruction and compatible restart.

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
| `natEuclideanHolon` / `intEuclideanHolon` | lossless residue--winding charts `ℕ ≃ ZMod m × ℕ` and `ℤ ≃ ZMod m × ℤ` | the complete residue fibre is the nonnegative or signed winding coordinate; equality at the receiver is exact divisibility of the returned difference |
| `ReceiverQuotient` | every declared receiver factors through `q` | complete predecessor fibre; a section is separately declared structure |
| `WeilDivisorLedger` | finite signed population of declared codimension-one loci | inversion negates coefficients; a function quotient subtracts ledgers |
| `CartierDivisorAtlas` | local equations joined by admitted unit transitions | overlap cocycle, reverse transition, and equality of local divisor ledgers |
| `LatticeIndexReceipt` | integer-linear transport with finite cokernel | kernel, image, complete lift fibre, cokernel, exact index, torsion witness, saturation |

[proved-derived; formal-checked] `Foundation/EuclideanResidueTransport.lean` now separates the
arithmetic operations that Lean exposes under neighboring notation.  Natural Euclidean division
returns a nonnegative winding, integer Euclidean division returns a signed winding, `ModEq` states
receiver equality, and `ZMod m` is the quotient carrier that retains only the residue cross-section.
The signed `ediv/emod`, `fdiv/fmod`, and `tdiv/tmod` coordinate conventions are also separated:
floor coordinates equal the Euclidean chart at a positive modulus; truncated coordinates agree on
the nonnegative half-axis but select a different cross-section across the sign seam.  Their actual
admissible coordinate images are retained as Holon targets, and every pair reconstructs its source
exactly.  In the Euclidean product charts the complete reconstruction fibre over one residue is
equivalent to the winding carrier.  Thus `3 mod 8 = 3` means that the residue
receiver returns the face `3`; it does not say the source occurrence has no quotient coordinate.
For source `3` that coordinate is `0`, while every `3 + 8k` occupies the same integer receiver
fibre at signed winding `k`.  The checked sign-seam example returns Euclidean/floor coordinates
`(5,-1)` and truncated coordinates `(-3,0)` for the same source `-3` modulo eight.

[proved-derived; formal-checked] Zero natural residue is equivalent to the existing
`NatFactorWitness`, so scalar divisibility is precisely occupancy of one specialized
multiplication-lift fibre.  No divisor is thereby defined for an arbitrary holon, matrix, tensor,
or geometric body.  Those carriers continue to return inverse information through transport
lifts, kernels, images, cokernels, dual lines, and reconstruction fibres.  Analytic norm modulus,
arithmetic residue modulus, geometric moduli spaces, and signed Weil/Cartier divisor ledgers remain
distinct typed owners until an explicit passage relates them.

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

[proved-derived; formal-checked] `HodgeConstructivePassage.lean` proves that such a compatible
section is exactly an inhabitant of each complete cycle lift fibre.  It constructs the section from
any finite Hodge basis whose vectors have addressed source cycles, and proves the rank-one
codimension-one case from one nonzero algebraic generator.  Thus finite rational gluing and global
cycle reconstruction are closed; Hodge--Riemann positivity and the Hodge-index shell remain useful
separation/coercivity stairs but do not by themselves construct the source basis cycles.

[proved-derived; formal-checked] The universal composition gap is now closed independently of a
finite basis.  `PrimitiveHodgeStep` retains the lower/upper cycle and Hodge transports, their
cycle-class square, the primitive submodule, and an exact returned decomposition of every upper
class.  A lower cycle lift plus a primitive cycle lift is added at source and proved to return the
upper class; `hodgeConclusion_iff_primitiveLiftable_of_lower` proves that primitive liftability is
the exact new obligation, and `primitiveHodgeStaircaseConclusion` carries it through every finite
codimension staircase.

[proved-derived; formal-checked] The primitive obligation has also been converted into an exact
interaction cut.  For a source-specific finite polarized Hodge receiver, the Hodge conclusion is
equivalent to the statement that every nonzero rational Hodge direction has nonzero intersection
with an algebraic class.  On one primitive step,
`PrimitiveAlgebraicInteraction.primitiveLiftable` uses the sharper primitive detector: every
nonzero primitive class interacts nontrivially with an algebraic primitive class.  Its proof makes
the algebraic orthogonal zero, uses polarized nondegeneracy to fill the primitive carrier, and only
then derives actual cycle-class source fibres.  Thus the active universal Hodge cut is no longer
global basis enumeration or another finite product.  It is construction of this algebraic
primitive detector on every genuine smooth-projective carrier.

[proved-derived; formal-checked] `HodgeSmoothProjectiveReceiver.lean` now removes the arbitrary
source *type* from that cut.  The geometric body is an actual smooth complex scheme closed inside
an actual finite-type `Proj`; its complex structure morphism is proper.  Its codimension source is
the tensor rationalization of actual locally finite integral algebraic cycles supported at scheme
points of the required coheight, and its target is the rational dual of genuine singular homology
of the same closed complex-point population.  The analytic carrier supplies only its topology and
the continuity of the identity current into the inherited closed-point Zariski topology; the
closed-point chart is that identity and its bijectivity is derived, not stored.  The former free
rational-Hodge-submodule aperture is now closed:
each realization carries an internal direct-sum decomposition of its complexification into all
`H^{r,2p-r}` components with conjugation exchange, and its rational `(p,p)` carrier is the exact
preimage of the middle component.  Equivalently it is the kernel of a typed quotient receiver
which returns the complete non-middle Hodge defect.  `HodgeSemantics` owns the one complex-dimension
coordinate used by every later Lefschetz passage and isolates the comparison data still to be
constructed: the analytic topology, Hodge splitting, and the geometric cycle-class map;
`Canonical` is the explicit admission predicate for those constructions.
The source-bearing detector returns an actual `CycleLiftFibre` witness together with every nonzero
primitive pairing.  Thus no arbitrary rational module called `CycleSpace`, no independently chosen
Hodge submodule, no Zariski topology mistaken for the analytic topology, and no cohomological range
witness without its source can satisfy the typed skeleton.  However, source typing alone does not
make the linear map geometric: `HodgeSemanticsFaithfulness.lean` formally erases the map while
preserving the source and thereby proves that admitting every such data bundle is insufficient.

[open] Two directions at the universal cycle-class seam remain distinct. The standard
algebraic-to-Hodge direction is now supplied only at irreducible geometric grain by
`FundamentalClassPoincarePassage.irreducibleHodgeFundamentalClass`; finite integral extension,
rationalization, generator reconstruction, and equality of the whole range with the irreducible
span are proved. It remains to construct each closed fundamental current from chart-compatible
complex tangent orientation and Poincare duality. The conjectural reverse direction is exactly one quantified source
law, not another degree census: every nonzero primitive rational `(p,p)` occurrence must have an
actual rational algebraic-cycle antecedent.  `primitive_mem_transportedLowerClasses_iff_eq_zero`
proves that repeated lower Lefschetz transport cannot create such a nonzero primitive antecedent.
`HodgeHolonicCutFalsifier.lean` separately proves that finite dimensionality, exact holonic fibres,
and signed-definite Hodge--Riemann polarization still do not force it.  Consequently no further
finite family, cardinality, sphere power, or renamed detector may be counted as progress on this
edge; the next proof-producing construction must originate the geometric source current itself.

[proved-derived; formal-checked] The tetrahedral sphere model now has a complete finite common-star
homotopy at singular-chain level.  `HodgeRefinedTriangleAffineCarrier.lean` constructs compatible
affine carrier homotopies on every sufficiently refined triangle;
`HodgeTriangleHomotopyPrism.lean` proves internal edge cancellation, vanishing lateral current on
cycles, and an explicit prism current whose boundary is the raw affine-label upper current minus
the iterated refined source.  `trianglePrismHolon_returns_globalBoundary` derives the same result
from the generic finite `BoundaryHolon` local-to-global theorem.  The same owner now proves its
finite upper face receiver is exactly `refinedCyclePointCurrent`, hence closed on cycles and exactly
the measured radial fundamental coefficient after realization.

[proved-derived; formal-checked] Ordered edge normalization is now an actual `BoundaryHolon`:
constant and non-monotone fold triangles are retained as its reconstruction fibre, and its boundary
is exactly raw ordered edge minus finite oriented-edge realization.  Applying these three edge
returns to an ordered label triangle leaves a formally checked closed degree-two normalization
defect.  Separately, the retained omitted-coordinate/prefix carrier constructs the lawful
degree-three affine occurrence and proves its exact four-face singular boundary.

[proved-derived; formal-checked] The shared `OrderedWordChain` owner now supplies the exact free
chain contraction and packages closed apex-prefix filling as `closedPrefixHolon`; no Hodge name is
attached to that algebraic law.  `HodgeLabelEdgeCancellation.lean` proves the other global seam:
the complete alternating edge-correction population factors through the refined source boundary
and vanishes on every source cycle.

[proved-derived; formal-checked] `HodgeLabelWordContraction.lean` closes the fixed-chart receiver
transport: the complete normalization defect is a closed free ordered-word current in one retained
omitted-coordinate chart, its geometric prefix is an explicit singular filler, and the free and
geometric boundary squares commute.  `HodgeCommonStarNormalization.lean` sums those fillers over
the common-star family, cancels the full correction seam on cycles, and composes refinement,
common-star prism, and normalization into a current with boundary
`q • sphereFundamentalCandidate - z`.  `HodgeSphereHomologyEquivalence.lean` descends that law
through the homology quotient and proves the finite tetrahedral realization bijective onto genuine
rational singular `H₂(S²)`.

[proved-derived; formal-checked] `HodgeProductMixedFilling.lean` now expresses the two factor
directions through one polarized operation: second-factor transport is first-factor transport
conjugated by `flipPair`, and the graded flip derives the opposite contractions and boundary laws.
`HodgeProductRulingDecomposition.lean` uses that owner to prove an exact degree-three boundary
witness from every product two-cycle to a rational combination of the two geometric rulings.  It
then proves `rulingHomologyMap_surjective` and combines the existing injectivity into
`rulingHomologyEquivalence : Bidegree ≃ₗ[ℚ] H₂(S²×S²;ℚ)`.  All three terminal declarations
audit to `propext`, `Classical.choice`, and `Quot.sound` only.

[proved-derived; formal-checked] The frozen product-validation residual is closed.
`HodgeProductSingularCohomologyDual.lean` transports the ruling equivalence to the actual
projective-line product and dualizes it through the fixed-factor/varying-factor pairing; its
explicit swap law recovers the geometric divisor intersection form.
`HodgeSurfaceCycleClass.lean` maps actual rational ruling divisors to those functionals, proves
their `1/0/0/1` evaluations on the varying-factor singular ruling basis, and proves the exact
cellular-to-singular cycle-class square.  `HodgeProjectiveLineType11Form.lean` independently
constructs the Fubini--Study area form as a smooth closed differential two-form, proves
type-`(1,1)` invariance and inversion gluing, and returns unit winding with its rational integral
realization.
`HodgeSurfaceType11Period.lean` uses one indexed factor operation to construct both surface
currents, defines `rationalType11` as their analytic period range, derives that this range is all
degree-two rational singular cohomology, identifies its basis periods with the singular divisor
classes, and proves `surfaceType11Conclusion`.  Every audited terminal theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

[open] The Hodge frontier is no longer this surface.  A lawful next deed must strictly enlarge the
admitted family while preserving actual cycle sources, singular cohomology, analytic `(p,p)` type,
intersection, and reconstruction fibres—for example a product/hyperplane closure whose conclusion
is derived componentwise.  A nonzero official quotient class remains both the exact falsifier and
the insufficiency witness for any proposed enlargement that loses a global class.

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

[counterexample; formal-checked] The coefficient gate is closed, while the local
curl/divergence receiver has been proved too coarse: two admitted trace-free jets with the same
curl return opposite stretching signs.  The deeper analytic gate is now the exact periodic
Hodge/Biot--Savart strain reconstruction and its direction-difference cancellation.  That enriched
receiver must either yield critical-rate integrability or return a source-specific obstruction;
the maximal-time globalization follows only after such a return.

[proved-derived; formal-checked] That enriched spatial passage is now complete.  The actual smooth
vorticity slice supplies a linear torus-distance cross modulus, the exact Hodge distance moments
are summable over every dyadic scale, the reciprocal direction chart cancels into vorticity square,
and the result reaches both `periodicVortexStretching` and `periodicEnstrophyRate` with no spatial
summability or uniform-Jacobian premise.  The returned coefficient is

```text
(13122*pi)*sqrt(2*kineticEnergy(t))
  + 729*vorticityLipschitzConstant(t)*totalDyadicHodgeDistanceMoment.
```

[proved-derived; formal-checked] The coefficient is now the canonical norm of the complete compact
derivative chart and is continuous on `(0,T)`.  More sharply, the curl multiplier proves the actual
vorticity zero mode vanishes.  Probability-Haar reconstruction and centered torus transport then
prove

```text
criticalVorticityRate(t) <= (3/2) * canonicalVorticityDerivativeRate(t).
```

Thus terminal integrability of the canonical derivative rate constructs the exact critical
integral and the already formalized compatible continuation.  No additional anchor or low mode is
left in that comparison.

[open] The remaining Navier--Stokes gate is the terminal PDE estimate itself: prove this canonical
derivative rate interval-integrable on `[0,T]` for every admitted maximal open solution, or derive
a weaker source rate which still majorizes the critical receiver and whose integral follows from
energy, viscosity, direction coherence, or another exact constitutive law.  Strict-interior
continuity alone is formally insufficient.  The exact axial-frequency separator additionally
rules out any direct uniform factorization through kinetic energy alone.

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

[proved-derived; formal-checked] The Navier--Stokes sequence now carries the physical translation
difference through aligned Hodge cancellation, every dyadic scale, the vanishing reconstruction
fibre, the unit-cube chart, and the signed enstrophy identity.  Positive viscosity absorbs one half
of the actual vorticity dissipation.  The exact remaining nonlinear receiver is the spatial
fourth-power vorticity population, beside the kinetic-energy/enstrophy base and forcing work.  The
amplitude audit now proves that no fixed algebraic coefficients can factor every positive scalar
rebase of that quartic population through only the quadratic dissipation and cubic
energy/enstrophy faces.  Because a scalar rebase need not preserve the fixed Navier--Stokes data,
this is a receiver-insufficiency theorem rather than a Clay alternative.  The exact parabolic
transport now supplies the missing PDE-owned scale/time passage: all momentum terms carry the
same cubic factor and official incompressibility is preserved.  On the simultaneously transported
cell, actual enstrophy, component-gradient dissipation, and fourth-power vorticity carry exact
weights `1`, `3`, and `5`; hence a linear quartic-absorption coefficient must carry weight `2`, and
the resulting transported inequality is equivalent to its source occurrence.  The unresolved
carrier boundary is no longer exponent bookkeeping or solution packaging.  The independent
amplitude and parabolic equations uniquely force the monomial powers
`Enstrophy^(1/2)·Dissipation^(3/2)`; equivalently the coefficient of one exposed dissipation factor
is `sqrt(Enstrophy·Dissipation)`, and its weight-two transport is now proved.  The actual BKM
receiver has now also been transported through every positive natural cover: its pointwise rate
has weight `2`, its accumulated current is exactly invariant after the quadratic time fold, and
terminal interval-integrability is an iff between source and return.  Thus repeated scaling is
formally proved insufficient to consume the obstruction.  The remaining edge is an
orientation-sensitive depletion or constitutive return which breaks this critical symmetry and
forces the accumulated current to be finite.  The amplitude-normalized direction seam now
supplies the first exact such carrier: its orientation face has weight zero, a linear spatial
coherence coefficient has weight one, and its accumulated current has weight minus one.  The
source-specific residual is to derive that coherence law on the dynamically relevant vorticity
region and compose its retained magnitude faces through the existing dyadic Hodge kernel.

1. **Navier--Stokes:** the generic terminal null-cone/reconstruction law and the genuine critical
   accumulation attachment are now proved, and the exact signed enstrophy exterior current is
   isolated.  Construct from the PDE either the accumulated critical-vorticity budget itself or a
   sharper orientation/scale carrier, then prove that it returns the dissipation,
   vortex-stretching, and forcing strands at maximal time.  Transport that terminal return through
   the high-order state reconstruction and compatible restart.  The passage may not discard the
   scale address exposed by the quartic-versus-lower-degree separator.
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

[proved-derived; formal-checked] The compression/phase-transition source synthesis, exact retained
cycle seam, rational fractal restriction law, cyclic diffraction cutting law, and direct
Millennium consumption audit are deposited in
`research/records/2026-08-28_COMPRESSION_RETURNS_CYCLE_SEAMS_PHASE_INTERFACES_AND_EXACT_FRACTAL_RECEIVER_FIBRES.md`.
