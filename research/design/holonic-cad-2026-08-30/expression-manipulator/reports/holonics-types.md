# Holonics typed glossary (read-only survey, 2026-08-30)

Path prefixes used below (all paths absolute once expanded):
- `L/` = `/home/b/Workspaces/holonics/soma/formal/elementary-holonics/ElementaryHolonics/`
- `LR/` = `/home/b/Workspaces/holonics/soma/formal/elementary-holonics/`
- `R/` = `/home/b/Workspaces/holonics/crates/`

Format of every row: `Name — fields — meaning — path:line`. Meanings are the source's own doc-comment, condensed to one line. Nothing was built or modified.

---

## A. Lean (formal vocabulary)

### A.0 Foundation base carriers used by the parametron files

| Name | Fields | Meaning | Where |
|---|---|---|---|
| `AddressedPassage X Y` | `Occurrence : Type`, `source : Occurrence → X`, `target : Occurrence → Y` | passage retaining the occurrence population that carries it, with two boundary maps | `L/Foundation/Lineage.lean:25` |
| `.Fibre P x y`; `.Join P Q`; `.comp`; `PassageEquiv` | `{o // source o = x ∧ target o = y}`; `left, right, joins : P.target left = Q.source right`; `Occurrence := Join P Q`; `occurrence ≃, source_exact, target_exact` | carrying occurrences; pullback witness; serial composition; passage equality | `Lineage.lean:31,56,65,75` |
| `AdditiveFace X := X →₀ ℤ`; `incoming/outgoing/additive/joinedMiddleBoundary` | — | oriented ±1 endpoint faces | `L/Foundation/AddressedBoundary.lean:23-39` |
| `boundary_join`, `boundary_comp`, `boundary_compAssociator`, `boundary_passageEquiv`, `additiveBoundary_shadow_forgets_the_carrier` (thms) | — | pullback cancels the joined middle face (Stokes-type); outer faces kept; `Rel.comp` is the forgetful shadow | `AddressedBoundary.lean:44-76` |
| `Holon Source Target Face` | `Occurrence : Type`, `source`, `target`, `receive : Occurrence → Face` | addressed occurrence population + receiver current per occurrence | `L/Foundation/Holon.lean:32` |
| `Holon.toPassage`, `.ReconstructionFibre face` (`{o // receive o = face}`), `.Interaction` (= `Join`), `.comp`, `.cartesian`, `.diagonal`, `.offDiagonal` (`{p // p.1 ≠ p.2}`), `.CompositeReconstructionFibre`; thms `compReconstructionFibreEquiv`, `cartesianReconstructionFibreEquiv`, `interaction_middle_boundary` | — | serial/Cartesian/diagonal bodies; composite fibres retain both component fibres; joined middle face = 0 | `Holon.lean:48-173` |
| `BoundaryHolon Chain Current` | `Occurrence`, `source target : Occurrence → Chain`, `receive : Occurrence → Current`, `boundary : Current →+ Chain`, `returnsBoundary : ∀ o, boundary (receive o) = target o − source o` | holon whose current has an additive boundary realizing `target − source`; `.map/.toHolon/.comp/.totalCurrent` | `Holon.lean:182-263` |
| `BoundaryHolon.boundary_totalCurrent` (thm) | `boundary totalCurrent = totalTarget − totalSource` | exact finite local-to-global law | `Holon.lean:268` |
| `TransportLift`/`ReconstructionFibre transport target`; `LiftObstruction {outsideRange}` | `{s // transport s = target}` | complete lift population; proof the fibre is empty | `L/Foundation/TransportLift.lean:21,27,49` |
| `LatticeIndexReceipt Source Target` | `transport : Source →ₗ[ℤ] Target`, `finiteCokernel : Finite (Target ⧸ range)`; `.kernel/.image/.Cokernel/.index/.cokernelTorsion/.SaturatedByImage` | integer-lattice transport; lift exists ⇔ in image ⇔ cokernel class 0 (`:65,76`); saturation ⇔ torsion witness (`:100`) | `L/Foundation/LatticeTransport.lean:29-135` |
| `Compression ι X Q Y` | `quotient : X → Q`, `receiver : ι → X → Y`, `factor : ι → Q → Y` | receiver-exact quotient | `L/Foundation/Receiver.lean:90` |
| `ReceiverTransformer`; `ReceiverInsufficiency`; `ReceiverCondensation` | `transform : Set.range entering → Returned`; `left right, sameEntering, differentReturned`; `left right, distinctEntering, sameReturned` | functional transformer on presented faces; insufficiency witness; lawful many-to-one | `Receiver.lean:123,163,181` |
| `DifferenceReceiver X A S` | `chart : X → A`, `read : A → S` | enter an additive chart, read its difference | `L/Foundation/MeasuredDifferenceReceiver.lean:26` |
| `ReceiverQuotient`, `QuotientSection` (`choice`, `rightInverse`) | — | named compression; a section selects one source per fibre | `L/Foundation/ReceiverQuotient.lean:26,45` |
| `ComparisonCell P Q` / `ReceiverDefect` | `left right`, `source_exact` / `separates` | two parallel routes at one source; receiver sees them differ | `L/Foundation/ComparisonCell.lean:20,38` |
| `BoundaryScalePassage` | `fineBoundary`, `coarseBoundary`, `interiorTransport`, `boundaryTransport`, `boundary_natural` (commuting square) | grain transport commuting with boundary formation; `transport_boundary`, `comp_transport_boundary` | `L/Foundation/BoundaryScalePassage.lean:16,44,82` |
| `PartitionReceipt` | `pieceOf`, `boundaryPiece`, `mate` (involutive, fixed-point-free), `hand : Side → ℤ`, `mate_reverses_hand` | exact partition with paired oriented cut sides; `pairedBoundaryCancels` | `L/Foundation/ExactPartition.lean:27,66` |
| `Current Occurrence` (`→₀ ℚ`), `Simplex`, `DiagonalOccurrence`, `TotalOne/Two/ThreeOccurrence` | — | rational chains on simplicial sets; `1×2` vs `2×1` kept distinct | `L/Foundation/DiagonalChainTransport.lean:27-115` |
| `Word α n`, `Chain R α n` (`→₀ R`); `CycleFilling {fill, boundary_fill}` | — | word chains; source-retaining filler ⇒ `exactAt` | `OrderedWordChain.lean:20,23`; `CycleFilling.lean:26` |
| `BoundaryReceiver` (thms) | `not_mem_range_of_receiver_boundary_eq_zero`, `zero_receiver_not_visible` | boundary-annihilating receiver with nonzero reading separates cycle from boundary image | `BoundaryReceiver.lean:35,48` |
| `Presented {presentation, value}`; `ProductFace {trail, leftSection, rightSection}`; `ExactRadixChart {depth, residual, decomposition, maximal}`; `FractalPacking.Cell {lower, upper : ℚ}` | — | presentation ≠ denotation; Leibniz leaf; exact radix; rational one-cell | `Presentation.lean:63`; `HigherDifferenceTransport.lean:67`; `PrimeValuationRadixAtlas.lean:53`; `FractalPacking.lean:28` |

Foundation files (26, 7744 lines): AddressedBoundary, BoundaryReceiver, BoundaryScalePassage, ComparisonCell, CoordinateHaarMomentReceiver, CoordinateHaarReceiver, CoordinateSubsetReceiver, CycleFilling, DiagonalChainTransport, EuclideanResidueTransport, ExactPartition, FractalPacking, HigherDifferenceAnnihilator, HigherDifferenceScaleDescent, HigherDifferenceTransport, Holon, LatticeTransport, Lineage, MeasuredDifferenceReceiver, OrderedWordChain, Presentation, PrimeValuationRadixAtlas, ProductDegreeTwo, Receiver, ReceiverQuotient, TransportLift.

### A.1 `Millennium/HolonicParametron.lean` (274 lines) — namespace `Soma.Holonics.Millennium.HolonicParametron`

| Name | Definition | Meaning | Line |
|---|---|---|---|
| `phaseCarrier phase : ℂ` | `exp(phase·I)` | phase carrier in the complex receiver | 23 |
| `halfTurnSheet phase` | `phase + π` | second locked sheet | 27 |
| `pumpStorage strength pumpPhase carrierPhase` | `−strength·cos(2·carrier − pump)` | averaged pump-storage face; doubled phase leaves the two sheets degenerate | 32 |
| `binaryPhase : Bool → ℝ` | `false ↦ 0`, `true ↦ π` | the two locked representatives | 68 |
| `spinFace : Bool → ℝ` | `false ↦ 1`, `true ↦ −1` | sign receiver of a locked phase (locked-state quotient face) | 73 |
| `windingLogI n : ℂ` | `(π/2 + 2πn)·I` | `n`-th logarithmic winding above `i` | 96 |
| `logarithmicWindingHolon : Holon ℤ ℤ ℂ` | `Occurrence := ℤ`, `source n := n`, `target n := n+1`, `receive n := exp(windingLogI n)` | winding index / next turn / returned face `i` | 117 |
| `logarithmicWindingReconstruction` | `ReconstructionFibre I ≃ ℤ` | every branch retained behind the one face | 128 |
| `structure IPowerReceiverFace` | `logarithmicCurrent : ℂ`, `exponentialFace : ℂ`, `powerCurrent : ℂ` | branch-resolved complex winding current | 176 |
| `iPowerIChartHolon : Holon ℤ ℤ IPowerReceiverFace`, `iPowerIHolon : Holon ℤ ℤ ℂ` | as above with `windingIPowerI n` | exact winding lift of `i^i` | 182, 201 |
| `phaseCoupling w φ₁ φ₂` | `−w·cos(φ₁−φ₂)` | cosine lattice coupling | 219 |
| `isingCoupling w s₁ s₂` | `−w·spinFace s₁·spinFace s₂` | signed edge after the locked receiver | 223 |
| `phaseNetworkEnergy edges weight phase`, `isingNetworkEnergy` | sums over `Finset (ι×ι)` | finite coupled population before/after the sign quotient | 235, 242 |

Theorems: `pumpStorage_halfTurnSheet` (36), `phaseCarrier_halfTurnSheet` (46), `phaseCarrier_binaryPhase` (78), `phaseCarrier_fullTurn_fibre` (84, receiver not injective), `exp_windingLogI` (100), `logarithmicWindingHolon_hasDistinctOccurrences` (138), `windingIPowerI_eq` (156), `phaseCoupling_binaryPhase` (227), `phaseNetworkEnergy_binaryPhase` (250: phase energy descends exactly to Ising energy on the locked population).

### A.2 `Millennium/HolonicComplexParametron.lean` (637 lines) — THE Complex Parametron carrier

Type variables `{Node Branch : Type*}` (line 28). Header claim `[proved-derived]` (7): oriented incidence, reversal invariance of diagonal storage, two-sided sign action on mutual tables; no spectral completeness/damping/Floquet/hardware theorem (16-17).

| Name | Definition / fields | Meaning | Line |
|---|---|---|---|
| **addressed nodes / oriented ports** `source target : Branch → Node` | parameters of `endpointIncidence` and every holon | branch endpoints as addressed nodes | 390, 453 |
| **oriented incidence** `incidence : Branch → Node → ℝ` | parameter | branch–node incidence map | 33 |
| `branchDrop incidence state branch : ℝ` | `∑ node, incidence b n · state n` | real drop presented by an oriented branch | 33 |
| `orientationSign selected branch` | `if selected then −1 else 1` | sign action reversing selected branch charts | 38 |
| `reorientIncidence selected incidence` | row reversal | chart change, not a physical intervention | 42 |
| `endpointIncidence source target : Branch → Node → ℝ` | `[n = target b] − [n = source b]` | exact signed incidence between two addressed nodes | 390 |
| **storage pullback** `diagonalStorage weight incidence state` | `½ ∑ b, weight b · (branchDrop b)²` | energy stored independently on branches (`weight` = C or L⁻¹) | 66 |
| `coupledStorage coupling incidence state` | `½ ∑∑ coupling b₁ b₂ · drop b₁ · drop b₂` | mutual quadratic storage before phase locking | 296 |
| `mutualBranchContribution source target coupling state pair` | one `(b₁,b₂)` term of the above | occurrence-level mutual storage | 499 |
| **receiver constitutive form** `diagonalResponse weight incidence state node` | `∑ b, weight b · incidence b n · drop b` (= `Bᵀ D B v`) | diagonal nodal response | 86 |
| `coupledResponse coupling incidence state node` | `∑ b₁, incidence b₁ n · ∑ b₂, coupling b₁ b₂ · drop b₂` (= `Bᵀ M B v`) | mutual nodal response | 188 |
| `IsGeneralizedMode stiffness capacity incidence ω² mode : Prop` | `mode ≠ 0 ∧ ∀ n, stiffnessResponse = ω²·capacityResponse` | generalized finite LC mode `K v = ω² C v` | 115 |
| `IsCoupledGeneralizedMode stiffness capacity …` | same with full `Branch → Branch → ℝ` tables | mutual eigenproblem | 274 |
| **lattice coupling** `coupling : Branch → Branch → ℝ`; `reorientCoupling selected coupling` | `sign b₁ · coupling b₁ b₂ · sign b₂` (= `S M S`) | two-sided sign transport of a mutual table | 182 |
| `driveAction drive incidence state`, `reorientDrive` | `∑ b, drive b · drop b` | work pairing of an addressed branch drive | 138, 143 |
| **complex coefficient current** `complexBranchDrop incidence (state : Node → ℂ) branch : ℂ` | `∑ n, (incidence b n : ℂ) · state n` | real incidence presenting a complex phasor section | 352 |
| `complexDriveAction (drive : Branch → ℂ) incidence state : ℂ` | `∑ b, drive b · complexBranchDrop b` | complex receiver of a branch-drive population | 357 |
| **relative phase** `phaseDrive amplitude phase branch : ℂ` | `amplitude b · phaseCarrier (phase b)` | phase-labelled complex drive per branch | 362 |
| `phaseSuperposition amplitude phase : ℂ` | `∑ b, phaseDrive …` | arbitrary relative phases retained before the two-sheet receiver | 373 |
| `structure ParametronReceiverFace` | `complexCurrent : ℂ`, `diagonalContribution : ℝ` | one branch receiver retains complex current and diagonal storage | 443 |
| **the holon** `complexParametronHolon source target weight drive realState complexState : Holon Node Node ParametronReceiverFace` | `Occurrence := Branch`; `source`, `target`; `receive b := { complexCurrent := drive b · complexBranchDrop (endpointIncidence …) complexState b, diagonalContribution := ½·weight b·(branchDrop … realState b)² }` | pre-locking Complex Parametron as a holon: branches = occurrences, endpoint maps = oriented ports, paired receiver = complex phase current + diagonal constitutive contribution | 452-463 |
| `mutualParametronHolon source target coupling state : Holon (Node×Node) (Node×Node) ℝ` | `Occurrence := Branch × Branch`; `receive := mutualBranchContribution` | interacting occurrence body of constitutive pairs | 507 |
| `diagonalMutualParametronHolon` | `Occurrence := Branch`, ports `(s b, s b)`/`(t b, t b)`, `receive b := … (b,b)` | self-coupling face: one occurrence on both axes, not a serial chain | 519 |
| `offDiagonalMutualParametronHolon` | `Occurrence := {p : Branch×Branch // p.1 ≠ p.2}` | genuinely two-occurrence body; no symmetry quotient (orientation may differ) | 532 |

Theorems (`#print axioms` audited, 624-637): `branchDrop_reorient` (53), `diagonalStorage_reorient` (71), `diagonalResponse_reorient` (94), `isGeneralizedMode_reorient_iff` (123), `driveAction_reorientIncidence/_reorientBoth` (147, 160), `coupledResponse_reorient` (196), `coupledResponse_reorientIncidence` (243: incidence reversal with fixed table = `S M S` in the old chart — the chart-vs-physical distinction), `isCoupledGeneralizedMode_reorient_iff` (283), `coupledStorage_reorient/_reorientIncidence` (304, 334), `phaseDrive_halfTurn`, `phaseSuperposition_halfTurn` (366, 377), `branchDrop_endpointIncidence` (397: drop = `state target − state source`), `complexBranchDrop_endpointIncidence` (415: same without collapsing phase), `complexParametronHolon_receive_complexCurrent` (466), `complexParametronHolon_totalComplexCurrent` (476: `∑ receive.complexCurrent = complexDriveAction`, by `rfl`), `complexParametronHolon_totalDiagonalContribution` (485), `offDiagonal/diagonalMutualParametronHolon_receive` (542, 551), `mutualParametronHolon_totalReceiver` (576: `= coupledStorage`), `mutualParametronHolon_totalReceiver_diagonal_offDiagonal` (597: exact partition diag ⊕ offDiag of the occurrence population).

### A.3 `Millennium/HolonicMeasuredParametron.lean` (211) — namespace `…HolonicMeasuredParametron`

| Name | Definition | Meaning | Line |
|---|---|---|---|
| `measuredCapacitance charge voltage s t` | `differenceRatio charge voltage s t` (`C = ΔQ/ΔV`) | coefficient as returned comparison between two occurrences | 30 |
| `measuredInductance`, `measuredInverseInductance`, `measuredImpedance`, `measuredAngularFrequency` | `ΔΦ/ΔI`, `ΔI/ΔΦ`, `ΔV/ΔI`, `Δθ/Δt` | same | 35-50 |
| `branchDifferenceReceiver incidence branch : DifferenceReceiver (Node→ℝ) ℝ ℝ` | `chart := branchDrop incidence · branch`, `read := id` | branch drop as a typed difference receiver | 98 |
| `measuredCapacityField`, `measuredStiffnessField : Branch → ℝ` | branchwise measured C / L⁻¹ | | 128, 136 |
| `IsMeasuredGeneralizedMode … : Prop` | `IsGeneralizedMode (stiffnessField) (capacityField) incidence (ω_measured)² mode` | LC mode after every scalar has been returned from differences | 145 |
| `binaryActionFace action s t` | `binaryExponentialFace (action s) (action t)` | binary phase selection as normalized exponential quotient of one action difference | 181 |

Theorems: `measuredCapacitance_mul_voltageDifference` (56), `measuredInverseInductance_mul_fluxDifference` (65), `measuredCapacitance_add_chartZeros` (74), `measuredAngularFrequency_add_chartZeros` (85), `branchDrop_stateDifference` (105), `branchDifferenceReceiver_returnedDifference` (118), `isMeasuredGeneralizedMode_reorient_iff` (158), `binaryActionFace_eq_logisticDifference` (186), `binaryActionFace_add_common` (193).

### A.4 `Millennium/HolonicMembraneActionTransport.lean` (306)

| Name | Fields | Meaning | Line |
|---|---|---|---|
| `structure AddressedMembraneContact Occ ExtB IntB ExtP IntP Current` | `occurrence`, `exteriorBoundary`, `interiorBoundary`, `exteriorPotential`, `interiorPotential`, `transport : ExtP →+ IntP`, `admittance : IntP →+ Current` | one caused crossing from exterior to interior boundary occurrence | 41 |
| `.returnedPotential` (`interior − transport exterior`), `.returnedCurrent` (`admittance returnedPotential`), `.receiverFace receiver`, `.reconstructionFiber receiver reading : Set Contact` | — | drop in the interior target fibre; constitutive current; reading fibre | 63-83 |
| `finiteCrossEntropy reference emitted` | `−∑ ref·log emitted` | scalar receiver | 157 |
| `structure FiniteCrossEntropyReceiver Action Index` | `reference`, `emitted : Action → Index → ℝ`, nonneg/normalized/positive proofs | probability chart for one action population; `.face`, `.reconstructionFiber` | 163-180 |

Theorems: `receiverFace_factors_through_returnedCurrent` (90), `membraneCurrent_rebase` (104), `localMembraneMixing_reorient` (131), `localMembraneMixing_zero_of_couplingRow_zero` (142), `same_fibre_of_equal_face` (189), `no_successor_factor_of_equal_face` (198), `distinct_sections_equal_crossEntropy` (228), `tailCrossEntropyReceiver_equalFace` (271), `tailCrossEntropyReceiver_no_identitySuccessorFactor` (277), `binaryNormalizedExponential_commonShift` (285).

### A.5 `Millennium/HolonicTorusParametronRealization.lean` (471)

Cell carrier (`Millennium/HolonicPolygonalTorusCarrier.lean`): `MajorIndex m := Fin (m+1)` (32), `MinorIndex n := Fin (n+3)` (35), `inductive Vertex | core | boundary` (46), `inductive Edge | coreLongitude | longitude | meridian | radial` (52), `inductive Face | crossSection | boundarySquare | radialLongitude` (61), `Cell3 | wedge` (69), `Chain α := α →₀ ℤ` (74), `edgeBoundary`, `boundaryOne`, `boundaryTwo` (77, 90, 154), `longitudeWindingChain`, `meridianWindingChain` (120, 124), `dualCrossSectionCut`, `evaluateCochain` (191, 198).

| Name | Definition | Meaning | Line |
|---|---|---|---|
| `ParametronNode m n := Vertex m n`, `ParametronBranch := Edge` | abbrevs | vertices = nodes, edges = branches | 32, 35 |
| `cellularIncidence edge node : ℝ` | `(edgeBoundary edge node : ℤ)` cast | signed cellular boundary as the real incidence matrix | 39 |
| `chainDrive chain : Branch → ℝ`; `chainDrivePassage : AddressedPassage (Chain Branch) (Branch → ℝ)` | `AddressedPassage.graph chainDrive` | integer chain into real branch coords, retaining the chain | 71, 86 |
| `BranchSection := Branch → ℝ` | — | | 163 |
| `crossSectionCurrent cut current`, `crossSectionCurrentLinear/AddHom` | `∑ e, current e · dualCrossSectionCut cut e` | exact current through one declared cut | 167-283 |
| `fluxLinkage winding flux`, `fluxLinkageLinear/AddHom` | `∑ e, flux e · chainDrive winding e` | linkage against a retained winding chain | 216-291 |
| `crossSectionCurrentFibreEquivKernel`, `fluxLinkageFibreEquivKernel` | `ReconstructionFibre … ≃ ker` | fibre is a kernel translate; no inverse selected | 300, 312 |
| `CurrentFluxOccurrence := BranchSection × BranchSection`; `currentFluxReceiver`, `currentFluxPassage` | pairs `(cut current, linkage)` | paired receiver as an addressed passage | 326-338 |
| `branchProbe probe : BranchSection` | indicator | one addressed branch probe | 352 |
| `crossSectionCurrentInsufficiency cut i : ReceiverInsufficiency …` | `left := 0`, `right := meridianWindingChain i` | cut current alone identifies zero and a meridian | 407 |

Theorems: `branchDrop_cellularIncidence_eq_endpointDifference` (56), `chainDrive_injective` (76), `cellularIncidence_sum_eq_boundaryOne` (98), `driveAction_chainDrive_eq_boundaryPairing` (112, discrete integration by parts), `driveAction_chainDrive_eq_zero_of_boundaryOne_eq_zero` (126), `crossSectionCurrent_chainDrive_eq_cast_evaluateCochain` (182), `crossSectionCurrent_longitudeChain_eq_one`/`_meridianChain_eq_zero` (199, 207), `fluxLinkage_exactDrop_eq_driveAction` (232), `currentFluxPassage_retains_occurrence` (344), `cutAndProbeReceiver_separates_zero_meridian` (425).

### A.6 `Millennium/HolonicFourTorusParametronRealization.lean` (192)

Carrier (`HolonicFourTorusCarrier.lean`): `Direction := Fin 4` (27), `AxisIndex g := Fin (g+1)` (30), `Vertex g := Direction → AxisIndex g` (33), `structure Edge g {direction, base}` (69), `structure Face g {first, second, first_ne_second, base}` (75), `Chain` (83), `edgeBoundary/boundaryOne/boundaryTwo` (86-115), `dualAxisCut` (158), `axisCycleRealization : Lattice → Chain (Edge g)` (218), `axisCycleReceiver` (222).

Defs: `ParametronNode/ParametronBranch` (26, 29), `cellularIncidence` (32), `chainDrive` (50), `axisCrossSectionCurrent direction cut current` (96), `fourAxisCurrentReceiver current : Direction → ℝ` (118), `fourAxisCurrentPairing probe current` (137). Theorems: `branchDrop_cellularIncidence_eq_endpointDifference` (41), `chainDrive_injective` (54), `cellularIncidence_sum_eq_boundaryOne` (62), `driveAction_chainDrive_eq_boundaryPairing` (75), `axisCrossSectionCurrent_chainDrive_eq_cast_evaluateCochain` (101), `fourAxisCurrentReceiver_realization` (130: four cuts reconstruct every period coefficient), `fourAxisCurrentPairing_realization` (142: `= cyclePairing`), `…_T1_A1/_T2_A2/_T0_M0` (150-168, monodromy covariance).

### A.7 `Millennium/HolonicRankFourWindingRealization.lean` (273)

`DoubledWinding m n := Fin 2 → Chain (ParametronBranch m n)` (28); `rankFourWindingRealization cycle` (33: `![c₀·longitude + c₁·meridian, c₂·longitude + c₃·meridian]`); `rankFourCoefficientReceiver : DoubledWinding → Lattice` (41); `rankFourWindingPassage : AddressedPassage Lattice DoubledWinding` (72); `rankFourCurrentFluxReceiver : DoubledWinding → Fin 2 → ℝ×ℝ` (91); `IsDoubledTwoBoundary` (178); `doubledBoundaryReceiverInsufficiency : ReceiverInsufficiency IsDoubledTwoBoundary id` (229). Theorems: `rankFourCoefficientReceiver_realization` (54, left inverse), `rankFourWindingRealization_injective` (66), `rankFourCurrentFluxReceiver_realization` (113), pairing `_T1_A1/_T2_A2/_T0_M0` (140-158), `rankFour_basis_one/three_isDoubledTwoBoundary`, `zero/two_isNot…` (187-217).

### A.8 `Millennium/HolonicDiscreteInduction.lean` (442)

`NodeSection/EdgeSection/FaceSection g` (45-47); `faceCirculation emf face` (50); `structure InductionGrain g {fluxBefore, fluxAfter : FaceSection, emf : EdgeSection, faraday : ∀ face, faceCirculation emf face = −faceFluxDifference …}` (79); `SatisfiesFaradayHistory` (122); `nodeDivergence` (150); `structure ContinuityGrain g {chargeBefore, chargeAfter, current, source, balance}` (191); `IsEddyCurrent` (223); `structure ConductiveInductionGrain extends InductionGrain {conductance, current, currentLaw}` (228); `periodBivector : LatticeEnd` (290); `AxisCoupling := Direction → Direction → ℝ` (341), `axisFluxLinkage`, `inducedAxisEmf` (344, 349). Theorems: `faceCirculation_eq_boundaryPairing` (55, finite Stokes), `faceCirculation_exactDrop_eq_zero` (62), `emf_ne_exactDrop_of_fluxDifference_ne_zero` (97), `faradayHistory_telescopes` (129), `sum_nodeDivergence_eq_zero` (170, divergence theorem), `ContinuityGrain.globalBalance` (201), `periodBivector_is_A1/A2/M0_invariant` (299-307), `inducedAxisEmf_reorient` (397).

### A.9 `Millennium/HolonicDiscreteMaxwellOperator.lean` (1044)

| Name | Fields / def | Meaning | Line |
|---|---|---|---|
| `cellularCurl g : EdgeSection →ₗ[ℝ] FaceSection`, `cellularCoCurl g` | curl = evaluate on face boundary; co-curl = transpose | coordinate Maxwell incidence pair | 94, 112 |
| `structure PositiveCellHodge g` | `edgeWeight : Edge → ℝ`, `faceWeight : Face → ℝ`, `_pos` | positive finite-cell Hodge datum; `.edgePairing`, `.facePairing`, `.coCurl` (= `M₁⁻¹ Bᵀ M₂`), `.fieldEnergy`, `.boundaryPower` | 182-579 |
| `inductive CellMeasureOrigin g` | `primalEdge | dualEdge | primalFace | dualFace` | addressed quantity origin | 401 |
| `structure PositivePrimalDualCellGeometry g` | `primal/dualEdgeMeasure`, `primal/dualFaceMeasure : → ℚ`, positivity | exact primal/dual cell measures; `toPositiveCellHodge` | 408, 477 |
| `structure MidpointMaxwellHistory hodge` | `faceToEdge : FaceSection →ₗ EdgeSection`, `electric magnetic current : ℕ → …`, `faraday`, `ampere` | midpoint Maxwell transport; `.energy`, `.outwardBoundaryPower`, `.sourceWork`, `.toCurrentBalance` | 619-649 |
| `structure CellHodgeScalePassage fineHodge coarseHodge` | `edgeTransport`, `faceTransport`, `curl_natural`, `coCurl_natural`, `edgePairing_natural`, `facePairing_natural` | scale passage preserving curls and pairings; `.comp` | 695, 819 |
| `CurlFibre/CoCurlFibre`, `curlFibreEquivKernel` | | reconstruction fibres | 929-950 |
| `structure CellularMaxwellHistory g` | `permeability`, `permittivity` (+pos), `electric`, `magnetic`, `faraday`, `ampereMaxwell` | vacuum cellular history; `.toVacuumMaxwellPassage` | 957, 972 |

Theorems: `cellularCurl_adjoint` (153), `PositiveCellHodge.adjoint` (253), `…CurlCurl_pairing_nonneg` (330, 337), `edge/facePairing_self_eq_zero_iff` (344, 369), `poynting_balance` (594), `MidpointMaxwellHistory.localBalance/telescopes/closed_material_sourceFree_conserves` (641, 656, 672), `transport_curl/coCurl`, `fieldEnergy_natural`, `edge/faceTransport_injective` (720-757), `exactDrop_mem_cellularCurl_kernel` (936), `electric/magnetic_secondDifference` (986, 993).

### A.10 `Millennium/HolonicGranularBoundaryRadiation.lean` (479)

| Name | Fields | Meaning | Line |
|---|---|---|---|
| `structure GranularBoundaryBody Scalar Cell Face Ridge Port` | `constitutive : Matrix Cell Cell`, `innerBoundary : Matrix Face Cell`, `outerBoundary : Matrix Ridge Face`, `portTrace : Matrix Port Face`, `boundary_boundary : outer * inner = 0` | finite granular body with interior constitutive response, two successive boundaries, port family | 45 |
| `.interiorCurrent`, `.boundaryRadiation`, `.outerReturn`, `.reflectedBoundaryPotential`, `.reflectedActionPotential`, `.portRadiation`, `.jointPortKernel` | — | radiation = cycle; transpose incidence = reflected pullback | 61-168 |
| `reconstructionFiber receiver face : Set Source` | | | 197 |
| `structure CausalGrain Source Index Face` | `signature : Source → Index → Face` | particle identity = complete receiver-history signature; `.signatureSetoid`, `.Particle` (quotient), `.particle`, `.reconstructionFiber` | 248-287 |
| `structure CausalGrain.Passage fine coarse` | `respects : fine.signature l = r → coarse.signature l = r` | coarsening exists only by factorization; `.map`, `.comp` | 294-317 |
| `completeReceiverHistoryGrain`, `restrictedReceiverHistoryGrain`, `completeToRestrictedPassage` | | | 341-378 |
| `structure CausalBoundaryGranulation …` | `causal : Passage`, `boundary : BoundaryScalePassage`, `realizeFine`, `realizeCoarse`, `realization_natural` | causally founded granulation commuting with boundary | 415 |

Theorems: `outerReturn_eq_zero` (79), `boundary_pairing_eq_reflected_interior_pairing` (108, finite Stokes), `same_portRadiation_iff_difference_mem_jointPortKernel` (175), `separated_surface_cannot_factor_through_coarse_receiver` (203), `particle_eq_iff_signature_eq` (275), `map_comp` (322), `coarse_grain_equality_with_fine_separation_returns_reconstructionFiber` (391), `radiation_natural` (448).

### A.11 `Millennium/HolonicTorusEntropyParametronEquivalence.lean` (108) and `HolonicTorusMonodromyReceiver.lean` (178)

`realizedWindingCurrent g cycle : ParametronBranch g → ℝ` (30); `windingLatticeEquivRealizedParametronCurrent g : Lattice ≃ {current // ∈ range}` (55). Theorems: `fourAxisCurrentReceiver_realizedWindingCurrent` (36), `realizedWindingCurrent_injective` (43), `entropyAxisCrossCurrent_realizedWindingCurrent` (63), `all_realizedEntropyAxisCrossCurrents_zero_iff_aligned` (80).

`cyclePairing probe cycle : ℤ := dotProduct` (27), `cyclePairingAddHom` (31), `latticeActionAddHom/Equiv` (38, 44), `T1/T2/T0CycleEquiv : Lattice ≃+ Lattice` (89-101), `receiverFibreCovariance sourceTarget sourceProbe targetProbe natural value : ReconstructionFibre … ≃ ReconstructionFibre …` (108), `T1/T2/T0ReceiverFibreEquiv` (141-157). Theorems: `cyclePairing_covariant_of_inverseTranspose` (62), `cyclePairing_T1_A1/T2_A2/T0_M0` (71-83).

### A.12 Computation

`Computation/HolonicOrientedSiteTransport.lean` (279): `structure OrientedPortSiteTransport Scalar Site Incidence Port {depart : Port → Matrix Incidence Site, arrive : Matrix Site Incidence}` (34; two maps so endpoint orientation is not erased); `.localTransport port := arrive * depart port` (48), `.pairCurrent port state target source := state source · localTransport target source` (52), `.returnedSiteCurrent` (sum over source, 57), `.portCurrent` (sum over target, 62), `.portPotentialSection : Port → Scalar` (67), `.returnedSiteSection : Port → Site → Scalar` (72), `.ecology : FiniteLocalCurrentEcology …` (100); `structure ConservedRealizationCurrent {boundaryKernel : MarkovKernel ProbSite (ProbPort × ProbSite)}` (163); `postContractionPortMass := ∑ normSq` (233). Theorems: `portCurrent_eq_sum_returnedSiteCurrent` (83), `ecology_step_eq_returnedSiteCurrent` (109), `ecology_inferWord_append` (126), `sum_portMass_eq_one` (184), `postContractionPortMass_eq_norm_joined_current` (240), `norm_before_linear_join_is_not_postContraction` (258).

`Computation/ErosAthenaNeuralObjects.lean` (210): `structure AthenaRestedEcology Site Carrier Morphology Generator Receiver Face RestIdentity Ingress Egress {body : FiniteLocalCurrentEcology …, restingMorphology, restingState : Site → Carrier, restIdentity, remount, remount_exact, ingress : Ingress → Generator × (Site → Carrier), egress}` (23); `structure SoulkillerReturn Spool Witness Insufficiency {spools, coldWitness, insufficiency}` (66); `structure SpoolAdmission {admit : Spool → Generator}` (72); `structure ErosCultivationPassage parent Difference {returnedDifference, returnMorphology, childMorphology, child_is_return, morphology_changed, childIdentity, witnessGenerator, witnessReceiver, witnessState, changed_later_conduct, ablate, ablation_exact}` (100); `.child` (139); `complexParametronEcology … : FiniteLocalCurrentEcology Site ℂ …` (174). Theorems: `infer_after_remount` (51), `child_rest_changed` (152), `ablation_returns_parent_rest` (155), `cultivation_has_behavioral_separator` (161), `complexParametronEcology_step` (186).

`Computation/SituatedMachineLearning.lean` (183): `structure SituatedLearningReturn Body Exterior Difference LossFace {difference : Body → Exterior → Difference, lossFace : Difference → LossFace, returnMorphology : Difference → Body → Body}` (26); `IsInferenceReturn`, `IsCultivationAt`, `ReturnDescendsThroughLoss` (38-53); `complexConstitutiveStep`, `realAffineStep`, `realCurrentFace := .re` (117-125); `fixedRealPhaseChart gain : DynamicReceiverChart Unit Unit ℂ ℝ ℝ` (132); `classicalPotential`, `retainedQuadrature : ParametronReceiverFace → ℝ` (154, 158). Theorems: `cultivation_excludes_inference` (46), `equalLoss_differentReturn_obstructsDescent` (68), `scalarLossDoesNotDetermineCultivation` (105), `fixedRealPhaseChart_everyRecurrence` (144), `equalClassicalPotential_canRetainDifferentQuadrature` (162).

### A.13 Geometry (8 files, 1596 lines)

Files: CrossRatio (`RatioPresentation K {num, den}`:17), DivisorAtlas (`WeilDivisorLedger := PrimeLocus →₀ ℤ`:27, `PrincipalDivisorSystem {divisor, divisor_one, divisor_mul}`:50, `CartierAtlas`:83, `CartierDivisorAtlas {atlas, principal, admittedUnit_has_zero_divisor}`:122), Gyrogroup (`class Gyrogroup {op, zero, inv, gyr, …loop}`:27), SixSphereExceptionalData (`A2CellOrbit`:96, `EllipticFilling | orderThree | orderFour`:124, `CuspToricInput`:172, `LogarithmicFillingInput {index, action, twist, …}`:188), SixSphereMonodromy, SixSpherePeriods, SixSphereTorusFibre, Telescoping.

SixSphere/Torus fibre in three lines: (1) `SixSphereMonodromy` checks the integral rank-four monodromies `T1,T2,T0` and dual actions `A1,A2,M0` on `Lattice := Fin 4 → ℤ`, `LatticeEnd := Matrix (Fin 4) (Fin 4) ℤ` (`L/Geometry/SixSphereMonodromy.lean:26-94`). (2) `SixSpherePeriods` gives `PeriodPoint {τ μ β : ℂ}` (`:36`) and period matrices; `SixSphereTorusFibre` builds `ComplexTorusFibre p := ℂ² ⧸ periodLattice p` (`:107`), `AdmissiblePeriodPoint {point, upper : 0 < τ.im, negativeDefect : D point < 0}` (`:318`), `AdmissibleTorusFamilyTotal := Σ p, AdmissibleTorusFibre p` (`:342`) with generator lifts. (3) `SixSphereExceptionalData` supplies finite toric-cusp and logarithmic-filling inputs; the header states no holomorphic functions, compactness, gluing, or identification with `S⁶` is constructed (`SixSphereTorusFibre.lean:24-29`).

### A.14 Umbrella, DerivationAtlas, catalog

`LR/ElementaryHolonics.lean` (842 lines) is purely `import` lines (no declarations): Foundation (24), Computation (6), Algorithm (2), Geometry (8), RH (22), Millennium (many, incl. the twelve parametron files at lines 91-112), then Navigation/Paying/Coupling/MillenniumCoupling/Pivots (116-120).

`LR/DerivationAtlas.lean` (462) — Lean executable, namespace `Holonics.DerivationAtlas`, header (6-17): "Lean parses, elaborates and kernel-checks a source occurrence; the executable exports the resulting typed expression graph, declaration bodies, source-linked term occurrences, and before/after proof-state events … no such view is part of Lean's truth authority." Entry structures (all `deriving ToJson`):

```lean
structure ExpressionFace where            -- :77
  renderedExterior : String
  leanStructuralHashExterior : String
  rootNode : Nat
structure ExpressionNode where            -- :83
  index : Nat
  kindExterior : String
  faceExterior : String
  children : Array Nat
structure ExpressionUse where             -- :90  node, parentNode, childPosition, count
structure LocalStanding where             -- :103 index, freeOccurrenceExterior, userFaceExterior, binderFaceExterior, kindFaceExterior, type, value
structure GoalFace where                  -- :113 goalOccurrenceExterior, userFaceExterior, localStanding, target
structure TermOccurrence where            -- :120
  sequence : Nat
  parentDeclarationExterior : String
  startByte : Nat
  stopByte : Nat
  elaboratorExterior : String
  syntaxExterior : String
  expression : ExpressionFace
  expectedType : Option ExpressionFace
structure ProofEvent where                -- :131 sequence, parentDeclarationExterior, startByte, stopByte, elaboratorExterior, syntaxExterior, before after : Array GoalFace
structure DeclarationOperation where      -- :142
  declarationExterior : String
  moduleExterior : String
  kindExterior : String
  type : ExpressionFace
  definingValue : Option ExpressionFace
  bodyReferencesExterior : Array String
structure AtlasBundle where               -- :151
  schema : String                         -- "holonics.derivation-atlas.v2" (:437)
  sourcePathExterior moduleExterior declarationModulePrefixExterior : String
  expressionNodes : Array ExpressionNode
  expressionUses : Array ExpressionUse
  declarationOperations : Array DeclarationOperation
  termOccurrences : Array TermOccurrence
  proofEvents : Array ProofEvent
  syntaxAndNamesAreExterior : Bool        -- true
  kernelChecked : Bool                    -- true
  truthStatus : String                    -- "established-bounded"
```

Two entry constructions verbatim (no emitted bundle is checked into the tree; `output/` was removed):

```lean
-- TermOccurrence, DerivationAtlas.lean:329-338
pure {
  sequence := terms.size
  parentDeclarationExterior := parentFace context
  startByte
  stopByte
  elaboratorExterior := term.elaborator.toString
  syntaxExterior := term.stx.reprint.getD (toString term.stx)
  expression := ← expressionFace standing term.expr
  expectedType := ← term.expectedType?.mapM (expressionFace standing)
}
-- DeclarationOperation, DerivationAtlas.lean:401-408
returned := returned.push {
  declarationExterior := name.toString
  moduleExterior
  kindExterior := constantKind info
  type := typeFace
  definingValue := definingValueFace
  bodyReferencesExterior := bodyReferencesExterior info
}
```

CLI: `derivation_atlas --input FILE [--module-prefix MODULE] [--output FILE]` (`:417`). `LR/M6CausalReturn.lean` (366) is a sibling exporter with the same `DeclarationOperation` shape plus a `CausalReceipt` (`:115-128`).

`LR/MILLENNIUM_FORMAL_CATALOG.md` headings (1115 lines): 1 Purpose and provenance discipline; 2 Measured station inventory; 3 Shared holonic theorem surface (3.1, 3.2); 4 Riemann hypothesis; 5 Birch–Swinnerton-Dyer; 6 Hodge; 7 Navier–Stokes; 8 Yang–Mills; 9 Poincaré and P vs NP; 10/10a/10b corrective difference atlas, prime/radix faces, transport lifts & lattice quotients; 11 Holonics is the source catalog; 12 candidate solution conditions (12.1–12.7); 13 Recurrence of recurrence and the derivation atlas; 14 matching-logic supplement; 15 active exterior closure goal; 16 maintenance rule; 17 evidence records.

---

## B. Rust (runtime vocabulary)

### B.1 `R/holonic-structure/src` (`#![no_std]`, 3344 lines) — "Production-owned structural carriers for exact holonic computation" (`lib.rs:1`)

| Name | Top-level fields | Meaning | Where |
|---|---|---|---|
| `BranchForkReceipt` | `shared_events: usize` | fork point count | `branch_lineage.rs:7` |
| `BranchLineage<T>` | `tip: Option<Arc<BranchNode<T>>>` (node: `prior`, `event`, `extent`) | holonic ancestry by pointer + count | `:24` |
| `ChainEnd<E>` | `Continues(E) | Terminates(E)` | open/closed end with testimony | `chain.rs:59` |
| `Unconnected<N,E>` | `at, attempt: N, reflected: E` | what did not connect | `:80` |
| `Disposition` | `Untouched | Saturated | Reached` | | `:95` |
| `Chain<N,L,E>` | `nodes: Vec<N>, links: Vec<L>, head: ChainEnd<E>, tail: ChainEnd<E>, unconnected: Vec<Unconnected>` | both-ends-open chain retaining failures | `:107` |
| `Face<S,R>` | `scalar: S, relation: R` | scalar face whose relation stays askable | `face.rs:29` |
| `TrivialGauge` / `DeclaredGauge<T>` | `ActedTrivially{members} | ExtentDisagrees{before,after} | NoMaterial` / `before, after: Vec<T>, moved: Vec<usize>` | declared re-indexing witness | `gauge.rs:44,58` |
| `CountedCrossing` | `incident: u64, transmitted: u64` (both nonzero) | junction count | `junction.rs:54` |
| `GrowingKeyAtlas<K,V>` | `nodes: SparseOrdinalAtlas<KeyNode>, root: Option<u64>, len` | keyed map over the ordinal atlas | `keyed_atlas.rs:58` |
| `LocalSet<T>` / `LocalQueue<T>` / `LocalSequence<T>` | `members: Vec<T>` / `members: Vec<Option<T>>, head` / `members: Vec<T>` | local populations | `local_population.rs:36,276`; `local_sequence.rs:19` |
| `trait CausalMembrane` | `type Standing; type Occurrence<'a>; type Return; type Error; fn standing; fn receive_occurrence` | one atomic receiving contract | `membrane.rs:7` |
| `SparseOrdinalAtlas<T>` | `pages: Vec<OrdinalPage<T>>, extent: u64, occupied` | paged ordinal store (page/offset never identity) | `ordinal_atlas.rs:86` |
| `Hand` | `Cohere | Anti | Ortho` | link hand that gates | `relating.rs:33` |
| `trait Relating` | `type Weight; type Transport; reach(); hand(); transport()` | a link carries reach that weighs and hand that gates | `:71` |
| `trait Composes` | `type Defect; type Remainder; identity(); compose()` | | `:111` |
| `LocalRelations<K,V>`, `RelationSpan {start,len: u64}`, `FrozenRelationBuilder`, `FrozenRelationAtlas {rows: Box<[Relation]>}` | | relation rows, frozen spans | `relation_atlas.rs:40,226,242,291` |

### B.2 `R/relational-geometry/src` — "Exact, receiver-relative geometry … no Bevy, glam, rendering scalars" (`lib.rs:1-5`)

`model.rs`: ids `FrameId, RelationId, EntityId, ConstraintId` (`pub struct X(pub u64)`, macro `:24`); `LocalChart {origin: RatVec3, basis: [RatVec3;3], labels}` (46); `LocalFrame {id, name, rank, chart}` (105); `HingeAxis {X,Y,Z}` (114); `FrameRelationKind { Declared{law} | Hinge{pivot_in_target, axis, parameter} }` (131); `FrameRelation {id, name, source, target, forward: AffineMap3, kind}` (143); `ConicSpecies` (160); `ProjectiveConic {center, axis_u, axis_v, species}` (179); `Geometry { Triangle{vertices} | Conic | Thread{vertices, closed} }` (292); `GeometryEntity {id, name, frame, geometry}` (327); `ConstraintKind { SharedVertex | PointOnConic | Declared }` (335); `Constraint` (353); `Construction {schema, frames, relations, entities, constraints, next_*}` (360); `TransportError`, `ConstructionError` (380, 403).

`projection.rs`: `ReceiverId(u64)` (20); `ProjectiveRatio {numerator, denominator: BigInt}` (60); `ExactSpin {components: [BigInt;4]}` (144); `ReceiverOrientation {spin}` (269); `ReceiverGauge {anchor, reference: RatVec3}` (330); `ProjectionLaw { Orthographic | PerspectiveRay{focal_distance} | StereographicNorth | Isometric }` (345); **`Receiver {id, name, frame, orientation, projection, gauge, route_overrides: BTreeMap<FrameId, Vec<RelationId>>}`** (380); `ProjectedPoint {exact: ExactVec2, rational: Option<RatVec2>, receiver_point, depth}` (413); `ProjectedPolyline/Entity/ChartLine/ChartLabel/ChartField` (423-466); `ReceiverMetric` (469); `TriangleFaceSignature` (478); **`Crossing {first_entity, first_segment, second_entity, second_segment, point, first_depth, second_depth, over_entity, orientation_sign: i8}`** (1034); `CrossingAnalysis {crossings, discriminants, exact, boundary}` (1047); errors `ProjectionError` (488), `ProjectionDiscriminant` (1024).

`receiver_topology.rs`: ids `SourceVertexId/DiagramNodeId/DiagramEdgeId/DiagramFaceId` (23-32); `SourceEndpoint {entity, vertex}` (35); `SourceSegmentAddress {entity, segment}` (41); `SourceVertex {id, members, receiver_point}` (47); `SourceSegment {address, from, to}` (54); `DiagramNodeKind { SourceIncidence{source} | ApparentCrossing{first, second, over, orientation, …parameters} }` (61); `DiagramNode {id, point, kind}` (81); `DiagramEdge {id, source, from, to, screen_parameter_start/end}` (88); `DiagramDart {edge, forward}` (100); `DiagramFace {id, boundary: Vec<DiagramDart>, signed_double_area, bounded}` (106); `ExactMultiGraph {vertex_count, edges}` (121); `ExactPolynomial {coefficients: Vec<BigInt>}` (127); `IharaSignature {reciprocal, primitive_oriented_cycles}` (220) + cross-check/frame readings (244-313); `TopologyDiscriminant` (316); **`ReceiverTopology {receiver, receiver_name, source_vertices, source_segments, nodes, edges, faces, source_graph, face_dual_graph, source_ihara, face_dual_ihara}`** (354).

`decorated_path.rs`: `SourceDartAddress {segment, forward}` (35); `CrossingRole {Over, Under}` (41); `ReceiverCrossingMark {source_parameter, screen_point, other_branch, role, crossing_orientation}` (47); `ReceiverDartFace {receiver, receiver_name, screen_origin, screen_target, chord squares, intervals, crossings}` (70); **`JointCausalDart {id, address, origin, target: SourceVertexId, source_frame, source_chord_squared, ordered_source_cuts, receiver_faces}`** (84); `ExactTurn {parallel, transverse: Rat}` (102); `DecoratedTransition {id, incoming, outgoing, through, receiver_faces}` (153); `ReceiverClosedTrace {…, closed_return: ExactTurn}` (164); `JointDecoratedPathOperator {schema, receivers, source_segments, darts, transitions, primitive_traces}` (185).

`receiver_atlas.rs`: `OccurrenceId(u64)` (22); `MarkedOccurrence {id, name, frame, point}` (25); `ReceiverGrain {width, height}` (49); `PixelCell/PixelAperture/ApertureAddress` (134-151); `GrainedReceiver {receiver, grain}` (166); **`SwingCell {id, name, pivot: [OccurrenceId;3], witness: OccurrenceId}`** (172); `ReceivedOccurrence {occurrence, name, projected, aperture}` (182); `ReceivedSwing {cell, cross_ratio}` (190); `ReceiverAtlasFace {receiver, receiver_name, grain, occurrences, swings, crossings}` (196); `JointSwing {cell, name, receiver_values, invariant}` (212); `GrainComparison {first, second, indistinguishable_at, distinguished_at, unaddressed_at}` (221); `JointReceiverAtlas {schema, faces, occurrences, swings, grain_comparisons}` (236); emanations (257-279); `CrossRatioRefusal` (616).

`scene.rs`: `LabScene {construction, receivers, primary_receiver, bookmarks}` (18); `SceneMoment {ordinal, label, scene}` (53); `SceneArchive {schema, moments, cursor}` (60).

`eta_atlas.rs`: `Field {Eta, ZetaPrime}` (78), `FieldJet {value, derivative: ComplexInterval}` (90), `Edge {start, start_value, end, end_value}` (181), `BandReceipt {ordinal, config, winding}` (556), `ZeroLineage {ordinal, config, root, refinements, final_receiver, midpoint_current}` (575), `EtaRatioAtlas {schema, arithmetic, source_function, receiver_law, symmetry_read, apparatus, scan, config, grain_bits, max_depth, physical_workers, elapsed_milliseconds, bands, zero_lineages, interval_relations, reciprocal_moments}` (600), `SaddleAtlas` (1213).

### B.3 `R/holonic-engine/src` (170 `pub mod`; crate: "Exact causal execution and receiver-relative visibility … no window, camera, raster pipeline, physics package, floating-point scalar" `lib.rs:1-5`)

Twelve central carriers with fields:

1. **`AddressedCurrentSection`** `{boundary_state: Option<u32>, quadratic_weight: BigUint, factor_current: Vec<(u32, BigUint)>}` — exact weighted integral current on a founded incidence population — `addressed_current.rs:19`. **`AddressedCurrentOccurrence`** `{source_section, generator, target_section: u32}` (49). **`AddressedCurrentPassage`** `{schema, factor_population, generator_population, source: Vec<Section>, target, generator_targets, occurrences}` — carries every `(source, generator)` to one target section, retains both boundary maps and the reconstruction fibre (140). Generated-port variants: `AddressedGeneratedPortSlot {port, generator, source_boundary_state, boundary_state, restriction}` (61), `…CurrentOccurrence {source_section, selected_slot, target_section, removed_scale}` (72), `…CurrentPassage` (91), `…JunctionOccurrence/Passage` (107, 121; adds `presented_current`).
2. **`NativeParametronCell`** `{native: NativeStateId, section: ExactComplexWaveCurrent, current: ExactComplexWaveCurrent, relative_phase: ExactUnitConicPhase, hand: NativeThreadHand}` — runtime image of the Lean parametron receiver face — `native_spool.rs:74`. `NativeThreadHand {Along, Against}` (66); `NativeConstitutiveResponse {native, receiver, presented, stored}` (86); `NativeMutualConstitutiveResponse {left/right_occurrence, left/right_native, receiver, storage: Rat}` (97); `NativeIncidenceTerm {occurrence, from, to, coefficient: i64}` (57); `NativeThreadOccurrence {occurrence, predecessor, entering_port, emitting_port: OccurrencePort, entering_native, emitting_native}` (45).
3. **`NativeThread`** `{schema, address, entering_boundary, emitting_boundary: BoundaryId, entering_carrier, emitting_carrier, occurrences, native_support, incidence, parametrons, constitutive_responses, chronology: Vec<InputId>, receiver_consequences, obstruction, open_exterior, reconstruction_fibre: BTreeSet<EventId>}` — retains the full occurrence span of one passage — `native_spool.rs:128`. **`NativeSpool`** `{schema, address, native_population, receiver_family, generator_family, threads, serial_pullbacks, generator_descents, receiver_factors, mutual_constitutive_responses, reconstruction_fibres, shortest_separators, interchanges, open_exterior}` (358). `ReceiverInsufficiency {schema, at_occurrence, native, retained_fibre, cause: ReceiverInsufficiencyCause}` (2298).
4. **`OccurrencePort`** `{event: EventId, hand: PortHand{Input,Output}, ordinal}`; `InteractionBond {source, target: OccurrencePort}`; `InteractionPattern {id, name, boundary: BoundaryId, temporality: {CarriesPrecedence|CoPresent}, bonds, receiver_scope}` — `interaction.rs:22-70`.
5. **`Holon` (Lean) ↔ Rust `ReceiverHistoryCompression`** `{schema, source_population, native_population, quotient: Vec<QuotientAssignment{source, native}>, receiver_factors: Vec<ReceiverFactor{native, receiver, observation}>, generators: Vec<GeneratorSquare{generator, source: Vec<SourceTransport>, native: Vec<NativeTransport>}>, reconstruction_fibres: Vec<ReconstructionFibre{native, sources}>, first_separators, construction_work}` — the coarsest receiver/history quotient as a native codec (commuting square `q∘T_i = U_i∘q`) — `receiver_history_compression.rs:127` (`NativeStateId(u64)`:40).
6. **`CausalBodyStanding`** `{schema, incidence: GradedCausalComplex, active_cells, active_by_grade, cofaces, openings: BTreeMap<CausalOpeningId, CausalBoundaryOpening>, connections, holonomy_generators, receivers, fields, used_events, last_chronology, next_opening}` — event-indexed, boundary-closed exact causal body — `causal_body.rs:159`. `CausalBoundaryOpening {id, boundary_grade, boundary: CausalChain, origin, founded_by, last_changed_by, state, receiver_measures}` (96); `CausalConnectionTransport {carrier, source, target, forward, reverse: ExactLinearMap, founded_by}` (114); `CausalHolonomyGenerator {chord, source, loop_boundary, ordered_steps, transport}` (130).
7. **`ReceiverGrainComplex`** `{schema, incidence: GradedCausalComplex, witnesses: BTreeMap<CausalCellId, HolonicCellWitness>}` (`holonic_complex.rs:100`); `HolonicCellWitness { PhaseGerm | PhaseTransport | PhaseClosure | QuotientedComplex }` (83); `HolonicCellAddress {grain: ReceiverGrainId, cell}` (38); `HolonicQuotient {id, caused_by, source_apex, source_closed_hull, target}` (137) — grade (boundary rank) vs grain (observation).
8. **`Lattice`** `{links: BTreeMap<u64, Link{id, tail, head}>, plaquettes: Vec<Plaquette{id, walk: Vec<OrientedEdge>}>}` (`lattice_gauge.rs:547`); `GaugeConfiguration {lattice, connection: StructureConnection}` (659); `ExactSpectrum {extent, characteristic, rational_eigenvalues, unresolved, intervals}` (908).
9. **`DiffusionComplex`** `{schema, nodes: BTreeMap<CurrentNodeId, DiffusionNode{node, capacity}>, branches: BTreeMap<CurrentBranchId, DiffusionBranch{branch, source, target, conductance}>}` (`diffusion.rs:62`); `DiffusionCurrent {branch, source, target, current, transferred}` (153) — implicit exact transport `M φ = n + s + τ ∂j`.
10. **`ExactRatMatrix`** `{rows, columns, entries: Vec<Rat>}` (`exact_linear.rs:52`); `LinearFactorization {rows, columns, rank, kernel, image, cokernel_annihilator, work}` (767); `RebaseReceipt { Rebase{inverse, …} | Refused{factorization, reason} }` (817).
11. **`ResidentSection<'chart>`** `{surface: &ResidentSurface, lo, hi: DeviceBuffer<i64>, rows, width, grain: ResidentGrain, octets}` — interval section resident on the card (`resident_section.rs:530`); `DyadicEnclosure {lo, hi, grain}` (390); `ResidentPassage {surface, origin: Stream, …, schedule, graph_census, exec: GraphExec}` (5016); `PassageReading {slots, obstruction: ObstructionLineage, census_before/after}` (5080); `FrontPassage<'chart> {surface, grain, schedule, reverse_fronts, declared_faces: BTreeSet<EventId>}` — operation diagram compiled into one graph (`front_passage.rs:1098`).
12. **`EvolutionShape`** `{schema, boundaries: CategoryPresentation, chronology: CausalDiagram, laws, occurrences, interactions, next_*}` (`evolution.rs:35`); `CategoryPresentation {schema, objects: BTreeMap<BoundaryId, BoundaryObject{id,name}>, arrows: BTreeMap<ArrowId, BoundaryArrow{id,name,domain,codomain}>}` (`category.rs:33`).

Other named modules: `graded_complex_form.rs` — canonical octet codec of `GradedCausalComplex` (`:1`); `presentation.rs` — plural receiver assembly and terminal finite presentation: `ReceiverStandingRelation {receiver, source_event, into_presentation: RatMat3}` (35), `TerminalMatrixSpec {width, height, boundary}` (506), `ExactCell {lower, upper: [Rat;2]}` (554), `ExactSurfacePresentation {schema, specification, cells, …}` (776); `live_presentation.rs` — multicore realization of caused receiver faces (`TerminalTile`:24, `LiveCpuPresenter<T>`:110); `display.rs` — `Rgb8`, `DisplayFace {schema, width, height, pixels}`, `DisplayPatch` (13-32); `exact_value.rs` — `ExactValue { Integer | Rational | Algebraic(AlgebraicRoot) | CertifiedSeries | Expression }` (813); `exact_work.rs` — `ExactWork {additions, multiplications, divisions, entries_written, cumulative_bits, peak_bits}` (77); `interchange.rs` — `Interchange { Interchangeable | Ordered{because} }` (264), `InterchangeCertificate {schema, predecessor, staged, orders, all_rebased, conduct_agrees, endpoints_agree, identified_agrees}` (309); `gluing.rs` — `Cover {left, right}`, `GluingReading {left, right, overlap, union: RebaseInvariants}` (59, 80); `generative_transport.rs` — `ParameterizedTransportModel {schema, extent, capacities, edges: Vec<GeneratedTransportEdge{edge, symmetric_coupling, skew_coupling}>, reactions, species}` (257); `inverse_transport.rs` — `PotentialTransportEdge {left, right}`, `TransportQuery {imposed_potential, receiver}` (46, 65).

### B.4 `R/holonic-language/src/lib.rs` (932 lines)

Owns: "Exact reflective runtime beneath learnable surface codecs … defines no universal syntax and no semantic token" (`:1-14`). Pub items: ids `FaceId, CodecId, ContinuationId, ReflectionId, ReceiverId` (29-41); `ContinuationState` (44); `CodecVersion<Program, Contact>` (52); `ReflectiveContinuation<Environment>` (67); `ReflectionState`, `ReflectionFrame` (82, 89); `ReflectiveRuntimeError` (99); `CodecStep<Env, Emission>` (130); `CodecObstruction` (148); `trait ReflectiveCodecExecutor<Program, Environment, Face>` (153); `CodecEmission`, `CodecCrossingError`, `CodecRevisionRefusal`, `CodecLineageRefusal` (170-194); `ReflectiveRuntimeRestReceipt`, `ReflectiveRuntimeRest` (202, 213); `ReflectiveRemountRefusal` (236); `ReflectiveRuntime<Program, Environment, Face, Contact>` (244) with `found_face`, `mount_codec`, `open_continuation`, `receive_with`, `revise_and_resume`, `into_rest`/`from_rest`, `resume_unchanged`, `mount_codec_with_lineage`, `revise_and_resume_with_lineage`, `recruited_codecs` (271-845).

### B.5 Lean ingestion / projection

- `R/holonic-engine/src/lean_development.rs` (2400): parses Lean **source text** (not kernel output). `read_development(text, grain: DeclarationGrain{OneArtifactOneDeclaration | EveryTopLevelDeclaration}) -> DevelopmentReading` (1867); emits `DevelopmentReading {grain, declarations: Vec<DeclaredForm>, unopened: Vec<UnopenedDeclaration>, commentary, preamble, scoping: BTreeMap<String,u32>, ambiguous_short_names}` (366); `DeclaredForm {former, name, anonymous, namespace_path, statement, recruited: BTreeMap<String,u32>, tactics, local_bindings, steps: Vec<ProofStep>, line}` (220); `ProofStep {former, cohort, focus, binder, statement, recruited, column, line}` (193); projections `derivations(ConductGrain)`, `declared_recruitment`, `open_recruitment`, `qualified_index`, `resolve` (386-610). Doc (`:1-40`) records why: the earlier reader named each file by its last `theorem` and charged comments/preamble as recruitment.
- `R/holonic-engine/src/derivation_atlas.rs` (2746): `Derivation {name, statement, recruited}` (236); `read_derivation(text) -> Option<Derivation>` (505); `DECLARATION_FORMERS` = abbrev, axiom, class, def, example, inductive, instance, lemma, opaque, structure, theorem, variable (188); `CircuitAperture {identity: {ByDeclaration|ByRoute}, coefficient: {Incidence|Multiplicity}, statements: {Withheld|Founded}, reach: {IntoDerivation|OutOfDerivation}}` (646); `found_circuit(...) -> DerivationCircuit {aperture, complex: GradedCausalComplex, vertices, recruitments, reaches, routes}` (1012, 800) — 0-cells = declarations/symbols/statements, 1-cells = recruitment or reach, no 2-cells (doc `:11-26`); `invariant_movement`, `route_movement` (1311, 1409) return what changed between two readings.
- `/home/b/Workspaces/holonics/soma/tools/derivation-atlas/src/main.rs`: `extract` runs `lake build derivation_atlas` then `.lake/build/bin/derivation_atlas --input … --output …` (1274-1290); `validate`, `inspect`, `corpus` consume the `holonics.derivation-atlas.v2` JSON (`SCHEMA`, mirrored `camelCase` structs).

### B.6 CUDA kernels `R/holonic-engine/kernels/` (all registered in `build.rs:52-58`)

| File | Header purpose | `__global__` entries |
|---|---|---|
| `exact_conic_support.cu` | exact 128/192/256-bit conic and segment support tests (`ExactCoefficient` int128 carrier, no header prose) | `exact_conic_support{,_i192,_i256,_i128}`, `exact_segment_support{…}` (698-831) |
| `exact_relation_support.cu` | exact pair relations over windows (`RelationPair`, `RelationWindow`; "Wire order: together, apart, open, conflicted" :117) | `exact_relation_all_pairs`, `_addressed_pairs`, `_count/emit_addressed_positive`, `_count/emit_window_positive`, `_grade_all_pairs`, `_emit_grade_obstructions` (174-431) |
| `exact_embedding_fiber.cu` | "every score `s[v] = <E[v],u>` exactly as 128-bit integer … does not rank, max, or threshold" | `exact_readout_scores{,_batched,_addressed}`, `exact_score_octaves`, `bfloat16_lowest_exponent`, `bfloat16_align`, `exact_row_absolute_mass` |
| `exact_eta_head.cu` | head of the eta jet, exact fixed-point interval arithmetic (int128, 96 fractional bits) at every box boundary point | `eta_head_jets` (179) |
| `exact_quartic_realizers.cu` | quartic rational-point refusal by quadratic residues at declared primes ("the card decides a refusal, never an admission") | `quartic_realizer_refusal{,_integral}`, `specialization_wheel_score/traces`, `surface_realizer_refusal` |
| `exact_resident_section.cu` | resident interval section `[lo,hi]` at dyadic grain `2^-F`, lower rounds down/upper up; owner `resident_section.rs` | `section_from_bfloat16`, `section_contract`, `section_factorized_contract`, `section_rms_rebase`, `section_chronology`, `section_contact`, `section_gelu_tanh`, `section_hadamard`, `section_carry`, `section_census`, `section_midpoint_seal`, `section_arithmetic_control`, `section_contract_join`, plus withdraw/permute/partition/scale helpers, `athena_walk_cooperative`, `athena_future_staged` (332-1904) |
| `refine_shell.cu` (488 KB, 137 kernels) | "The exact quotient and its resident materials": `claim_identities` is the material-free law (class,key) → identity; one body, one law, many materials | `claim_identities` (73), `conduct_native_word` (116), `conduct_complex_incidence` (143), **`conduct_coupled_complex_parametron`** (315), `receive_interval_potential_incidence` (377), `return_and_recur_native` (561), `cultivate_dynamic_morphology` (657), `conduct_inference_ecology` (1381), `conduct_material_operation_world_tube` (1482), `conduct_membrane_local_contacts` (2282), `conduct_membrane_sparse_relational_forward` (2365), `gather_membrane_radiation` (2950), `verify_resident_receiver_history_compression` (7352), `balance_membrane_boundary_chain` (10063), `refine_shell` (10101); the remainder are `membrane_*` moment/front/quotient stages (3058-10622) |

---

## C. Cargo workspace (`/home/b/Workspaces/holonics/Cargo.toml`)

Header (`:1-13`): "`body` is pure law: no_std, zero dependencies. `crates/holonic-structure` is the substrate … `relational-geometry` and `holonic-engine` are the exact receiver-relative geometry, float-free over BigRational with Sturm-certified algebraic roots. `holonic-language` is the reflective runtime. `soma/life` is the membrane where the ecologies live." Resolver 2, edition 2024. Excluded (own nightlies, committed artifacts): `soma/kernel`, `soma/kernel/builder`, `soma/mount/mount-smoke-kernel`, `soma/mount/soma-kernel-cuda`.

| Member | First doc comment |
|---|---|
| `crates/holonic-structure` | Production-owned structural carriers for exact holonic computation (`src/lib.rs:1`) |
| `crates/holonic-language` | Exact reflective runtime beneath learnable surface codecs (`:1`) |
| `crates/relational-geometry` | Exact, receiver-relative geometry for the standalone laboratory (`:1`) |
| `crates/holonic-engine` | Exact causal execution and receiver-relative visibility (`:1`) |
| `crates/holonic-architecture-lint` | Repository architecture ratchet for continuing holonic machinery; observer/build tool, per-file census (`:1-6`) |
| `soma/body` | `#![no_std]` "the law and the organs — one module per organ" (`src/lib.rs:3`) |
| `soma/abi` | Substrate-neutral word records at Soma's execution membrane |
| `soma/membrane` | The live, organ-neutral execution membrane |
| `soma/surface` | the M4 felt-series card boundary; `FeltSurface` |
| `soma/life` | Production library surface for the continuing Soma bodies |
| `soma/mount` | CUDA Driver API boundary scaffolding for the headless production mount |
| `soma/tools/record-index` | (no crate doc; modules `model, render, scan, sha256`) |
| `soma/tools/derivation-atlas` | CLI `extract|validate|inspect|corpus` over `holonics.derivation-atlas.v2` bundles (`src/main.rs:11-16`) |
| `soma/tools/standing-deposit` | The standing deposit and its verifier |
| `soma/tools/holon-plate` | `.holon` — the on-disk deposit mouth |

Workspace deps: `serde`, `ron 0.12`, `num-bigint 0.4`, `num-rational 0.4`, `num-traits`, `sha2`, `thiserror 2`.
