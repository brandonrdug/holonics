# Winding, carry, faces and placement generalize the helical pair

**Date:** September 21, 2026. **Source:** Holonics `0daab75a`. **Scope:** Brandon's direction on
the general objects behind the helical pair, recovery of their existing owners, four new checked
Lean modules, one exact Rust owner, and the operating-contract and issue updates that attach
them. The reusable definitions live in the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md); this record keeps the direction, the
source recovery and the boundary between theorem and correspondence. No native HNN behavior
changed.

[historical] The later [design iteration](2026-09-21_THE_GENERATOR_MACHINE_RETAINS_ITS_SOURCE_AND_RECEIVING_LAWS.md) preserves this return and corrects its source-moment attribution, zero-power/lock and closure domains, harmonic-standing scope, spectral/functionality claim and cost contract. Use the live guides and native contract for the finalized implementation. The measurements and original source audit below retain their recorded scope.

## Direction

[project-postulate] Brandon's September 21 message, written deliberately coarsely and asking for
the technical analogues rather than a literal reading, joins these subjects as one picture:

- primes as patterned phases of remainders after divisions and inversions of basis, with their
  winding and staircasing, and the distribution law `ζ` reads from them;
- Rodgers–Tao and `Λ_DN` as flux and fluid motion, cross-entropy as a physical crossing flux,
  several axes of time, induction and electromagnetism, resonance and addresses;
- Einstein's tensors as an atlas of where things can go; tensors holding matrices as samples,
  a Holon as the object that *continues*, its parametric behavior as its own codec, a picture
  of it as an instantaneous moment, and its reading as a temperature;
- chains of measurable pairwise intersections between winding strings, toroids and knots,
  navigated rather than searched;
- generalized algebraic cycles and Hodge classes as winding structures, conservation of faces
  and compression of functionality in music, tying, codes and composition;
- elliptic curves, flux and induction packaged into helical/toroidal simplicial complexes;
- the critical strip as a winding transport tube between two plates, whose cross-sections are
  discrete charts, whose arc is completely determined and *continuable*, and which reads either
  as a whole circuit or as the intermediary between two bodies, with an interior/exterior
  polarity; integration by reflection and fractal packing.

[project-postulate] Brandon confirmed the returned correspondence and directed that these
objects be formalized, given native owners and ingrained in both operating contracts, so that
the picture is unified continuously during work.

## Recovered owners

[established-bounded; source-audit] A search of `docs`, `research`, `formal` and `crates` at
`0daab75a` found that most constituents already have owners, mainly under `Millennium/` and
`RH/`, none of them joined to the pair unit:

| Subject | Existing owner |
|---|---|
| Continued-fraction words in the modular group, mediant and unimodularity | `Millennium/Farey`, `Millennium/Towers` |
| Euler factor as a transfer determinant; trace sequence; roots on the circle of radius `√q` | `Millennium/LocalFactor`, `TraceSequence`, `PartitionFunction` |
| Zero pairs as LC tanks; RH as Foster losslessness | `RH/FosterTanks` |
| Backward heat flow, Hermite optimum and the confined log-gas | `RH/HeatFlowStackedSeam` |
| Hodge index signature `(1, n−1)`; reflected positivity; Pontryagin placement | `Millennium/HodgeIndex`, `LorentzianPerp`, `ReflectedPositivity`; `holonic_interaction::StructuralPlacement` |
| Lefschetz (1,1) through the exponential passage | `Millennium/HodgeDivisorExponentialPassage` |
| Finite weighted Hodge decomposition; harmonic ≅ cohomology | `Foundation/HodgeReceiver`, `sheaf_diffusion.rs` |
| Product over places; p-adic tower and compatible sections; Hensel lifting | `Millennium/PlaceLedger`, `Foundation/IwasawaTower`, `ContinuingTower`, `FamilyTunnellBrandtPadicHensel` |
| Crossing populations, polygon winding, helicity and Lamb faces | `Millennium/WindingLedger`, `Crossings`; `exact_analysis::polygon_winding` |
| Integration by reflection as a boundary construction | `diffusion.rs`, `causal_reflection.rs`, `Millennium/Horizon.smith`, `traversible_chain` |
| Packing by mediants | `Foundation/FractalPacking` |
| Optimal transport words; future-distinguishing retention | `Foundation/TransportWord`, `Standing`, `ReceiverHistoryCompression` |

[established-bounded; source-audit] Absent before this return: a statement of the carry as a
cocycle and of the odometer as a cascade; the lock of a pair as its zero-power direction with
a modular address; the conservation of trace faces under phase carriage and a machine's
transfer determinant; the holonomy of a cell with the dormant mode as its harmonic class; and
any Rust owner for Farey addresses, the carry tower or site factors. The August 13 record had
set aside Krohn–Rhodes because irreducible factors discard the gluing, observing that `ℤ/4` and
`ℤ/2×ℤ/2` share composition factors; the carry cocycle is that gluing.

## Returned formal statements

[proved-derived; formal-checked] Four modules, 38 theorems, standard axioms only, imported from
`Framework/Geometry` and `Framework/Dynamics`; `bash tools/lean_check.sh
ElementaryHolonics.Framework` passes at 9,206 jobs:

- [`Geometry/PhaseCarry`](../../formal/elementary-holonics/ElementaryHolonics/Geometry/PhaseCarry.lean):
  winding additivity up to the carry, the carry cocycle, `ℤ/4 ≄ ℤ/2×ℤ/2`, the odometer as `+1`
  in the digit chart with the upper level advancing by the lower winding, the integer winding of
  a closed loop, and the group form in which the state retains a central carry while carried
  material returns.
- [`Geometry/PairResonance`](../../formal/elementary-holonics/ElementaryHolonics/Geometry/PairResonance.lean):
  a lock is the zero-power direction of the pair face; neighbouring locks are unimodular; the
  mediant neighbours both, lies between and is the cheapest ratio in the gap; a unimodular
  rechart is invertible and conserves intersection numbers; the diagonal step generates the
  torus of two coprime circles.
- [`Transport/GeneratorTraceFaces`](../../formal/elementary-holonics/ElementaryHolonics/Transport/GeneratorTraceFaces.lean):
  powers of carried material are carried powers; phase carriage conserves determinant, trace
  sequence and transfer determinant; a machine of independent sites has the product of the site
  factors and the sum of the site trace sequences.
- [`Transport/CellHolonomy`](../../formal/elementary-holonics/ElementaryHolonics/Transport/CellHolonomy.lean):
  regauging conjugates a cell's holonomy, a pure gauge is trivial, an abelian holonomy and the
  trace and determinant of a matrix holonomy are gauge-free; cell flux ignores a potential; a
  harmonic mode is silent at every node and cell, is not a potential, and every closed field
  retains exactly one.

[proved-derived; formal-checked] [`RH/ZeroPairLock`](../../formal/elementary-holonics/ElementaryHolonics/RH/ZeroPairLock.lean)
returns the first derivation target of the zero-pair interpretation: the reflected pair
`(σ,γ)`, `(1−σ,γ)` reads power `(2σ−1)²` on the isotropic unit face, is locked exactly on the
seam, and for `γ ≠ 0` is locked exactly when the `FosterTanks` inductance is a positive real.
It is imported by the research umbrella, not by the `Framework` default target, because
`FosterTanks` carries the analytic `RH/` stack.

## Returned native owner

[established-bounded; implemented-exact] `relational_geometry::winding` mirrors those modules in
exact arithmetic: phase, winding, carry and a mixed-radix `Odometer` whose `advance` moves each
level by the winding of the one below; `LockAddress` as the Stern–Brocot word of a rate ratio
with mediants, neighbour tests, the cheapest lock in an interval and `pair_lock` on a
`ScrewPair`; `SiteFactor` and `Machine` with trace sequences, transfer coefficients, rotation /
marginal / dilation classification and Newton's identities between them; and
`triangle_holonomy`/`regauge` on `AffineMap3`, whose translation part is the Burgers step
(`burgers_step`, with `linear_trace` as the gauge-free face). Twenty exact tests mirror the Lean
theorems, several exhaustively over small ranges. `screw.rs` is consumed unchanged:
`pair_lock` reads `ScrewGenerator::velocity` at each `SituatedScrew::initial`, and the holonomy
uses `AffineMap3::followed_by`/`inverse` in the order that makes `triangleHolonomy_regauge` hold
verbatim.

[definition; agent-inferred] Three scope notes from the native return. `Odometer` requires every
radix at least two, narrower than Lean's `0 < n`, because a radix-one level holds no phase.
`simplest_between` returns the Stern–Brocot ancestor when an interval spanning more than one
integer has several minimal-denominator rationals; the minimal denominator is unique and is what
the tests pin, and between Farey neighbours the mediant is the unique minimizer. `SiteKind::
Dilation` is exactly where `TraceSequence.theRootHasSquaredModulusQ` and
`LocalFactor.theFactorSplitsThroughTheWeilRoot` stop applying, so `kind()` is the executable
boundary of placement. `ℤ/4 ≄ ℤ/2×ℤ/2`, the group-form carry theorems and the coprime diagonal
winding have no executable counterpart in this owner.

## Theorem and correspondence

[definition] The guide's §7 table grades each arithmetic statement. Standard theorems are cited
in their ordinary scope: the Chinese remainder torus, Hasse–Weil placement for curves through
the Hodge index theorem, the `Λ_DN` zero dynamics and `Λ_DN ≥ 0`, the argument-principle
staircase, Lefschetz (1,1), Poincaré–Lelong, the Eisenstein scattering tube, the devil's
staircase of a driven pair and the holonomy decomposition of finite machines. Two
correspondences are graded `interpretation` with their maps, limits, first derivation target
and falsifier: the zero pair `(ρ, 1−ρ̄)` as a helical pair with equal angular rates, and primes
as knots. Hodge beyond divisors remains a conjecture. None of these is a claim about a
Millennium endpoint.

## Consequences for construction

[definition] The campaign packets are unchanged in order. They acquire operands:

- Packet 1 (#28/#48) declares the pair face and reports its locks through `LockAddress`.
- Packet 3 (#17) gives each generator a `RationalPhase` with its carry level, each admitted
  pair its lock address and tolerance, each site a `SiteFactor`, and the incidence complex its
  cells, so that participation, flux and the retained harmonic class are read from the same
  complex.
- Packet 5 (#17) realizes a dormant generator as a harmonic class that a cycle receiver reads.
- Packet 6 (#18/#61) checks a compressed machine against Newton's identities between its
  transfer determinant and trace sequence, and advances phases by winding rather than by step.
- Packet 8 (#62) gains: the carry tower joined to `IwasawaTower.padicTower`; the Foster pair
  identity as a pair quadrance (first derivation target of the zero-pair interpretation); the
  lock address joined to `Farey.cfProd`; signature placement (#54) for the pair medium; the
  affine holonomy as a screw with its Burgers step.

[established-bounded; source-inspected] Verification: the Lean and Rust receipts in
`docs/VERIFICATION_RECEIPTS.tsv`, link checks over the edited documents and `git diff --check`.
