# Threshold refinement and partitioned energy return Holonic toolkits

[project-postulate] Brandon requests a bounded mathematical construction before proceeding with
Athena: develop Holonic representations from RH, Hodge, NS, BSD and Yang–Mills, with the official
endpoint statements treated as applications. He proposes repeated exponentiation of the current
RH upper bound and reconnects energy cuts, crystals, thermal/cosmological transport and receivers.
This return develops two formal owners and an exact exterior energy experiment. It does not
restart five endpoint campaigns or make their completion prerequisites to Athena.

## Why the checked bound is 1/8

[proved-derived; source-inspected] `RH/DeBruijnIterate.lean::strip_xiIter` starts with
`|Re z−1/2|<1/2` for zeros of ξ. After k translation averages of size μ it bounds the squared
strip width by `max(1/4−k μ²,0)`. Taking μ=1/(2N) and k=N² spends a total squared displacement
1/4. `DeBruijnLimit` passes those changed functions to the Gaussian-kernel limit

\[
\cosh\!\left(\frac{u}{2N}\right)^{N^2}\longrightarrow
\exp(u^2/8).
\]

The coefficient is (1/2)·(1/2)²=1/8: the quadratic term of log cosh and the original half-strip
width. `DeBruijnSeal` then gives `0≤Λ_DN≤1/8`. `CriticalChart` proves
`Λ_std=4Λ_DN`, so this is the classical standard-coordinate upper bound 1/2. None of these
numbers comes from octets, vocabulary or a byte representation.

[proved-derived] Increasing N improves the approximation to the same flowed function; it does
not lower that function's time from 1/8. Serial heat evolution adds its time parameters.
Changing spatial/phase coordinates rescales the generator and its clock together. A smaller
printed coefficient after such a rechart is not automatically a stronger statement about the
original source at its original clock.

[proved-standard] A stronger source-specific bound is already available in the published
Platt–Trudgian result: Corollary 2 gives `Λ_std≤1/5`, using rigorous zero verification and the
Polymath criterion. In our coordinate this gives `Λ_DN≤1/20<1/16`. See
[the primary paper, §3.4](https://arxiv.org/pdf/2004.09765). This comparison does not claim the
latest numerical record. That published theorem/certificate route has not been imported into
this repository's Lean proof; its presently checked upper bound remains 1/8. The proof boundary
is therefore narrower than available external mathematics, not an intrinsic barrier at 1/8.

## The proposed square refinement is now exact mathematics

[definition] `RH/ThresholdRefinement.lean` defines `SquareClosed` on the actual seam set:

\[
0<t<1,\quad t\in\mathrm{seamTimes}
\quad\Longrightarrow\quad t^2\in\mathrm{seamTimes}.
\]

[proved-derived; formal-checked] `squareClosed_iff_RH` proves that this property is equivalent
to RH using the existing closed-ray theorem `seamTimes=[Λ_DN,∞)` and the checked bound. If the
attained threshold were positive, applying square closure to it would put Λ_DN² below its own
infimum. Conversely RH gives the seam set [0,∞), which is square-closed. The proposed sequence
would be `2^(-3·2^n)`, starting `1/8,1/64,1/4096,…`. The module also checks a halving iteration
and its limiting implication. These are conditional refinement mechanisms; no unconditional
square-closure theorem for ξ is asserted.

[proved-derived; formal-checked] The same module gives an actual sharpness control for the
generic strip method. The existing polynomial heat operator satisfies

\[
e^{-tD^2}(z^2+a^2)=z^2+a^2-2t.
\]

`heat_quadratic_zero` proves this identity. For a=1/2, the function has the following roots:

| Time | Constant term | A checked off-real root, when present |
|---|---|---|
| 1/8 | 0 | The polynomial is z² |
| 1/16 | 1/8 | i√(1/8) |
| 1/32 | 3/16 | i√(3/16) |
| 1/64 | 7/32 | i√(7/32) |

The module proves both zero evaluation and strictly positive imaginary part for the last three.
Thus generic strip information alone cannot justify the proposed descent. This polynomial is
not ξ; the control identifies the extra source-specific structure a successful ξ refinement
must use. It does not contradict the external ξ bound below 1/16.

## Exponentiation, composition and the null fibre

[established-bounded; computational-witness] The exact exterior experiment also compares two
operators on the same four paired-mode coordinates. Each factor has diagonal readings (0,a),
with the declared rational a=1/8:

| Operator | Diagonal readings | Null dimension |
|---|---|---:|
| Independent generator sum A⊗I+I⊗A | 0,a,a,2a | 1 |
| Coupled product A⊗A | 0,0,0,a² | 3 |

The positive face really squares, but two more directions become invisible. This supplies a
concrete reading of the hypergeometry question: the operation producing the product changes
the retained source family. It is useful compositional mathematics, not an inference that a heat
threshold or physical mass gap must square. The receiver, generator and null fibre must all
travel through the proposed representation change.

## A returned Hodge energy cut

[proved-derived; formal-checked] `Physics/PartitionedHodgeEnergy.lean` now owns the arbitrary
finite real and complex section identity

\[
E_A(h+e)=E_A(h)+E_A(e)
+2\operatorname{Re}\sum_{j\in A}h_j\overline{e_j}.
\]

For disjoint pieces A,B, the mixed terms add. If their union is orthogonal at the chosen
receiver, those two terms are opposite. Global Hodge orthogonality therefore does not permit
discarding the local mixed term. This is a receiver ledger; it does not assume that cutting
a complex commutes with its global Hodge projection.

[proved-derived; formal-checked] The concrete four-edge cycle has

\[
x=(1,2,3,4),\quad h=(5/2,5/2,5/2,5/2),\quad
e=(-3/2,-1/2,1/2,3/2)=d(0,-3/2,-2,-3/2).
\]

The constant h has zero boundary at every vertex. Its restriction to the first two edges has
a nonzero cut boundary; the two pieces' boundaries cancel when rejoined. The checked energy
is 30=25+5, while the two cut energies are 5 and 25. On each piece the separate h/e energies
sum to 15; the necessary mixed terms are −10 and +10. The formal source exposes those exact
readings and the paired boundary cancellation. This is the explicit finite-cycle Hodge
decomposition, not a new general algebraic-cycle realization theorem.

[established-bounded; implemented-exact; computational-witness] The
[exterior witness](../experiments/partitioned_hodge_energy/witness.py) continues the same current
under the exact finite implicit law `(I+τL)x_τ=x_0`, where L is the four-cycle incidence
Laplacian. The nonharmonic pieces are actual eigenvectors with eigenvalues 2 and 4; their
coefficients are divided by 1+2τ and 1+4τ. The harmonic current is retained.

| Local step τ | Total quadratic energy | Left/right mixed terms |
|---|---|---|
| 0 | 30 | −10, +10 |
| 1/8 | 6301/225 | −8, +8 |
| 1/2 | 235/9 | −5, +5 |
| 1 | 5734/225 | −10/3, +10/3 |

Every row checks the full implicit equation, cut energy ledger and exact decrease
`||x_0||²−||x_τ||²=2τ<x_τ,Lx_τ>+τ²||Lx_τ||²`. The
[rational receipts](2026-09-11_holonic_toolkit_receipts/partitioned-energy.json) retain the
currents, potentials and cut boundaries. This is a declared finite step law, not exact continuous
heat flow or the RH clock. Its quadratic energies have no unprovided joule calibration.

## Holonic representations already available across the five subjects

[established-bounded; source-inspected] These are reusable existing constructions, checked
against actual source owners rather than inferred from the names of the problems:

| Source subject | Actual representation and owner | Productive next composition |
|---|---|---|
| RH | Positive kernel/heat passage, prime-power phase current, zero/strip receivers and retained tails; `RH/FoldedSource*`, `FosterClassHeatFlow`, `CriticalChart` | A ξ-specific strip/barrier improvement with full source/remainder and unchanged clock; the new refinement criterion locates its required content |
| Hodge | Finite differential, adjoint, harmonic/exact/coexact decomposition; `HodgeFiniteDecomposition`, `HilbertTransportChain`, actual cycle-class source in `HodgeConjecture` | Partitioned constitutive energy and transported projection with its boundary/mixed defect; today's finite cut is the first returned instance |
| NS | Complex-valued field and real receiver, actual pressure/triads, world tubes and hidden-state closure; `FluidReceiverClosure` and the existing complex two-field/Duhamel owners | Carry that partition ledger through full nonlinear resolved/hidden feedback and a finite-interval memory/remainder bound |
| BSD | Local transfer determinant `det(I−TM)=1−aT+qT²`, power-trace recurrence and Weil phase; `LocalFactor`, `TraceSequence`, `FamilyHeight`, concrete descent/analytic witnesses | Relate actual arithmetic realizers and height/period receivers across a specified tower, retaining locally invisible alternatives |
| Yang–Mills | Noncommuting gauge/curvature transport and finite Hilbert energy/gap/refinement; `HolonicGaugeCovariance`, `HilbertTransportRefinement`, `DissipationGapBridge` | Transport the actual quadratic form and its nonharmonic spectrum across a chosen refinement, separating a coordinate rescale from changed null/gap structure |

[definition] The finite Hodge/gauge/energy representations are useful without solving algebraic
cycle surjectivity or continuum gauge existence. The elliptic local factor already has a
constructive matrix/phase realization; older “still missing” BSD prose must not revoke later
specific point, descent or analytic returns. A general height/global realization correspondence
has its actual scope rather than being assumed from a determinant. The Yang–Mills toolkit's
scale-uniform gap question remains separate from positivity at each finite scale.

## What the three supplied papers add

[conditional] [Life on a closed timelike curve](https://arxiv.org/html/2405.18640v1) derives
periodic quantum evolution from a fixed-background periodic symmetry, with the observer's
proper-time generator and energy spacing tied to the period. Its useful import is the complete
phase/clock constraint, including relative clock rates; backreaction is outside its construction.
For our torus/Parametron work, a returning phase face and a returning complete state are different
receivers. This offers a spectral-clock construction, not evidence that a physical CTC exists.

[established-bounded; source-inspected] [Fractal basins trap latent reasoning](https://arxiv.org/html/2609.04963v1)
studies initialization slices, decoded settling times and saddle-associated transients in selected
models/tasks. The methods exclude specified unconverged or multistable slices; finite-resolution
basin statistics are not a universal complexity theorem. The useful Athena import is to compare
actual decoded trajectories and retained internal differences under situated perturbations.
Stable decoded output alone does not show full-state convergence. No large external model sweep
was performed in this pass.

[conditional] [The superconducting point-contact paper](https://arxiv.org/html/1906.01682v2)
expresses dissipative conductance through a phase/energy integral of
`Tr((∂φS)†(∂φS))`, with occupation weighting and its low-bias assumptions. Integer Fourier
sidebands carry energy exchange when phase winds. This connects junction geometry, phase
derivative, quadratic response and an actual work receiver. It is a useful target for extending
our finite scattering/port-energy owners; today's cut theorem does not claim to derive the
complete superconducting conductance formula.

## Energy distribution and the choice before Athena

[established-bounded; source-inspected] The existing physical atlas and cosmological inference
records already connect pressure, heat flux, stress, gravity and receiver-dependent clocks.
The water/crystal/plasma discussion retains changing constitutive regimes, and
`HolonicCosmologicalInference` retains the plural `(H,Ω)` fibre behind `Λ=3ΩH²/c²`.
`PortEnergyHeat`, `ReceiverStressEnergy` and `HolonicPolarizedCrystalTransport` supply current,
energy and coherent-path ingredients. These sources were recovered; no geothermal, dark-sector
or cosmological parameter fit was run.

[interpretation] The immediately useful connection is **partition, interior relaxation and
receiver consequence with the mixed term retained**. A sharp boundary changes what is exposed;
a material/pressure change changes the constitutive form; a clock change changes the rate chart.
Their joined ledger can describe what an apparently missing local energy contribution actually
depends on. A dark-sector interpretation additionally supplies its physical source and jointly
tested receivers; one omitted cross term does not identify a dark-matter or dark-energy model.

[definition] The preferred next use is to carry the new partition/mixed-current obligation into
Athena's family incorporation and Holonic Encoding work, and into the existing nonlinear fluid
closure as a bounded mathematical application. A stronger RH bound is a distinct source-specific
certificate task. Repeated squaring has an exact formal criterion now, but no unconditional
contraction mechanism was found in the inspected strip argument. There is no reason to hold the
native plan until that criterion is proved. The user may direct a further bounded mathematical
branch; this return does not silently schedule one.

## Verification

[established-bounded; process-audit] The focused new Lean checks and
`lake build ElementaryHolonics.Framework.Physics ElementaryHolonics.RH.ThresholdRefinement`
pass (9,214 jobs, including replayed dependencies). The primary agent generalized the energy
identity to arbitrary finite real/complex sections and repaired the paired-cut proof before
the final successful build. The exact Python witness passes all displayed receiver and step
identities. No native CUDA operation or Athena model changed. The new energy owner is imported
by `Framework.Physics`; both owners are linked in the maintained source map.

[established-bounded; process-audit] The research umbrella `lake env lean ElementaryHolonics.lean`
also passes after importing both new owners. Targeted axiom inspection of square closure, the
actual quadratic heat identity, the complex cut-energy identity and paired boundary cancellation
returns only `propext`, `Classical.choice` and `Quot.sound`.
