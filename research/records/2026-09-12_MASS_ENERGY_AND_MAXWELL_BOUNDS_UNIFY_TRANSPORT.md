# Mass–energy and Maxwell bounds unify transport

[project-postulate] Brandon's latest September 12 request makes mass–energy equivalence
central to the comprehensive synthesis of physical transport, prediction, modes and
intelligence. His correction also rejects categorical denials that restricted models are
scientific simulations or that the work belongs to computational biology/neuroscience.
The [comprehensive report](../../docs/MASS_ENERGY_AND_CAUSAL_TRANSPORT.md) is the self-contained
mathematical reading surface; this record retains implementation and verification evidence.

## Source recovery and classification correction

[established-bounded; source-inspected] The source recovery includes the July 19
`THE_QUANTUM_PROPERTY_IS_THE_HOLONS_TRANSPORT_CLASS_THE_PIVOT_RETURNS_ONE_FACE` mass/proper-time
and QCD sections, July 12 `THE_RESERVOIR_THE_UNTYING_AND_THE_MUTUAL_WORLD` annihilation and
compound-nucleus corrections, the traffic canon, September 3 dual-constitutive/Maxwell seam
record, and the September 12 generator, optics, periplus and predictive-release returns.
Their current formal owners were inspected directly. Historical source slogans and engine
scheduling rules were not restored.

[established-bounded; source-inspected] Primary external sources include PDG 2025 kinematics,
Perez–Ribisi's confined-radiation inertia construction (arXiv:2101.11923v1), Yang et al.'s QCD
mass decomposition (arXiv:1808.08677v2), the BIPM 2018 SI resolution and NIST SP330, Tong's
electrodynamics and GR chapters, and the cited nuclear/source and prior information/RH papers.
The report retains numbered citations and a full source list. The source review explicitly
distinguishes complete invariant mass from scheme-dependent decompositions, and exact
constitutive identities from measured SI coefficients.

[project-postulate] The prior predictive-release report and guides said the construction was
not a brain/GR simulator. That blanket wording is replaced with its actual scientific scope:
a GR-derived weak-field simulation with prescribed uniform acceleration, used in the
computational biology/neuroscience programme. Its neural preparation correspondence and its
held degrees of freedom are stated directly. The operating contract now requires this
affirmative, equation-specific classification. Earlier stored terminal/JSON descriptions
remain historical evidence of the former wording; live code and guides use the correction.

[definition] The turn canon's categorical “nothing fissions or fuses as an event” clause is
also corrected: the old software-predicate ruling is historical, while physical nuclear
channels retain their actual reaction dynamics and conserved currents. The August `temper`
description and name counts are marked historical rather than used as present physical
capability evidence. The traffic canon now links its current constitutive/mass-energy reading.

## New formal consumers

[proved-derived; formal-checked] `Physics/CompositeMassEnergy.lean` reuses
`HolonicMassShellFace.FourMomentum` and its Lorentz polarization law. It proves the complete
exchange identity, the angle-dependent invariant mass of two massless momenta, opposite
versus parallel unit-photon controls and boost invariance under
`gamma²(1-beta²)=1`. Its unit-speed coordinate boost is a chart of the full energy/cp law.

[proved-derived; formal-checked] `Physics/MaxwellEnergyCone.lean` proves the cross-product
identity and the complete sum-of-squares defect

`c²u²-|S|²=c²[(|X|²-|Y|²)²/4+(X·Y)²]`.

It derives `|S|≤cu` for nonnegative c, and a parallel-field zero-flux control. Both owners
are imported by `Framework.Physics`. The existing discrete Maxwell constitutive and Poynting
owners give their adjacent source/dynamical laws; the report supplies the continuum and
Lorentz interpretation with its physical hypotheses.

## Exact energy–momentum and electromagnetic application

[established-bounded; implemented-exact] `exact_linear/energy_momentum.rs` exports
`EnergyMomentum`, `VacuumEnergyChart`, `MaxwellEnergyFace` and `EnergyMomentumError`.
It retains energy and three c*p coordinates, signed exchange, Lorentz pairing and invariant
square. Boosts reuse `ExactRatMatrix` and require the exact positive-gamma/sub-luminal-beta
constraint. Future-causal total momenta are distinguished from signed exchange vectors.

[established-bounded; implemented-exact] The vacuum chart validates positive c, epsilon and
mu with `c² epsilon mu=1`. It reads energy density, Poynting current, both electromagnetic
invariants and the full causal-cone defect. Observer changes transform the six E/B components
before reading them again; the contracted energy-current face is not mistaken for a total
four-momentum vector. These are reusable exact relativistic and electromagnetic modelling
operators, with rational coordinate/unit charts and no floating-point selection.

[established-bounded; computational-witness] The new `mass_energy_transport` application
returns the following exact controls in its stated c=1 energy-scaled chart:

| Construction | Return |
|---|---|
| Two equal opposite photons | E=2, p=0, M²=4 |
| Two equal parallel photons | E=2, |p|=2, M²=0 |
| Boost of the opposite pair, beta=4/5 and gamma=5/3 | E=10/3, p_x=-8/3, M²=4 |
| Body rest energy 3 retaining the balanced radiation | E=5, p=0, M²=25 |
| Absorption of one unit photon by the body | E=4, p_x=1, M²=15 |
| Radiative transition from parent rest energy 5 to daughter rest energy 3 | Photon energy 8/5; daughter E=17/5 and p_x=-8/5; recoil kinetic energy 2/5 |
| Elastic reflection of a unit photon by the rest-energy-3 body | Reflected photon energy 3/5; body E=17/5 and p_x=8/5; body's invariant mass remains 3 |
| Orthogonal equal normalized E/B | u=1, |S|=1, cone defect 0 |
| Parallel equal normalized E/B | u=1, S=0, cone defect 1 |
| Boosted orthogonal field | u=25/9, cone defect 0; field invariants preserved |

[established-bounded; computational-witness] A second constitutive coordinate chart with
`c=1/2`, `epsilon=mu=2` preserves the null-field equality and has impedance square one.
This is a separate declared chart, not a change of the universal SI vacuum constant. The
exact SI conversion for 41 J retained as rest-frame internal energy is
`Delta M=41/89875517873681764 kg`. The application explicitly distinguishes it from a 41 J
increase of translational kinetic energy at fixed invariant mass. The
[complete receipt](2026-09-12_mass_energy_receipts/mass-energy.json) retains all comparisons.

## Verification and integration

[established-bounded; process-audit] `cargo test -p holonic-engine --no-default-features --lib exact_linear`
passed all 40 selected tests, including the three new mass/boost/Maxwell tests. The exact
application completed its assertions. The [Cargo terminal](2026-09-12_mass_energy_receipts/cargo-tests.txt)
retains the test names and result; native recurrence was unchanged.

[established-bounded; process-audit] `bash tools/lean_check.sh ElementaryHolonics.Framework.Physics`
completed with the new imports. The [formal receipt](2026-09-12_mass_energy_receipts/formal-terminal.txt)
retains the owner/build output and completion. Source comments and naming corrections were
checked with their consumers; Rust formatting and `git diff --check` pass.

[definition] The report unifies mass/rest energy, radiation/recoil, Maxwell/impedance, Lorentz
dilation, friction/relaxation, Hodge/mode classes, fractal and periplus representations,
information/Gamma/zeta, predictive release and the source-specific RH bound. It preserves
the roadmap's operator/encoding order. Causal-front and spectral-threshold bounds are connected
through explicit preservation maps, not by equating their numerical constants.

[proved-derived] The report also derives the finite positive-spectrum wave/heat identity
`exp(-tA)=(4πt)^(-1/2)∫ exp(-s²/(4t)) cos(s sqrt(A)) ds` by diagonalization and the
standing checked scalar `FlowedGamma.gaussian_fourier` theorem. With `D=d+δ`, `D²=Δ`, it
joins Hodge heat to the same oscillatory representation. This finite operator derivation is
given in the report; it is not reported as an additional newly checked Lean declaration.
