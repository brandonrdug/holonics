# The finite many-body and polarized crystal transport foundation

## Authority and requested return

**Status:** COMPLETED FORMAL CAMPAIGN UNDER [`THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md). QLT1--QLT6
RETURNED; THIS FILE NOW SCHEDULES NOTHING.

[definition] Brandon's direct instruction of 2026-08-31 founds this campaign, `QLT1--QLT6`. Its
return is a Lean-standardized finite transport theory in which fermionic populations, coherent
polarized light, crystalline path differences, diffusion, boundary radiation, and receiver
observations compose existing Holonics owners without becoming one another.

[definition] The terminal milestone is one checked formal surface which provides:

- finite fermionic occupation sectors and creation/annihilation transports satisfying the
  canonical anticommutation relations;
- finite local Hamiltonians, beginning with the Fermi--Hubbard family;
- coherent complex path transport from interior lattice occurrences to addressed surface ports;
- polarization as a dependent complex vector fibre transported by local crystal/interface maps;
- diffraction and interference by linear path joining before any intensity receiver;
- distinct real-time, imaginary-time, stochastic, physical-diffusion, and open-system passages;
- receiver-resolved observables and reconstruction fibres; and
- exact or bounded simulation certificates with TorchLean available only as an exterior tensor,
  graph, finite-precision, and backend-contract adapter.

[project-postulate] The formal theory is useful independently of an executable simulator. Lean is
the structural construction chart and proof checker; Eros/Athena later receive an explicit
conformance map rather than being redefined by Lean syntax or by a numerical backend.

## Standing-reuse receipt

[established-bounded; source-inspected] At repository revision `62f1f517`, the reusable formal
owners are:

- `HolonicOrientedSiteTransport.lean`: source/target incidence, complex target and port junctions,
  retained port alternatives, and norm only after coherent linear joining;
- `HolonicDiffusionCharts.lean`: deterministic capacity/Laplacian transport and normalized
  stochastic kernels as different structures;
- `HolonicComplexParametron.lean`: oriented incidence, complex current, constitutive storage,
  coupled response, phase superposition, and chart-reorientation laws;
- `HolonicMaxwellPropagation.lean` and `HolonicDiscreteMaxwellOperator.lean`: finite field transport,
  constitutive propagation, and receiver folds;
- `HolonicSnellInteraction.lean`: exact phase carriers, interface current, compatible path families,
  and retained normal remainder;
- `HolonicPortResolvedBoundaryTransport.lean`: addressed boundary returns, telescoping balance, and
  receiver reconstruction fibres; and
- `AngleExcess.lean`: finite crystalline history positions, complex phase, coherent diffraction
  amplitude, and the later norm-square intensity face.

[counterexample; source-audit] The command
`rg -n "Fock|CAR|creation|annihilation" formal/elementary-holonics/ElementaryHolonics -g '*.lean'`
on 2026-08-31 found no live finite Fock carrier or CAR operator owner. The existing complex-current,
Maxwell, diffraction, and Parametron theorems therefore do not yet constitute a fermionic
many-body theory.

[open] `AngleExcess.lean` owns source-specific crystalline diffraction but does not carry
polarization, local optical transport along each history, an interior-to-surface boundary map, or
the common path receiver. Those are missing compositions, not evidence for another optics machine.

## Common finite path object

[definition] A finite coherent path occurrence from an interior source to a surface receiver is

```text
P = (v_0 <- e_1 -> v_1 <- ... <- e_n -> v_n,
     J_(e_1), ..., J_(e_n), alpha_P, ell_P),
```

where each edge retains both boundary maps, `J_e` transports the dependent carrier at that
crossing, `alpha_P` is an additional complex amplitude/current, and `ell_P` is the complete path
lineage. Composition retains the joining equality and multiplies transports in chronological
order.

[definition] For polarization fibre `Pol`, a source section `psi : Pol -> C`, and a finite family
of paths reaching one surface occurrence, the coherent return is

```text
Psi_surface = sum_P alpha_P * J_P psi,
J_P = J_(e_n) ... J_(e_1).
```

A receiver covector or positive effect `rho` acts only after the surface junction. A scalar
intensity is a later face such as `normSq (rho Psi_surface)`; it is not the transported carrier.

[definition] A crystalline realization additionally supplies periodic or otherwise declared local
incidence, spatial positions, constitutive axes, and recurring phase transport. Diffraction may
attach `exp(i k.x_P)` to one path; birefringence or optical activity acts through its local
polarization transport. Equal surface endpoints do not identify histories with different phase,
polarization, or interior crossings.

[project-postulate] The first implementation uses finite path sums. Calling a later limit a
continuum path integral requires a measure/cylinder construction, convergence theorem, boundary
conditions, and reconstruction statement. A finite history enumeration is not silently promoted
to that limit.

## Fermionic dependent fibre

[definition] For a finite linearly ordered mode population `Mode`, one fermionic occupation is a
finite subset of `Mode`; the finite Fock chart is the complex function space on those occupations.
The mode order is a presentation used to compute Koszul signs. Relabeling modes owes a transported
equivalence and may not change receiver consequences.

[definition] Creation and annihilation insert or remove one occupied mode with sign

```text
(-1)^(number of occupied modes preceding the addressed mode).
```

The first formal gate is the complete CAR family:

```text
c_i c_j + c_j c_i = 0,
c_i^dagger c_j^dagger + c_j^dagger c_i^dagger = 0,
c_i c_j^dagger + c_j^dagger c_i = delta_(ij) I.
```

[project-postulate] Fermions are not individually addressable particles carried through the
lattice. Modes, occupation occurrences, operator insertions, and histories retain addresses;
antisymmetry makes particle labels a forbidden native identity.

## Evolution and diffusion boundary

[definition] The campaign keeps five passages distinct:

1. real-time quantum transport `U(t) = exp(-i t H)`, with unitarity derived from a self-adjoint
   finite Hamiltonian;
2. imaginary-time transport `S(beta) = exp(-beta H)`, a generally nonunitary semigroup;
3. stochastic Markov transport in configuration, worldline, auxiliary-field, or diagram space;
4. physical constitutive diffusion with storage, current, source, boundary, and chronology; and
5. open-system dissipative transport through a declared channel or Lindblad generator.

[project-postulate] A Wick rotation or stochastic representation is a separately proved passage
with analytic and reconstruction hypotheses. Shared notation or numerical agreement never
identifies these five objects.

## Ordered construction

### QLT1 -- finite occupation carrier and CAR -- PASSED

[definition] Build the finite occupation basis, parity/Koszul sign, creation and annihilation as
linear transports, vacuum and number grading, nilpotence, adjoint relation, and all three CAR laws.

**Pass QLT1:** [definition] the focused module builds under Lean `v4.33.0` without `sorry` or a new
axiom; its audit prints only admitted Mathlib/Physlib axioms; a finite control exhibits Pauli
exclusion and the mixed anticommutator.

[proved-derived; formal-checked] `HolonicFermionicOccupation.lean` returns the power-set occupation
carrier, Koszul signs, complex-linear creation and annihilation, vacuum and particle-number grading,
same- and mixed-mode CAR, conjugate-transpose matrix relation, and a two-mode exclusion/mixed control.
The campaign umbrella built 3,167 jobs under Lean `v4.33.0`; its printed axioms are only `propext`,
`Classical.choice`, and `Quot.sound`, and the new closure contains no `sorry` or declared axiom.

### QLT2 -- local fermionic Hamiltonians -- PASSED

[definition] Compose number, hopping, on-site interaction, pairing, and current operators from the
CAR owner. Construct the finite Fermi--Hubbard Hamiltonian and prove self-adjointness, particle-number
sector preservation where applicable, and a finite observable interface.

**Pass QLT2:** [definition] a declared finite lattice returns one exact Hamiltonian matrix, its
self-adjointness theorem, invariant sector, and nontrivial hopping/interacting control.

[proved-derived; formal-checked] `HolonicFermiHubbard.lean` composes the QLT1 matrices into directed
hopping, adjoint-paired physical bonds, number and double-occupation receivers, and the finite
Fermi--Hubbard Hamiltonian. It proves Hermiticity and exact particle-number-sector preservation.
The two-site control returns a unit directed hopping amplitude and a unit on-site interaction; the
campaign umbrella built 3,171 jobs without `sorry` or a new axiom.

### QLT3 -- coherent polarized crystal paths and surface receivers -- PASSED

[definition] Extract the existing crystalline diffraction construction into a general finite
coherent-path owner. Add dependent polarization fibres, local Jones/unitary transports, interface
and crystal composition, interior-to-surface boundary ports, analyzer/effect receivers, and
path-resolved reconstruction fibres.

**Pass QLT3:** [definition] the same owner proves path-composition order, basis-rebase covariance,
interference before intensity, polarization-dependent receiver separation, boundary reconstruction,
and a two-path cancellation/reinforcement control. `AngleExcess.lean` consumes the common owner or
its duplicated diffraction definitions depart.

[proved-derived; formal-checked] `HolonicPolarizedCrystalTransport.lean` returns path boundary
fibres, coherent surface sections, analyzer and intensity receivers, chronological composition,
polarization rebase covariance, crystalline phase/amplitude/intensity, orthogonal analyzer
separation, and two-path cancellation/reinforcement. `AngleExcess.lean` now delegates its phase,
diffraction amplitude, and intensity to this common owner. Both focused modules and the 3,172-job
campaign umbrella build without `sorry` or a new axiom.

### QLT4 -- evolution, histories, and diffusion separation -- PASSED

[definition] Construct finite self-adjoint Hamiltonian evolution, imaginary-time evolution,
worldline and diagram history carriers with fermionic sign, and explicit bridges to the standing
deterministic/stochastic diffusion charts. Add open-system transport only through a separate typed
channel owner.

**Pass QLT4:** [definition] Lean refuses every untyped interchange among the five evolution species
and proves each admitted bridge with its hypotheses. Real-time norm conservation, imaginary-time
semigroup composition, Markov mass preservation, and one physical boundary balance return as
separate theorems.

[proved-derived; formal-checked] `HolonicEvolutionKinds.lean` composes Physlib's finite target with
the standing Holonics diffusion and boundary owners. It proves real-time norm conservation and
group composition, imaginary-time semigroup composition, stochastic mass preservation, and the
physical boundary telescope as distinct theorems. Fermionic worldline/diagram histories retain
permutation parity; open-system transport remains a separate typed carrier. The campaign umbrella
built 3,745 jobs without `sorry` or a new axiom.

### QLT5 -- certified finite simulation apparatus -- PASSED

[definition] Start with exact diagonalization or a residual-checked Krylov return. Every approximate
backend returns the finite model identity, parameters, cutoff/order/timestep, residual, conservation
defect, finite-precision enclosure, stochastic interval/autocorrelation where applicable, sign
severity, systematic assumptions, and source lineage.

[definition] Diagrammatic, determinant/auxiliary-field, worldline, diffusion Monte Carlo, tensor
network, analog-emulator, and digital-quantum returns are different apparatus certificates over the
same declared observables. Experimental agreement is measured validation and never a convergence
proof.

**Pass QLT5:** [definition] one exact finite control and one bounded approximate control are checked
against the same Lean observable, with their different assurance layers explicit. TorchLean may
materialize typed tensors/graphs and replay numerical certificates but supplies no Fock, CAR,
Hamiltonian, or Holonics topology.

[proved-derived; formal-checked] `HolonicSimulationCertificate.lean` returns typed method and
assurance layers, a decomposed nonnegative error budget, Hermitian model/state/energy/cutoff
certificates, and exact residual checking. The exact and approximate controls use the same
Hamiltonian/state observable and return residual masses `0` and `1/16`; the approximate producer is
explicitly external while the certificate checker remains Lean. The campaign umbrella built 3,746
jobs without `sorry` or a new axiom.

### QLT6 -- engine conformance and return -- PASSED

[definition] Map the formal path/current/receiver fields to existing Rust/CUDA owners. The map must
name which structure is native, which is an apparatus chart, which complex contraction remains on
the strongest resident surface, and which finite reconstruction fibre crosses the exterior port.

**Pass QLT6:** [definition] the Lean campaign builds through one declared umbrella, source/audit
gates are green, the engine map names no new semantic cabinet, and `THE_ROADMAP.md` plus
`CONSTRUCTION_STATE.md` return the exact next Rust/CUDA deed informed by the new theorem surface.

[established-bounded; formal-checked; process-audit] QLT6 made
`HolonicQuantumTransport.lean` the single default and `tools/lean_check.sh` target; that umbrella
imports the prior HNN/HML surface and all QLT owners. `bash tools/lean_check.sh` built 3,762 jobs
under the 180-second boundary. Document law, epistemic tags, named paths, and source shape passed;
the source-shape receiver reported 620 live files and zero violations. The exact Rust/CUDA map and
returned CONS3 deed are in
[`research/records/2026-08-31_FINITE_MANY_BODY_POLARIZED_CRYSTAL_AND_DIFFUSION_LEAN_FOUNDATION_RETURNED_TO_THE_ENGINE.md`](../../research/records/2026-08-31_FINITE_MANY_BODY_POLARIZED_CRYSTAL_AND_DIFFUSION_LEAN_FOUNDATION_RETURNED_TO_THE_ENGINE.md).

## Falsifiers

[counterexample] Any occupation implementation whose same-mode creation is nonzero after occupation
fails Pauli exclusion and QLT1.

[counterexample] Any optical implementation which sums intensity per path rather than amplitudes at
the surface junction erases interference and fails QLT3.

[counterexample] Any polarization implementation which stores only a scalar phase or intensity
cannot distinguish orthogonal analyzer returns and fails QLT3.

[counterexample] Any crystal implementation whose lattice is only a coordinate array, without
recurring local phase/constitutive transport and boundary response, does not establish the crystal
morphology claimed here.

[counterexample] Any simulation receipt which reports a digest, terminal scalar, GPU residency, or
experimental agreement without its model, receiver, error/reconstruction boundary, and assumptions
fails QLT5.

[counterexample] A finite lattice spectrum, path sum, or analog emulator cannot by itself establish
the continuum Yang--Mills mass gap, Navier--Stokes regularity, the Hodge conjecture, BSD, RH, or
`P != NP`; each remains governed by its official quantifiers and missing limit/bridge.
