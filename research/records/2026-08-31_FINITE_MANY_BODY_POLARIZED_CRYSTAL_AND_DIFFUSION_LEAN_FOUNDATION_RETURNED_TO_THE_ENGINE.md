# Finite many-body, polarized crystal, and diffusion Lean foundation returned to the engine

Date: 2026-08-31  
Status: terminal QLT conformance record; evidence only; schedules nothing outside
`blueprint/THE_ROADMAP.md`

## Requested qualitative return

[established-bounded; formal-checked] The Lean production line now has one import closure for:

- finite fermionic occupation, Koszul transport, vacuum/number grading, CAR, and the
  creation/annihilation adjoint relation;
- a finite Fermi--Hubbard Hamiltonian with Hermiticity and exact particle-number sectors;
- coherent complex paths from addressed source occurrences to surface receivers;
- dependent polarization transport, analyzer faces, crystal phase, diffraction, and intensity
  only after coherent joining;
- distinct unitary real time, imaginary time, stochastic sampling, physical boundary diffusion,
  and open-system carrier types; and
- exact/bounded finite simulation certificates with decomposed trust and error boundaries.

[proved-derived; formal-checked] The primary owners are:

```text
ElementaryHolonics/Computation/HolonicFermionicOccupation.lean
ElementaryHolonics/Computation/HolonicFermiHubbard.lean
ElementaryHolonics/Computation/HolonicPolarizedCrystalTransport.lean
ElementaryHolonics/Computation/HolonicEvolutionKinds.lean
ElementaryHolonics/Computation/HolonicSimulationCertificate.lean
ElementaryHolonics/Computation/HolonicQuantumTransport.lean
```

[proved-derived; formal-checked] `AngleExcess.lean` no longer owns an isolated implementation of
crystalline phase, diffraction amplitude, or intensity. Its public wrappers delegate to the common
polarized-crystal owner.

## Exact implementation conformance map

| Formal construction | Existing Rust/CUDA owner | Conformance boundary |
|---|---|---|
| addressed source/surface path fibre | `ResidentQuadraticMomentFront`, `ResidentCurrentAddress`, `ResidentCompletedTargetObservationAperture`, `membrane_moment_plan.rs` | [established-bounded; source-inspected] Source/current addresses and the completed target aperture exist. The UAR off-diagonal realization-site passage remains the narrower runtime obstruction recorded by the roadmap. |
| complex amplitude joins before a positive receiver | `ExactComplexWaveCurrent`, `conduct_quadratic_moment_front_inner`, `membrane_moment_plan.rs`, `membrane_boundary_return.rs` | [established-bounded; source-inspected] The split owners retain current limbs, active factors, generator/local targets, boundary state, moment/contraction work, and returned receiver testimony. UAR still owes the complete dependent target contraction on the strongest resident surface. |
| coherent path boundary and receiver reconstruction | `ResidentFactoredHistoryQuotientPassage`, `SourceNeutralObservableContinuation`, `athena_receiver_history`, `membrane_boundary_return.rs` | [established-bounded; source-inspected] These owners carry history/receiver/reconstruction testimony. Equal terminal values or digests remain insufficient. |
| polarized optical field | `soma/life/src/athena_native/membrane_optical.rs` | [counterexample; source-audit] `rg -n "polariz|Jones|birefring|Fock|CAR" soma/life/src/athena_native/membrane_optical.rs` on 2026-08-31 returns no dependent polarization/Jones or fermionic carrier. `NativeOpticalCell` carries one `ExactComplexWaveCurrent`; raster/color remains a later receiver. A later physical-optics runtime phase must add a typed polarization fibre and local path transport rather than reinterpret RGB or scalar phase. |
| fermionic occupation and CAR | no current Rust/CUDA simulation owner | [open; source-audit] `rg -n "Fock|canonical anticommutation|creation operator|annihilation operator" crates soma/life -g '*.rs'` on 2026-08-31 returns no runtime many-body carrier. QLT proves the formal owner and does not inject it into UAR. |
| finite Fermi--Hubbard Hamiltonian | no current Rust/CUDA simulation owner | [open] A later simulator deed must instantiate sparse occupation sectors and local bond terms on the resident apparatus. The Lean theorem surface, not a numerical fixture, is its contract. |
| deterministic physical diffusion | `crates/holonic-engine/src/diffusion.rs` and the standing boundary/current owners | [established-bounded; source-inspected] Exact rational capacity/Laplacian/Schur transport remains distinct from imaginary-time projection and configuration-space Monte Carlo. |
| real/imaginary quantum time | Physlib finite target and the QLT Lean adapter | [established-bounded; formal-checked] This is currently formal/checker apparatus. It is not an Eros/Athena runtime claim. |
| numerical certificate and TorchLean adapter | `HolonicSimulationCertificate.lean`; TorchLean remains exterior | [established-bounded; formal-checked] Lean checks the residual/error predicate. An external tensor graph, CUDA runtime, or producer does not become theorem-kernel evidence. |

## Engine consequence

[project-postulate] UAR is not turned into a fermion simulator, optical ray tracer, TorchLean
trainer, or quantum backend. Its immediate theorem consequence remains the stricter common law:
retain addressed paths and dependent complex current through the target junction; join linearly;
apply a receiver afterward; keep the reconstruction fibre.

[counterexample; source-inspected] The consolidated coordinator
`crates/holonic-engine/src/cuda_refine.rs` is 4,386 lines, but
`conduct_quadratic_moment_front_inner` still begins at line 1,603 and owns the remainder of the
coordinator's contraction/receiver/readback passage. `membrane_moment_plan.rs` (1,103 lines),
`membrane_moment_workspace.rs` (661), and `membrane_boundary_return.rs` (807) already expose the
owner seams. The remaining function is therefore still the exact CONS3 source-shape residual; QLT
does not erase or pass it.

[definition] After QLT closes, the roadmap returns to CONS3 at that function. Its deed is to leave
`conduct_quadratic_moment_front_inner` as a narrow coordinator over the existing admission/plan,
workspace/contraction, and boundary-return owners while preserving one context, one terminal
synchronization, exact direct/resident equality, and all UAR current/reconstruction testimony.

[definition] CONS4 then treats `HolonicQuantumTransport.lean` as the single live Lean umbrella.
The umbrella imports the prior HNN/HML production surface, so the formal line is extended rather
than forked. QLT's Fock, polarized-crystal, evolution, and certificate owners remain independent
theorem prerequisites until an engine campaign explicitly admits their runtime ports.

## Validation boundary

[established-bounded; formal-checked; process-audit] Focused `lake env lean` checks passed for all
five new owners and for the refactored `AngleExcess.lean`. On 2026-08-31,
`timeout 180s bash tools/lean_check.sh` built the unified
`ElementaryHolonics.Computation.HolonicQuantumTransport` closure in 3,762 jobs. The same bounded
validation sequence returned document law, epistemic tags, named paths, and source shape green;
source shape reported 620 live files, 447 inherited baselines, and zero violations.

[project-postulate] Simulation remains a receiver. A finite spectrum, residual, diffraction image,
Monte Carlo interval, TorchLean graph, or analog-emulator agreement does not promote a continuum or
Millennium claim. Each later bridge retains its regulator/limit, calibration, error, receiver, and
reconstruction fibre.
