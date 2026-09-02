# The modal Riccati inequality drives a tail mode only by the tail against the Stokes dissipation

**Date:** 2026-09-01
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-01: *"proceed"*, after *"Stop waiting for my permission on things that are obviously progress."* Assistant derivation for the proofs.
**Band:** MODAL ENERGY DIFFERENTIATED / CURL BOUND IN L1 / NONLINEAR SOURCE PAID BY SHELL-STEP COST / MODAL RICCATI PROVED / NO SUM OVER THE TAIL / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Present question

[definition] The shell-step cost bounded the advection coefficient of a tail mode by tail masses.
Sol's exact per-mode vorticity equation in diagonal Stokes form
(`openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes`) has the curl of that coefficient as its
nonlinear source. The Riccati closure begins by differentiating the modal energy and reading the
source through the cost.

## Return

[proved-derived; formal-checked] `NavierStokesModalRiccati.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]` on every theorem; no `sorry`).

`modalEnergy k τ = Σ_c ⟪ω̂_{k,c}(τ), ω̂_{k,c}(τ)⟫_ℝ = Σ_c |ω̂_{k,c}(τ)|²` on Sol's vorticity mode
curve. `complexVectorL1_sq_le_three_mul_modalEnergy`: `ℓ¹(ω̂_k)² ≤ 3 · E_k`.

`complexVectorL1_frequencyCurlMultiplier_le`: `ℓ¹(curl_k v) ≤ 3 · √λ_k · ℓ¹(v)`, with
`λ_k = (2π)² |k|²` the Stokes eigenvalue, from Sol's squared bound.

`complexVectorL1_vorticityNonlinearMode_le`: for `k` outside the cube of radius `2N`,
`ℓ¹(N_k) ≤ 9 · √λ_k · B_N`, where `B_N` is the shell-step cost
`(2N+1)³ · 3√(2E(0)) · tailJ(N) + velocityTail(N) · totalJ`.

`modalEnergy_riccati`: at every interior time `t` and every `k` outside the cube of radius `2N`,
the modal energy is differentiable at `t` with derivative `D` and

```text
D ≤ −2 ν λ_k E_k(t) + 2 · ℓ¹(ω̂_k(t)) · 9 √λ_k · B_N(t).
```

The proof differentiates the real inner product of each component along Sol's equation, reads the
real scalar through `Complex.real_smul`, and bounds the cross term by Cauchy--Schwarz and the
component-to-`ℓ¹` comparison.

[established-bounded; measured] `lake build ElementaryHolonics.Millennium.NavierStokesModalRiccati`
completes; the job count is recorded in the commit receipt.

## What it says

[interpretation] Dissipation acts on the modal energy at the Stokes eigenvalue; the drive is the
mode's own amplitude times the square root of the eigenvalue times the tail masses beyond `N`.
A tail mode is self-limiting relative to the tail: whenever
`√E_k > 9√3 · B_N / (ν √λ_k)` the modal energy decreases. The step cost enters exactly once, as
`B_N`, and its energy-paid factor is the coherent count `(2N+1)³`.

## What this does not establish

[open] No sum over the tail is taken; the tail masses `tailJ(N)`, `velocityTail(N)`, `totalJ` are
not differentiated; no Gronwall integration is performed; `TailRelevanceControl` remains
uninhabited. The summed inequality over a finite family of tail modes, followed by the passage to
the tail mass as a supremum, is the next owner.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesModalRiccati.lean` (new; registered). It
imports the shell-step cost owner and, through it, Sol's advection bridges, the open Fourier mild
identity, and the vorticity shell dissipation bridge.
