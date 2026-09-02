# A bounded shell-step cost keeps every tail mode bounded by its own dissipation

**Date:** 2026-09-01
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-01: *"proceed"*. Assistant derivation for the proofs.
**Band:** ARITHMETIC-GEOMETRIC FORM PROVED / WEIGHTED EXCESS ANTITONE / TAIL MODE BOUNDED UNDER BOUNDED COST / EQUILIBRIUM DECAYS WITH THE EIGENVALUE / NO SUM OVER THE TAIL / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Present question

[definition] The modal Riccati inequality bounds the derivative of a tail mode's energy by Stokes
dissipation against the amplitude times the shell-step cost. This record integrates it on a
terminal tail under the hypothesis that the cost stays bounded there.

## Return

[proved-derived; formal-checked] `NavierStokesModalGronwall.lean` (registered; `lake build`
`4065` jobs; axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`).

`one_le_frequencySquared_of_not_mem`, `torusStokesEigenvalue_pos_of_not_mem`: a mode outside any
cube has a positive Stokes eigenvalue.

`amgm_step`: `18 x y ≤ (ν/3) x² + (243/ν) y²` for `ν > 0`.

`modalEnergy_riccati_amgm`: for `ν > 0`, every interior time, and every `k` outside the cube of
radius `2N`, the modal energy is differentiable with derivative `D` and

```text
D ≤ −ν λ_k E_k + (243/ν) · B_N².
```

`modalEnergy_le_of_feedBound_le`: if the shell-step cost at radius `N` is at most `M` on
`[s, T)`, then on `[s, T)` every mode outside the cube of radius `2N` satisfies

```text
E_k(τ) ≤ max ( E_k(s), 243 M² / (ν² λ_k) ).
```

The proof is the weighted maximum principle: the excess `(E_k − c) · e^{ν λ_k (τ − s)}` with
`c = 243 M²/(ν² λ_k)` has nonpositive derivative once `B_N ≤ M`, hence is antitone on `[s, τ]`
(`antitoneOn_of_deriv_nonpos`), and the two cases `E_k(s) ≤ c`, `E_k(s) > c` return the maximum.

## What it says

[interpretation] The equilibrium `243 M²/(ν² λ_k)` decays with the Stokes eigenvalue: a mode
farther out is held closer to zero by its own dissipation, against the same cost. The hypothesis
is the shell-step cost bounded on a terminal tail, which is a bounded form of
`TailRelevanceControl`. The sum over the tail of the equilibria carries `Σ_k λ_k⁻¹`, which does
not converge in three dimensions with a cost uniform in `k`; the half-radius instantiation of the
reach theorem, with the cost at radius `⌊(|k|_∞ − 1)/2⌋` for the mode `k`, supplies the decay in
`k` that a summed inequality needs. That instantiation is the next owner.

## What this does not establish

[open] No sum over the tail; no differentiation of the tail masses; the bounded-cost hypothesis is
not discharged. `TailRelevanceControl` remains uninhabited.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesModalGronwall.lean` (new; registered). It
imports the modal Riccati owner.
