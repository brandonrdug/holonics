# The Yang–Mills Hessian: the energy along any linear path is a quartic whose second coefficient is the linearized Weitzenböck form

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3725 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, exposing the object the mass-gap receiver reads. Assistant derivation for the proofs.
**Band:** FIRST VARIATION ∫ΣB(D_A B, F) / HESSIAN ∫Σ(B(D_A B, D_A B) + 2B([B,B], F)) / CUBIC AND QUARTIC COEFFICIENTS / ENERGY ALONG A + εB IS THE QUARTIC / FIRST DERIVATIVE EVERYWHERE / SECOND DERIVATIVE AT ZERO IS THE HESSIAN / C¹ SUFFICES / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HolonicYangMillsHessian.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`firstVariation P A B = ∫ Σ B((D_A B)_ij, F_ij)`; `hessian P A B = ∫ Σ (B((D_A B)_ij, (D_A B)_ij) +
2 B([B_i, B_j], F_ij))`; `cubicCoefficient`, `quarticCoefficient`; `yangMillsEnergy_add_smul`:

```text
YM(A + εB) = YM(A) + ε·first + ε²·(½ hess) + ε³·cubic + ε⁴·(½ quartic),
```

for `C¹` connections `A` and perturbations `B`; `hasDerivAt_yangMillsEnergy` (the derivative at
every `ε`); `deriv_deriv_yangMillsEnergy`: the second derivative at `0` is `hessian P A B`.

## Reading

[definition] The Hessian of the Yang--Mills energy at `A` is the quadratic form of the linearized
Weitzenböck operator: the squared covariant exterior derivative of the perturbation plus the
curvature's commutator coupling. Its spectrum at a critical connection is the linearized theory's
energy spectrum, and the mass-gap receiver asks whether that spectrum has a strictly positive
bottom above the vacuum. The formal object is now exact and polynomial; what is missing is the
Hilbert-space completion and the quantum receiver, which are the finish line's own ports.

[established-bounded] Next in the loop: NS frontier chain, BSD sign law, RH divisor conjugation;
on Y1, the Hessian at a flat connection reduces to `∫ Σ B(D B, D B)` (the curvature term
vanishes), the free Laplacian on the adjoint bundle.

## Evidence

- `lake build ElementaryHolonics.Millennium.HolonicYangMillsHessian` green within the 180 s bound.
- Axiom audits: `yangMillsEnergy_add_smul`, `deriv_deriv_yangMillsEnergy` each depend on
  `[propext, Classical.choice, Quot.sound]`.
