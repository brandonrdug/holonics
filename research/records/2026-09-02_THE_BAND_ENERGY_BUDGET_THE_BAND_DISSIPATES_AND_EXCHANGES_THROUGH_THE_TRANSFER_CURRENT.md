# The band energy budget: the band dissipates and exchanges through the transfer current

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4090 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, joining the Fourier Kirchhoff law to the exact velocity-mode evolution. Assistant derivation for the proofs.
**Band:** MODAL MASS IDENTITY / PRESSURE GRADIENT DOES NO MODAL WORK ON A DIVERGENCE-FREE MODE / BAND MASS AND BAND DISSIPATION / BAND BUDGET d/dt E_F = −2νD_F − 2Σ_F transfer = −2νD_F + 2Σ'_{k∉F} transfer / ALL IDENTITIES / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesBandEnergyBudget.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`re_mul_conj_comm`; `re_sum_gradient_pairing` (`Σ_c Re((2πi k_c) P conj v_c) = 0` when
`k · v = 0`); `modeMass k τ = Σ_c ‖û_k(τ)(c)‖²`; `modeMass_eq_velPop`;
`sum_inner_pressureGradientMode_eq_zero` (the pressure gradient does no modal work);
`hasDerivAt_modeMass`: `d/dt ‖û_k‖² = −2 ν λ_k ‖û_k‖² − 2 · transfer k` exactly, from the
unforced momentum mode `M_k = ν(−λ_k û_k) − adv_k − ∇p̂_k`; `bandMass`, `bandDissipation`;
`hasDerivAt_bandMass`; `hasDerivAt_bandMass_kirchhoff`:

```text
d/dt E_F = −2 ν D_F + 2 Σ'_{k ∉ F} transfer k.
```

## Reading

[definition] This is the join theorem in Fourier form: the divergence constraint kills the
pressure at every receiver (the pressure is a pure gauge on the lattice), the viscosity is a
diagonal drain, and the only exchange is the transfer current, which by the Kirchhoff law is
conserved. A band can lose mass only to dissipation and to the current into its complement; the
tail can gain only what the band's current gives it. The tail budget is the same identity with
`F` the complement: the tail grows only through a coherent current across the frontier.

[established-bounded] The NS line now carries: (i) the exact modal and band identities, (ii) the
conserved transfer current, (iii) the conditional closure of Statement B on a uniform coherence
defect with the energy premise discharged, and (iv) the barycentric form of the defect. The
remaining Millennium content is unconditional control of the defect. Next in the loop: RH Weil
positivity on the existing finish line.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesBandEnergyBudget` green within the 180 s bound.
- Axiom audits: `sum_inner_pressureGradientMode_eq_zero`, `hasDerivAt_modeMass`,
  `hasDerivAt_bandMass_kirchhoff` each depend on `[propext, Classical.choice, Quot.sound]`.
