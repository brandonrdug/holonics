# The Fourier Kirchhoff law: the transfer currents sum to zero

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4089 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, formalizing Brandon's Kirchhoff/current-law and join-theorem reading of the Clay problem in Fourier form. Assistant derivation for the proofs on the line's Parseval, torus-chart, and advection-work owners.
**Band:** TWO-FIELD PARSEVAL ON THE SLICE / TORUS PAIRING = CUBE INTEGRAL OF THE PRODUCT / TRANSFER CURRENT Re⟨adv_k, û_k⟩ / Σ' TRANSFER = 0 / BAND–TAIL BUDGET / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesFourierKirchhoff.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`hasSum_re_conj_mul_smoothSliceFourierL2`: the real Parseval pairing of two smooth periodic
components, `Σ'_k Re(conj û_c(k) · v̂_c(k)) = ∫_torus Re(conj U · V)` (Mathlib's
`hasSum_prod_mFourierCoeff` on the `L²` lifts). `integral_re_conj_mul_lift_eq`: the torus pairing is
the cube integral `∫_cube u_c v_c`. `transfer k = Σ_c Re(conj adv_k(c) · û_k(c))`;
`hasSum_transfer_component`; `hasSum_transfer : HasSum transfer 0` (the periodic advection work
`∫ ⟨(u·∇)u, u⟩ = 0` under incompressibility); `summable_transfer`; `tsum_transfer`;
`sum_transfer_add_tsum_compl`; `tsum_compl_transfer_eq_neg`:

```text
Σ'_{k ∉ F} transfer k = − Σ_{k ∈ F} transfer k.
```

## Reading

[definition] This is Brandon's reading of the divergence constraint as a current law, lifted to the
lattice: the nonlinear transfer is a current on the receivers, and its total is zero. The tail can
only be fed by what the band gives up. Together with `tail_fed_only_through_tail` (a receiver
outside the double cube is not fed by two band senders) and the coherence-defect closure, the
picture is: transfer into the tail is a band-to-tail current through the frontier of the cube,
bounded by band quantities, and it must be coherent to grow the tail.

[established-bounded] Next: the tail energy budget `d/dt E_tail(N) = −ν D_tail(N) + Π(N)` with
`Π(N) = Σ'_{k∉cube N} transfer k = −Σ_{k∈cube N} transfer k`, and the bound of `Π(N)` by band
quantities; then RH Weil positivity.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesFourierKirchhoff` green within the 180 s bound.
- Axiom audits: `hasSum_re_conj_mul_smoothSliceFourierL2`, `hasSum_transfer`,
  `tsum_compl_transfer_eq_neg` each depend on `[propext, Classical.choice, Quot.sound]`.
