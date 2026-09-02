# The finite-dimensional Hodge decomposition: every closed element has one balanced representative

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 2392 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, supplying the linear-algebraic spine of the Hodge decomposition in Brandon's balance vocabulary. Assistant derivation on Mathlib's adjoint and orthogonal-complement API.
**Band:** DIFFERENTIAL d² = 0 / CODIFFERENTIAL δ = d† / LAPLACIAN Δ = dδ + δd / HARMONIC = CLOSED ∩ COCLOSED / E = range d ⊕ range δ ⊕ ker Δ / CLOSED = HARMONIC + EXACT / HARMONIC ∩ EXACT = 0 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HodgeFiniteDecomposition.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`Differential E` (`d` with `d ∘ d = 0`); `delta = d†`; `laplacian = dδ + δd`; `harmonic = ker Δ`;
`d_sq_apply`, `delta_sq_apply`, `inner_d_left`, `inner_delta_left`; `mem_harmonic_iff`
(`Δx = 0 ↔ dx = 0 ∧ δx = 0`, by `⟪Δx, x⟫ = ‖δx‖² + ‖dx‖²`); the three orthogonality lemmas;
`harmonic_eq_orthogonal` (`ker Δ = (range d ⊔ range δ)ᗮ`); `sup_eq_top`
(`E = range d ⊔ range δ ⊔ ker Δ`); `exists_harmonic_add_exact` (every closed `x` is `h + d a` with
`h` harmonic); `harmonic_inf_range_d_eq_bot` (the harmonic representative is unique).

## Reading

[definition] In Brandon's vocabulary the Laplacian is the receiver of balance: `Δx = 0` says the
element is closed and coclosed at once, and the theorem says every class of closed elements is
supported by exactly one balanced element. This is the finite exact form of "receiver-visible
balance has something supporting it" on the linear side; the Hodge conjecture is the claim that on
the algebraic side the balanced `(p,p)` classes are supported by cycles, which this owner does not
touch. The same decomposition is the one the discrete Hodge star and the Poynting balance of the
2026-08-27 record live in.

[established-bounded] Next in the loop: NS frontier chain, BSD sign law, then the discrete Hodge
star on the cell complexes of the Hodge line as an instance of `Differential`.

## Evidence

- `lake build ElementaryHolonics.Millennium.HodgeFiniteDecomposition` green within the 180 s bound.
- Axiom audits: `Differential.mem_harmonic_iff`, `Differential.sup_eq_top`,
  `Differential.exists_harmonic_add_exact`, `Differential.harmonic_inf_range_d_eq_bot` each depend on
  `[propext, Classical.choice, Quot.sound]`.
