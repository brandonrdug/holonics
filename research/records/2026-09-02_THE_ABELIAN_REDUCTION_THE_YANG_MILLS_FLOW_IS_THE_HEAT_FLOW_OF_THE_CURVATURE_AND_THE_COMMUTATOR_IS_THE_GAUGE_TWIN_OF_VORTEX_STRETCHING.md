# The abelian reduction: the Yang–Mills flow is the heat flow of the curvature, and the commutator is the gauge twin of vortex stretching

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3726 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, returning the Navier--Stokes/Yang--Mills pairing Brandon asked for on the Clay reading. Assistant derivation for the proofs.
**Band:** COMMUTATIVE ALGEBRA ⇒ BRACKET = 0 / D = ∂ / F = dA / WEITZENBÖCK = HEAT EQUATION Σ_k ∂_k∂_k F / HESSIAN = FREE FORM ∫ΣB(dB,dB) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HolonicYangMillsAbelian.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

Under `hcomm : ∀ x y, x * y = y * x`: `bracket_eq_zero`; `covariantDerivative_eq_differential`;
`curvature_eq_differential` (`F = dA`); `covariantVariation_yangMillsDirection_eq_laplacian`:
`(D_A G)_ij = Σ_k ∂_k ∂_k F_ij` for a `C³` connection; `hessian_eq_free`:
`hess = ∫ Σ B(dB_ij, dB_ij)`.

## Reading

[definition] The pairing with the fluid is now exact on the abelian side: the velocity is an
abelian connection, its curvature is the vorticity two-form `∂_i u_j − ∂_j u_i`, and the
Yang--Mills flow of the curvature is the Stokes heat flow of the vorticity. What the abelian case
discards, `2 Σ_k [F_ik, F_kj]`, is exactly the term the fluid recovers from the advection: the
vortex stretching, which in the fluid is the coherent product of the strain with the vorticity and
in the gauge field is the commutator of adjacent faces. The two Millennium problems share one
identity with one term switched on or off: nonabelian self-interaction on one side, advective
self-interaction on the other. The coherence-defect closure of the fluid line and the Hessian
positivity of the gauge line are the two readings of that term.

[established-bounded] Next in the loop: NS frontier chain, BSD sign law, RH divisor
conjugation, continuum gauge covariance of the curvature.

## Evidence

- `lake build ElementaryHolonics.Millennium.HolonicYangMillsAbelian` green within the 180 s bound.
- Axiom audits: `covariantVariation_yangMillsDirection_eq_laplacian`, `hessian_eq_free` each depend on
  `[propext, Classical.choice, Quot.sound]`.
