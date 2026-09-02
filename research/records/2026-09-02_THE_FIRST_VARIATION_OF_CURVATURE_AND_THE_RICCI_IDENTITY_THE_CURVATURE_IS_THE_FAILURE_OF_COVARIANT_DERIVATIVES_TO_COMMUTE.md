# The first variation of curvature and the Ricci identity: the curvature is the failure of covariant derivatives to commute

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 3719 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, on the Y1 covariant-lift contract (2026-08-22 record). Assistant derivation for the proofs on the connection-curvature owner.
**Band:** ∂(εf) = ε∂f / BRACKET SCALING / COVARIANT EXTERIOR DERIVATIVE OF A PERTURBATION / F(A+B) = F(A) + D_A B + [B,B] / F(A+εB) = F(A) + ε D_A B + ε²[B,B] / RICCI IDENTITY D_iD_jX − D_jD_iX = [F_ij, X] / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `HolonicConnectionVariation.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`differential_smul`; `bracket_smul_left`, `bracket_smul_right`; `covariantVariation A B i j =
D_i B_j − D_j B_i`; `curvature_add`: `F(A+B)_ij = F(A)_ij + (D_A B)_ij + [B_i, B_j]` for
differentiable components; `covariantDerivative_smul`; `curvature_add_smul`:
`F(A + εB) = F(A) + ε (D_A B) + ε² [B, B]`; `ricci`: `D_i D_j X − D_j D_i X = [F_ij, X]` for a
`C²` section and a differentiable connection.

## Reading

[definition] The curvature is the commutator of the covariant derivatives and the first-order
response of the connection to a perturbation is the covariant exterior derivative. These are the
two identities the Yang--Mills heat flow spends: the flow direction `Σ_j D_j F_{ji}` is a
perturbation, so the curvature moves by its covariant exterior derivative, and commuting the
covariant derivatives to reach the covariant Laplacian pays exactly in commutators with `F`.
In the holonic reading the Ricci identity is the statement that the returned face defect is the
noncommutation of the two edge transports, the continuum twin of the discrete face return.

[established-bounded] Next on Y1: the Yang--Mills flow direction `G_i = Σ_j D_j F_{ji}` and the
curvature evolution `(D_A G)_ij` expanded by Bianchi and Ricci into the covariant Laplacian of
`F` plus `[F, F]` terms (the Weitzenböck form); then the energy identity once an invariant inner
product on `𝔤` is admitted.

## Evidence

- `lake build ElementaryHolonics.Millennium.HolonicConnectionVariation` green within the 180 s bound.
- Axiom audits: `curvature_add`, `curvature_add_smul`, `ricci` each depend on
  `[propext, Classical.choice, Quot.sound]`.
