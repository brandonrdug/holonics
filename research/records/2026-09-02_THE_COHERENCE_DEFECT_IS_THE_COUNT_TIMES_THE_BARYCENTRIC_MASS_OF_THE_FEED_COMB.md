# The coherence defect is the count times the barycentric mass of the feed comb

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below: 4088 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, expressing the coherence defect through Brandon's barycentric/affine collapse of the Dirac comb. Assistant derivation for the proofs.
**Band:** COMB POWER = COUNT × BARYCENTRIC MASS / DEFECT ⟺ n(n−1−κ)‖m‖² ≤ (1+κ)·SPREAD / BAND FEEDS CONVERGE TO THE ADVECTION MODE ALONG THE CUBES / BARYCENTRIC CONDITION ON EVERY CUBE ⇒ COHERENCE DEFECT / BARYCENTRIC TAIL CONTROL ⇒ STATEMENT B / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Return

[proved-derived; formal-checked] `NavierStokesCombBarycenterDefect.lean` (registered; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`).

`norm_sum_sq_eq_card_sq_mul_mean_sq`: `‖Σ z‖² = n² ‖m‖²` on any finite comb.
`norm_sum_sq_le_iff_barycenter`: `‖Σ z‖² ≤ (1+κ) Σ ‖z‖² ⟺ n (n − 1 − κ) ‖m‖² ≤ (1+κ) Σ ‖z − m‖²`.
`summable_feedTerm`, `hasSum_feedTerm`, `tendsto_bandFeed` (the band feeds converge to the
advection mode along the cubes, through `tendsto_frequencyCube_atTop`).
`coherenceDefectAt_of_cubes`: the defect bound on every cube passes to the whole comb.
`coherenceDefectAt_of_barycenter`: the barycentric condition on every cube returns
`CoherenceDefectAt κ k`. `BarycentricTailControl`; `coherenceDefectTail_of_barycentric`;
`statementB_of_barycentric`; `officialProblem_of_barycentric`.

## Reading

[definition] The defect is a geometric quantity of the comb: with `n` teeth, barycenter `m`, and
spread `S = Σ ‖z − m‖²`, the comb power is `n · (n ‖m‖²)` and the diagonal is `S + n ‖m‖²`, so
`1 + κ = n · (n‖m‖² / (S + n‖m‖²))`: the count times the barycentric fraction of the diagonal.
A uniform defect `κ` demands `‖m‖²/S ≤ (1+κ)/(n(n−1−κ))`, i.e. the barycenter of the feed comb must
vanish against its spread like `1/n²` as the cube grows. This is Brandon's collapse into
barycentric and affine geometry: blow-up needs a comb whose teeth do not balance, a persistent
barycenter, an aligned strike; a balanced comb (teeth cancelling in the mean) cannot feed a tail.

[established-bounded] Statement B now rests on one geometric premise along a terminal tail
(`BarycentricTailControl`) plus interior finiteness. The next owner turns the barycenter of the
feed comb into a statement about the velocity field itself: the barycenter of
`p ↦ û(p)·(2πi(k−p))·û(k−p)` over the cube is the mean sender-carrier grip, and its vanishing is
the mean-zero condition of the transported strain along the receiver's direction.

## Evidence

- `lake build ElementaryHolonics.Millennium.NavierStokesCombBarycenterDefect` green within the 180 s bound.
- Axiom audits: `norm_sum_sq_le_iff_barycenter`, `coherenceDefectAt_of_barycenter`,
  `statementB_of_barycentric` each depend on `[propext, Classical.choice, Quot.sound]`.
