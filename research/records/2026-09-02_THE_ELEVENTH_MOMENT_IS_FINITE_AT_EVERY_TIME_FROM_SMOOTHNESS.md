# The eleventh moment is finite at every time, from smoothness alone

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: owner cone within the Navier–Stokes tree; root module green, 9741 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02, discharging the per-time summability clause of the coherence-defect tail control from the smoothness of the solution's slices, so that the official problem follows from the defect bound along a tail and the compact eleventh-moment bound alone. Assistant derivation for the proofs.
**Band:** sup^{11} ≤ |q|^{12} / eleventhMoment ≤ (2π)^{−12}·λ_q^7·velPop / EVERY STOKES-WEIGHTED VELOCITY POPULATION SUMMABLE FROM THE ALL-ORDERS SLICE OWNER / Summable(eleventhMoment σ) AT EVERY TIME / CoherenceDefectTailControl' (DEFECT + COMPACT BOUND) ⇒ CoherenceDefectTailControl ⇒ THE OFFICIAL PROBLEM / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `sup_pow_eleven_le`: `sup(q)^{11} ≤ |q|^{12}` (zero at `q = 0`, and
`sup ≤ sup²·… ≤ |q|²` otherwise). `eleventhMoment_le_stokes`:
`sup(q)^{11} ‖ω̂_q‖² ≤ (2π)²/(2π)^{14} · λ_q^7 · ‖û_q‖²` with `λ_q = (2π)²|q|²` the Stokes
eigenvalue, through `ω̂_q = 2πi q × û_q`. `summable_stokes_pow_mul_velPop`: every
`Σ_q λ_q^{order} ‖û_q‖²` converges, since each slice is smooth and periodic and the all-orders
owner gives its Fourier coefficients every finite Sobolev order.

[proved-derived] `summable_eleventhMoment` (**the eleventh moment is finite at every time**):
`Summable (eleventhMoment σ)` for every `σ ∈ (0, T)`, from smoothness alone.

[definition] `CoherenceDefectTailControl'`: along a terminal tail every nonzero receiver has
coherence defect at most `κ`, and the eleventh moment is bounded on every compact `[s, τ]`,
`τ < T`. No summability clause.

[proved-derived] `coherenceDefectTailControl_of_defect`, `officialProblem_of_defect`: the
primed control implies the corpus's tail control, hence **the official Navier–Stokes problem
follows from the defect bound along a tail together with the compact eleventh-moment bound**.

## Constants

[definition] `(2π)²/(2π)^{14} = (2π)^{−12}`: one curl factor over seven Stokes factors;
`7 = 6 + 1`, six from `sup^{11} ≤ |q|^{12}` and one from the curl. `11` is the corpus's moment
order. All inherited.

## Holonic reading

[definition] The hypotheses that were bookkeeping are being paid down: what remains on the NS
face is the coherence defect (the analogue of the pair population of `ξ`) and one uniformity in
time (the compact bound), which is continuity of the slice's Sobolev norm along the tail. The
defect is the physics; the compact bound is the next bounded owner.

[established-bounded] The compact eleventh-moment bound on `[s, τ]` with `τ < T` is
derivable from joint smoothness on the closed space-time slab, through Parseval for the
derivative jets and their continuity in time; it has not been returned yet.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesEleventhMomentFromSmoothness.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.NavierStokesVelocityMassEnergy`.
- Axiom audit for `summable_eleventhMoment`, `officialProblem_of_defect`:
  `[propext, Classical.choice, Quot.sound]`.
