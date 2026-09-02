# The official Navier–Stokes problem follows from the coherence-defect bound alone

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: owner cone within the Navier–Stokes tree; root module green, 9743 jobs)
**Provenance:** Assistant, under Brandon's direct-route directive of 2026-09-02, discharging the last bookkeeping clause of the coherence-defect tail control: the eleventh moment is bounded on every compact time interval, from joint smoothness on the open slab through the iterated derivative and Parseval for the coordinate word jets of order seven. Assistant derivation for the proofs.
**Band:** WORD JET = ITERATED DERIVATIVE ON BASIS VECTORS / SLICE DERIVATIVE = JOINT DERIVATIVE ∘ SPATIAL INCLUSION ON THE OPEN SLAB / BOUNDED ON unitCube × [s, τ] BY CONTINUITY / PARSEVAL: moment 11 ≤ (2π)^{−12}·3·3^7·M²·vol / CoherenceDefectOnly ⇒ CoherenceDefectTailControl' ⇒ THE OFFICIAL PROBLEM / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `NavierStokesWordJetIsIteratedDerivative`: `spatialCoordinateWordJet_eq_iteratedFDeriv`,
the coordinate word jet of a smooth field is its iterated Fréchet derivative evaluated on the
basis vectors of the word; `norm_spatialCoordinateWordJet_le`, hence bounded by the operator norm
of the iterated derivative.

[proved-derived] `NavierStokesEleventhMomentCompactBound`: `iteratedFDeriv_slice_eq`,
`norm_iteratedFDeriv_slice_le`: for `σ ∈ (0, T)` the slice's iterated derivative is the joint
iterated derivative on the open slab composed with the spatial inclusion (shift by `(0, σ)`,
then the inclusion `x ↦ (x, 0)`), and is bounded by it. `exists_bound_iteratedFDeriv`: the joint
iterated derivative is continuous on the open slab, so bounded on the compact
`unitCube × [s, τ]`. `moment_eleven_le_of_bound`: a bound `M` on the seventh slice derivative on
the cube gives `moment 11 σ ≤ (2π)^{−12} · 3 · 3^7 · M² · vol(unitCube)` through Parseval for
the `3^7` coordinate words of order seven. `exists_compact_bound` (**the eleventh moment is
bounded on every compact time interval**).

[definition] `CoherenceDefectOnly`: along a terminal tail every nonzero receiver has coherence
defect at most `κ`. Nothing else.

[proved-derived] `officialProblem_of_coherenceDefectOnly` (**the official Navier–Stokes problem
follows from the coherence-defect bound along a terminal tail**).

## Constants

[definition] `3 · 3^7 = 3 · 2187`: three components times the `3^7` coordinate words of order
seven; `(2π)^{−12}` inherited; `vol(unitCube)` is carried as `volume.real unitCube`.

## Holonic reading

[definition] The Navier–Stokes face is now one hypothesis: the coherence defect. Every other
clause of the closure was a consequence of the solution's own smoothness and has been returned
as such. The defect is the fluid's pair population: the advection mode exceeding the diagonal
of its feed comb by a bounded factor along a terminal tail. On the RH face the zero comb has
no such excess (the Kirchhoff cancellation of the phase-flow ledger); on the NS face it is the
open question, stated now with nothing else in the way.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesWordJetIsIteratedDerivative.lean`
  and `.../NavierStokesEleventhMomentCompactBound.lean` compile under `lake env lean` and
  `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.Millennium.NavierStokesEleventhMomentFromSmoothness`.
- Axiom audit for `officialProblem_of_coherenceDefectOnly`, `exists_compact_bound`,
  `spatialCoordinateWordJet_eq_iteratedFDeriv`: `[propext, Classical.choice, Quot.sound]`.
