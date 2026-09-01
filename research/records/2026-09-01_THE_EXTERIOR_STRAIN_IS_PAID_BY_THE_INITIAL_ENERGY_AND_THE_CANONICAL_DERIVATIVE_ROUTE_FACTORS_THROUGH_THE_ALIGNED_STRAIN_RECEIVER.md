# The exterior strain is paid by the initial energy, and the canonical derivative route factors through the aligned strain receiver

**Date:** 2026-09-01
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job counts below)
**Provenance:** Brandon, 2026-09-01: *"Go for that suggested 'next deed' then."* Assistant derivation for the proofs.
**Band:** BUDGET GENERALIZED TO INTEGRABLE / ENERGY EXTERIOR TERM CONSTANT / CANONICAL ROUTE FACTORED / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / NOT COMMITTED

---

## Present question

[definition] The preceding record left the periodic finish line hanging on one signed integral, an
aligned strain budget that was required to be continuous. Brandon asked for the Biot--Savart
split of that budget into an exterior face paid by energy and an interior face paid by direction
coherence. Sol's direction-coherence line already owns that split in Fourier form: the canonical
enstrophy coefficient of `NavierStokesVorticityCanonicalModulus` is
`13122π·√(2E(t)) + 729·Lip(ω(t))·M`, with `E` the periodic kinetic energy and `M` the summable
dyadic Hodge distance moment. This record composes it into the aligned strain receiver.

## Return

[proved-derived; formal-checked] `AlignedStrainBudget` now requires its budget only to be
measurable, continuous on the open tail, and interval-integrable up to the terminal face. The
weight is built from the budget clipped to the tail, whose primitive is globally continuous and
differentiable at interior times by the fundamental theorem of calculus. Every theorem of the
previous record is retained under the weaker hypothesis: `norm_vorticity_le`,
`intervalIntegrable_criticalVorticityRate`, `compatibleOpenPeriodicExtension`, and
`statementB_of_alignedStrainTerminalControl`.

[proved-derived; formal-checked] `alignedStrain_le_canonicalBudget`: at every interior event the
aligned strain differential is at most `canonicalBudget(t)·‖ω‖²`, where
`canonicalBudget t := 13122π·√(2E(0)) + 729·rate(t)·M` and `rate` is the canonical vorticity
derivative receiver. The passage is Sol's pointwise canonical enstrophy-density law read through
the torus projection, with the kinetic energy rebased to its initial value by the standing
unforced energy law `openPeriodicSolutionOn_periodicKineticEnergy_le_initial`. The exterior face
of the strain is therefore a constant on the entire lifespan; only the interior face enters the
integral.

[proved-derived; formal-checked] `AlignedStrainBudget.ofCanonicalDerivativeRate`: interval
integrability of the canonical derivative receiver on any tail `[s, T]` constructs an aligned
strain budget, hence `compatibleOpenPeriodicExtension_of_canonicalDerivativeRate_tail` returns
the compatible extension from tail integrability alone. The canonical route of
`NavierStokesOfficialAnalyticDischarges`, which asked for integrability on `[0, T]`, factors
through the signed aligned receiver and loses its initial-face obligation.

[established-bounded; measured] `lake build ElementaryHolonics.Millennium.NavierStokesAlignedStrainBudget`
returned success; the eight audited theorems, including `alignedStrain_le_canonicalBudget` and
`compatibleOpenPeriodicExtension_of_canonicalDerivativeRate_tail`, depend only on
`[propext, Classical.choice, Quot.sound]`.

## The obligation, stated once

[open] The periodic official alternative now rests on one signed integral on one terminal tail:

```text
∫ₛᵀ  sup_x ⟪S ω̂, ω̂⟫⁺(x,t) dt < ∞
```

the time integral of the supremum of the positive aligned strain differential. The exterior face
is paid. The interior face is bounded by the canonical vorticity derivative through direction
coherence, and that bound is where the terminal obligation sits. Integrated along a closed vortex
line, the aligned strain is the logarithmic time differential of the line's length, so the
obligation is that no vortex line element stretches at a non-integrable rate before `T`.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesAlignedStrainBudget.lean` (rewritten
budget section and canonical composition). No Rust, CUDA, canon, blueprint, or construction-state
file changed.

## What this does not establish

[open] No budget is constructed unconditionally. Nothing here claims Navier--Stokes regularity.
The construction state and roadmap are unchanged; the live frontier remains SCF2.
