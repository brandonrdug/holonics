# The aligned strain differential budgets the critical vorticity and returns the periodic finish line

**Date:** 2026-09-01
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job counts below); `source-inspected` (Git stashes and the SCF release commit)
**Provenance:** Brandon, 2026-09-01: *"Are you being semantically aesthetic or do you mean 'strain rate' literally? ... I'd want you to immediately proceed into (3) after (1) and (2) ... So just go hard, act like you have what you need to solve and just keep going."* Assistant derivation for the proofs.
**Band:** STEPS ONE AND TWO CLOSED / ALIGNED STRAIN BUDGET PROVED INTO STATEMENT B / SIGNED RECEIVER REPLACES UNSIGNED MAGNITUDE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / NOT COMMITTED

---

## Present question

[definition] The preceding record left the Navier--Stokes periodic finish line one Prop away,
`CriticalVorticityTerminalControl`, an unsigned bound on the vorticity magnitude. Brandon asked
whether the "strain rate" of the proposed next rung is literal. It is: the strain differential is
the symmetric part of the velocity differential, and the theorem reads its quadratic form along
the vorticity's own frame. This record returns that rung.

## Return: the maximum principle from any initial face, with a source

[proved-derived; formal-checked] `NavierStokesTransportedScalarMaximumPrinciple.lean` now proves
`transportedSubsolution_le_of_le_at`: the parabolic maximum principle for a periodic scalar from
an arbitrary initial face `a ∈ Ico 0 T`, requiring only joint continuity on `univ ×ˢ Ico a T`,
`C²` spatial slices and time differentiability at times in `Ioo a T`, and the transport-diffusion
law as an inequality there. `transportedSubsolution_mul_weight_le_of_le_at` adds a multiplicative
source `2 A(t)` removed by a positive weight with `E a = 1` and `E' = -2 A E`. The earlier
equality and absolute-value theorems are corollaries. The owner builds through `lake` with eight
audited theorems, each on `[propext, Classical.choice, Quot.sound]`.

## Return: the aligned strain differential and its budget

[proved-derived; formal-checked] `NavierStokesAlignedStrainBudget.lean` proves, for every `C²`
vector field `w` on the periodic space, the exact identity
`Δ‖w‖² = 2⟪w, Δw⟫ + 2 Σᵢ ‖∂ᵢ w‖²` (`laplacian_norm_sq`) through the tree's affine-line
second-differential mechanism, hence `2⟪w, Δw⟫ ≤ Δ‖w‖²`.

[definition] `alignedStrain velocity x t := ⟪(∇u) ω, ω⟫` is the vortex-stretching term read along
the vorticity's own frame. By the standing `inner_matrixAction_curl_eq_symmetricPart` only the
symmetric strain contributes; compression and rotation along the frame cost nothing.

[proved-derived; formal-checked] `vorticitySquare_law`: on every open periodic solution with
`0 ≤ ν` and no force, the squared vorticity magnitude obeys
`∂ₜ q + (u·∇) q ≤ 2 · alignedStrain + ν Δ q` at every interior time. The time and transport
differentials come from the pointwise vorticity balance already proved on the closed interior
slab (`smoothSolutionOn_pointwiseVorticityBalance_inner` through `toClosedInterior`), the time
differential is the Eulerian jet by interior joint smoothness, and the Laplacian inequality above
supplies the viscous sign.

[definition] `AlignedStrainBudget solution` retains a start `s ∈ Ioo 0 T` and a continuous
`budget : ℝ → ℝ` with `alignedStrain x t ≤ budget t · ‖ω x t‖²` for every `x` and `t ∈ Ioo s T`.

[proved-derived; formal-checked] `AlignedStrainBudget.norm_vorticity_le`: on `Ico s T`,
`‖ω(x,t)‖ ≤ criticalVorticityRate(s) · exp ∫ₛᵗ budget`. The weight `exp(-2 ∫ₛ budget)` removes
the source and the weighted maximum principle from the face `s` returns the bound.

[proved-derived; formal-checked] `AlignedStrainBudget.intervalIntegrable_criticalVorticityRate`:
the critical vorticity receiver is interval-integrable on `[0, T]`, the initial face by the
standing unconditional `intervalIntegrable_criticalVorticityRate_initial` and the tail by the
continuous majorant above. `AlignedStrainBudget.compatibleOpenPeriodicExtension` then returns
the existing compatible extension through
`compatibleOpenPeriodicExtension_of_integrableCriticalVorticity`.

[proved-derived; formal-checked, conditional] `AlignedStrainTerminalControl`, the existence of a
budget on some tail for every positive-viscosity official solution, implies
`CriticalVorticityTerminalControl` (`criticalVorticityTerminalControl_of_alignedStrain`) and
therefore the literal periodic official alternative `StatementB`
(`statementB_of_alignedStrainTerminalControl`). The hypothesis is a signed, receiver-relative
quantity; the previous terminal Prop was unsigned.

[established-bounded; measured] `lake build ElementaryHolonics.Millennium.NavierStokesAlignedStrainBudget`
returned `Build completed successfully (3988 jobs)`; the six audited theorems depend only on
`[propext, Classical.choice, Quot.sound]`. Both owners are registered in `ElementaryHolonics.lean`.

## The release stash and its recovery

[historical; source-inspected] The SCF release commit `d49c55c1` (13:03) cleaned the working
tree and preserved this line's uncommitted work as `stash@{1}` "pre-existing non-SCF formal work
preserved before SCF release" and `stash@{0}` "additional non-SCF formal work preserved during SCF
release". The files were restored from the stashes into the working tree without dropping them,
the claim index was regenerated, and a cross-line notice was posted on the Provenance cursor. No
content was lost.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesTransportedScalarMaximumPrinciple.lean`
(extended) and `ElementaryHolonics/Millennium/NavierStokesAlignedStrainBudget.lean` (new). No
Rust, CUDA, canon, blueprint, or construction-state file changed.

## What this does not establish

[open] No aligned strain budget is constructed for any solution. Step three, the Biot--Savart
split of the aligned strain at the vorticity peak into an interior part depleted by direction
coherence and an exterior part bounded by energy, is the next deed; it requires the periodic
Biot--Savart kernel and its singular-integral bounds, which the tree does not yet own.

[open] The theorem bounds the tail from the value of the critical receiver at the start of the
tail; it does not bound the initial layer by the data, which the standing initial-face theorem
supplies only qualitatively.

[definition] Nothing here claims Navier--Stokes regularity. The construction state and roadmap are
unchanged; the live frontier remains SCF2.
