# The contact material is a sheaf Laplacian, the loss covector reads the relative phase on every branch, and a basin's delay on the ring is its Doppler face, in Lean

November 18, 23:55 UTC. The sixth formalization pass over boxes of #410,
the second half of [the fifth](2026-11-18_THE_MODULAR_GROUP_IS_A_HALF_TURN_AND_A_THIRD_OF_A_TURN_A_TERNARY_POPULATION_IS_READ_BY_ITS_ROOT_A_JOINT_STEP_STAYS_PASSIVE_AT_EVERY_CERTIFIED_DEPOSIT_AND_A_LOCK_IS_ITS_RUN_WORD_IN_LEAN.md)
(#1003): its workers were stopped by a restart of the host and relaunched. Three modules of `lean/HolonicsResearch`,
each elaborated at the package's toolchain with no `sorry`, no `axiom` and no `native_decide`. Nothing here touches
the engine, a state or a run.

Refs #410, #408, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Holon/SheafLaplacian` | A cellular sheaf on a finite graph, stalks of any widths as coordinate sets and restriction maps as matrices that read only their own end: the slip is the coboundary, `(δx)_e = F_(t◁e) x_(t e) − F_(s◁e) x_(s e)`, and `δx = 0` exactly on the global sections. With `J_e = P_e δ`, `Σ_e w_e J_eᵀ D J_e = δᵀ W δ` (`material_eq_laplacian`); it is positive semidefinite for `w ≥ 0` and `D ⪰ 0`, and for `w > 0` and `D` definite its kernel is the global sections (`material_ker_iff_globalSection`). An edge assignment glues exactly when its class in `coker δ` vanishes, and `dim ker δ − dim coker δ = Σ_v d_v − Σ_e d_e` (`glues_iff_class_zero`, `index_eq_stalks`). The repository's `contactForm` is this Laplacian (`contactForm_eq_laplacian`), and one transport per edge gives `Holon/Complex.blockIncidence` as the coboundary. On the triangle, holonomy one leaves a section and an obstruction, holonomy `−1` neither. | #410's box on the contact material (#408); the sheaf record of October 23, §1 | `contact.sheaf-laplacian`, `contact.sheaf-cohomology-index` (both new), `contact.material` |
| `HNN/LossPhase` | For `ψ_H = √p e^{iφ}` and `ψ_T = √q e^{iθ}`, every lift `ℓ_n = ½(log q − log p) + i(θ − φ + 2πn)` exponentiates to `R = ψ_T/ψ_H`, the principal logarithm is one of them, and `Objects/Ratio.logRatio` is `ℓ_0`. With both participants moving along one clock every lift has the one derivative `½(q̇/q − ṗ/p) + i(θ̇ − φ̇)` and `R⁻¹R′` equals it (`hasDerivAt_lift`, `logDeriv_ratio`): the winding branch is absent. A common turn leaves the ratio, every lift and the covector; a turn of the produced phase alone moves the phase face by `−α̇`. | #410's box on the phase part of the loss covector; CLAUDE.md's loss law | `ratio.two-sided-covector` (new), `ratio.full-covector` |
| `Transport/InformationSpectroscopy` | The pencil's clock gauge `det(s²C + sλD + λ²K) = λ^(2n) det((s/λ)²C + (s/λ)D + K)` over any field, and a lossless proportional mass `μC` as the clock `μ^(−1/2)`; the Cayley chart sends `s ↦ ks` to the boost `φ_a`, `a = (k − 1)/(k + 1)`; `1 − \|φ(a)\|² = (1 − \|a\|²)(1 − \|c\|²)/\|1 − c̄a\|²` and the invariance of `δ(a, b)`; the basin's group delay `(1 − \|a\|²)/\|z − a\|²` on the circle and, for real `a`, its Doppler form `√(1 − β²)/(1 − β cos ω)` with peak `k` and trough `1/k`; the ring sum `Σ_(ζ^N = 1) (1 − \|a\|²)/\|ζ − a\|² = N Re((1 + a^N)/(1 − a^N))`, proved by finite power sums of the roots; the reading's mass `1/h′ = 1/h + 1` and its share `h′` of the residual, with the record's witness `215/209 ↦ 215/424`. | #410's spectroscopy box; the record of October 24, §2 to §4 and §6 | `spectro.clock-gauge`, `spectro.basin-doppler`, `spectro.basin-shape`, `spectro.reading-mass` |

The boxes of #410 these answer, by their opening words: "The contact material is a sheaf Laplacian" (whole);
"The phase part of the loss covector" (whole, with `Objects/RatioPhase` of #948, which proved the covector in the
logit chart with the target held, beside this module's two-sided amplitude chart); of "Information spectroscopy"
everything but the first-order line shift.

## 2. What the pass corrected

1. **The phase covector box was largely answered on November 17.** `Objects/RatioPhase` (#948) proved
   `excessCovector_re`, `excessCovector_im` and `ratio_logDerivative_curve`; the box stood open because nothing
   named it. `HNN/LossPhase` adds what the logit chart does not show, both participants moving, and names both
   owners.
2. **`import Mathlib` changes a matrix product here.** In `Holon/SheafLaplacian` a product of a mask and the
   coboundary elaborated through the `CStarMatrix` multiplication once all of Mathlib was imported, and the
   rewrites failed; the module imports the narrow Mathlib files it uses.
3. **Two spectroscopy rows move to `formal-checked`** (`spectro.basin-doppler`, `spectro.reading-mass`), each with
   the one clause Lean does not check named in its scope (the witness at `a = (3 + 4i)/10`; the off-range share);
   `spectro.clock-gauge` and `spectro.basin-shape` keep their grades, their unproved clauses named.

## 3. What each statement stands on, and the constructions beside it

- **The sheaf.** The record's general claim, that with invertible restriction maps a global section exists exactly
  where the holonomy round each cycle fixes it, is shown on the triangle's two witnesses; its general form is the
  cycle's holonomy of `Holon/Complex.block_cell_curvature` acting on one stalk, `1 − hol` invertible on the
  cycle's space. The least-squares offset `‖δx − b‖²_W` and its residual as an `H¹` representative, and the
  tower's three returns as unique, plural and obstructed sections, stand beside `Foundation/ContinuingTower`.
- **The loss covector.** One channel; the receiver's weighted sum is `RatioPhase.hasDerivAt_excess_curve`. The
  covector is a reading of the loss, and the implemented descent on the phase is `RatioPhase.alignCost`.
- **Spectroscopy.** The first-order line shift needs the derivative of a simple root of `det P_ε`; the
  inner–outer factorization `H = H_min B` and the count of basins as a winding are the argument principle on the
  circle.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the three modules by name: `Build completed successfully (8751 jobs)`, exit 0, 12 s,
no declaration elaborated with `sorry`; projected under 10 minutes, deadline 20 minutes, peak resident set not read. Single-file checks of each module at the
package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib revision on a cloud host, read by exit status
(each `EXIT 0` with no output), for the reason the first pass's record gives (`agent-inferred`). The research
library's aggregator imports the three modules.

Two workers on disjoint owner paths wrote the modules; the lead re-checked each file from the tree, and every
`L:` owner added to the atlas was read against its module's declarations by `tools/link_check.py atlas`.
